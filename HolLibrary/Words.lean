/- ========================================================================= -/
/-          Theory of machine words using finite indexing types.             -/
/-                                                                           -/
/- Introduces a type `:N word` of N-bit words (N being a type of size N).    -/
/- Note that this builds in a priori the assumption the wordsize is nonzero. -/
/- Some abbreviations like `:byte` = `8 word` are often used for brevity.    -/
/-                                                                           -/
/- Mappings `val:N word->num` and `word:num->N word` for unsigned values,    -/
/- and similar 2s-complement `ival:N word->int` and `iword:int->word`, cast  -/
/- (reducing modulo wordsize in one direction) between words and numbers.    -/
/- The `bit` function gives a specific bit as a Boolean.                     -/
/-                                                                           -/
/- The usual operations are provided like `word_add`, `word_xor`; currently  -/
/- for explicitness we don't overload the usual operators. Some have signed  -/
/- and unsigned variants (e.g. `word_ushr` is unsigned/logical shift right,  -/
/- while `word_ishr` is signed/arithmetical shift right).                    -/
/-                                                                           -/
/- For some cases where the result is debatable or machine-dependent, we     -/
/- have versions that match the JVM tagged with a "j" (e.g. `word_jshr`      -/
/- truncates shift counts modulo word size).                                 -/
/-                                                                           -/
/- There are conversions like WORD_REDUCE_CONV for reducing via proof        -/
/- expressions built up from concrete words like `word 255:byte`.            -/
/-                                                                           -/
/- Some simple decision procedures for proving basic word lemmas are here    -/
/- too, and have limited and somewhat complementary scopes:                  -/
/-                                                                           -/
/-  - WORD_RULE for simple algebraic properties                              -/
/-  - WORD_BITWISE_RULE for bitwise-type properties of logical operations    -/
/-  - WORD_ARITH for things involving numerical values                       -/
/-  - WORD_BLAST for fixed-size bitwise expansions followed by arithmetic    -/
/-  - BITBLAST_RULE is a BDD-based "flattening" or "bit-blasting" rule       -/
/-                                                                           -/
/-              (c) Copyright, John Harrison 2019-2024                       -/
/-                (c) Copyright, Mario Carneiro 2020                         -/
/-                (c) Copyright, June Lee 2022-2024                          -/
/- ========================================================================= -/
/- File: HolLibrary/Words.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/words.ml`, by hand, in file order,
  in the style of HolLibrary/Prime.lean (see there and HolMath/Base.lean
  for the conventions).  Each section of words.ml is a theorem bundle (a
  `structure`) proved by a `setup` function; SessionLibrary/Words.lean
  builds the bundles in order and exports every name.  `needs
  "Library/bdd.ml"` (words.ml 39) is done by the wiring first.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print
  (MESON, SET_RULE, NUMBER_RULE, INTEGER_RULE) they are bound first, in
  OCaml's order.

  STATE.  words.ml's refs (`word_sizes`, `word_pow2sizes`, `word_SIZE_CONV`,
  `word_POW2SIZE_CONV`, words.ml 65-69) live in SessionLibrary and come in
  through `WordsDeps`; conversions read them when applied, as OCaml's `!r`.
-/

import HolMath
import HolLibrary.BDD

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolLibrary.Words

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

/- ------------------------------------------------------------------------- -/
/- What words.ml uses from the core library (supplied by Session).           -/
/- (Four structures, each under 128 fields: Lean 4.33.1 crashed on a        -/
/- constructor with 128 or more, which could not be reproduced on 4.34.1.    -/
/- The runtime limit is 255 fields, so at least two would still be needed.  -/
/- ------------------------------------------------------------------------- -/

/-- Theorems words.ml uses from the core library, A-E. -/
structure CoreThms1 where
  (ADD ADD1 ADD_AC ADD_ASSOC ADD_CLAUSES ADD_EQ_0 ADD_SUB ADD_SUB2 ADD_SYM
   AND_CLAUSES AND_FORALL_THM ARITH ARITH_EQ ARITH_ODD ARITH_SUC ARITH_ZERO
   BINARY_INDUCT BIT0 BIT1 CARD_CLAUSES CARD_EQ_0 CARD_IMAGE_INJ
   CARD_IMAGE_LE CARD_NUMSEG_LT CARD_SING CARD_SUBSET CARD_UNION
   CARD_UNION_EQ CARD_UNION_GEN CARD_UNION_LE CART_EQ COND_CLAUSES COND_ID
   COND_RAND COND_SWAP CONG CONG_DIV2 CONG_LMOD CONG_NSUM CONG_RMOD
   CONJ_ASSOC CONJ_SYM CONTRAPOS_THM DE_MORGAN_THM DIMINDEX_1 DIMINDEX_2
   DIMINDEX_3 DIMINDEX_4 DIMINDEX_FINITE_SUM DIMINDEX_GE_1 DIMINDEX_NONZERO
   DIMINDEX_TYBIT0 DIMINDEX_UNIQUE DISJOINT_EMPTY DISJOINT_SYM DISJ_SYM
   DIVIDES_DIV_MULT DIVIDES_LE DIVIDES_MOD DIVISION DIVISION_SIMP
   DIVMOD_UNIQ DIV_0 DIV_1 DIV_ADD_EQ DIV_DIV DIV_EQ_0 DIV_EXP DIV_LE DIV_LT
   DIV_MOD DIV_MULT DIV_MULT2 DIV_MULT_ADD DIV_UNIQ DIV_ZERO EMPTY_GSPEC
   EQ_ADD_LCANCEL EQ_ADD_RCANCEL EQ_IMP EQ_SYM_EQ EQ_TRANS EVEN EVEN_ADD
   EVEN_EXISTS EVEN_EXP EVEN_MOD EVEN_MULT EXISTS_BOOL_THM EXISTS_OR_THM EXP
   EXP_1 EXP_2_NE_0 EXP_ADD EXP_EQ_0 EXP_EXP EXP_LT_0 EXP_MULT EXP_ONE
   EXP_ZERO EXTENSION : thm)

/-- Theorems words.ml uses from the core library, F-I. -/
structure CoreThms2 where
  (FINITE_EMPTY FINITE_IMAGE FINITE_INSERT FINITE_NUMSEG FINITE_NUMSEG_LT
   FINITE_RESTRICT FINITE_SING FINITE_SUBSET FINITE_UNION FORALL_AND_THM
   FORALL_BOOL_THM FORALL_IN_GSPEC FORALL_IN_IMAGE FUN_EQ_THM GE GT HAS_SIZE
   IMP_CONJ IMP_CONJ_ALT INSERT_UNION_EQ INTER_COMM INTER_SUBSET INT_ABS_MUL
   INT_ABS_NUM INT_ABS_POS INT_ABS_POW INT_ADD_RID INT_CONG_DIV2
   INT_CONG_IMP_EQ INT_DIVISION INT_DIV_1 INT_DIV_DIV INT_DIV_EQ_0
   INT_DIV_LT_EQ INT_DIV_MUL INT_DIV_MUL_ADD INT_DIV_REM INT_DIV_ZERO
   INT_EQ_MUL_LCANCEL INT_EQ_SUB_RADD INT_FORALL_POS INT_GE INT_GT
   INT_LE_DIV_EQ INT_LE_LMUL_EQ INT_LE_MUL2 INT_LE_POW2 INT_LE_REFL
   INT_LE_RMUL INT_LE_TRANS INT_LT_IMP_LE INT_LT_IMP_NE INT_LT_LMUL_EQ
   INT_LT_POW2 INT_MAX INT_MIN INT_MUL_ASSOC INT_MUL_RID INT_MUL_RNEG
   INT_MUL_RZERO INT_MUL_SYM INT_NEG_LT0 INT_NOT_LE INT_NOT_LT
   INT_OF_NUM_ADD INT_OF_NUM_CLAUSES INT_OF_NUM_DIV INT_OF_NUM_EQ
   INT_OF_NUM_LE INT_OF_NUM_LT INT_OF_NUM_MUL INT_OF_NUM_OF_INT
   INT_OF_NUM_POW INT_OF_NUM_REM INT_OF_NUM_SUB INT_POS INT_POW INT_POW_ADD
   INT_POW_EQ_0 INT_POW_LE INT_POW_MONO INT_REM_EQ INT_REM_EQ_0
   INT_REM_MOD_SELF INT_REM_REM INT_REM_REM_POW_MIN INT_REM_UNIQUE INT_SUB_0
   INT_SUB_LZERO IN_ELIM_PAIR_THM IN_ELIM_THM IN_IMAGE IN_INSERT IN_INTER
   IN_NUMSEG IN_SING IN_UNION IN_UNIV : thm)

/-- Theorems words.ml uses from the core library, J-Q. -/
structure CoreThms3 where
  (LAMBDA_BETA LDIV_LT_EQ LE LEFT_ADD_DISTRIB LEFT_IMP_EXISTS_THM
   LEFT_SUB_DISTRIB LET_ADD2 LET_TRANS LE_0 LE_1 LE_ADD LE_ADD2
   LE_ADD_LCANCEL LE_ANTISYM LE_CASES LE_EXISTS LE_EXP LE_LT LE_MINIMAL
   LE_MULT_LCANCEL LE_MULT_RCANCEL LE_REFL LE_SUC_LT LE_TRANS LT LTE_TRANS
   LT_ADD2 LT_ADD_LCANCEL LT_EXISTS LT_EXP LT_IMP_LE LT_LE LT_MULT2
   LT_MULT_LCANCEL LT_POW2_REFL LT_REFL LT_TRANS MAX MIN MINIMAL MINIMAL_LE
   MINIMAL_UBOUND MINIMAL_UNIQUE MOD_0 MOD_1 MOD_2_CASES MOD_ADD_CASES
   MOD_ADD_MOD MOD_CASES MOD_EQ_0 MOD_EQ_SELF MOD_LE MOD_LT MOD_LT_EQ
   MOD_LT_EQ_LT MOD_MOD MOD_MOD_EXP_MIN MOD_MOD_REFL MOD_MULT MOD_MULT2
   MOD_MULT_ADD MOD_MULT_MOD MOD_NSUM_MOD_NUMSEG MOD_REFL MOD_UNIQ MOD_ZERO
   MONO_EXISTS MONO_FORALL MULT_2 MULT_AC MULT_ASSOC MULT_CLAUSES MULT_EQ_0
   MULT_SYM NOT_EVEN NOT_FORALL_THM NOT_IMP NOT_IN_EMPTY NOT_LE NOT_LT
   NOT_ODD NOT_SUC NSUM_ADD NSUM_ADD_NUMSEG NSUM_CLAUSES NSUM_CLAUSES_LEFT
   NSUM_CLAUSES_NUMSEG NSUM_CLAUSES_NUMSEG_LT NSUM_CLOSED NSUM_CONST
   NSUM_DELTA NSUM_EQ NSUM_EQ_0_IFF NSUM_EQ_GENERAL_INVERSES NSUM_GROUP
   NSUM_IMAGE NSUM_LE NSUM_LMUL NSUM_NSUM_PRODUCT NSUM_OFFSET NSUM_REFLECT
   NSUM_RESTRICT_SET NSUM_RMUL NSUM_SING NSUM_SUPERSET NSUM_UNION
   NSUM_UNION_EQ NUMERAL NUMSEG_CLAUSES_LT NUMSEG_LT NUMSEG_LT_DIMINDEX
   NUM_OF_INT_OF_NUM ODD ODD_ADD ODD_EXP ODD_MOD ODD_MOD_EVEN ODD_MULT
   ODD_SUB OR_CLAUSES PAIR_EQ : thm)

/-- Theorems words.ml uses from the core library, R-Z and lower case. -/
structure CoreThms4 where
  (RDIV_LT_EQ REAL_OF_INT_CLAUSES REAL_OF_NUM_ADD REAL_OF_NUM_CLAUSES
   REAL_OF_NUM_EQ REAL_OF_NUM_LE REAL_OF_NUM_POW REAL_OF_NUM_SUB
   REAL_OF_NUM_SUM REAL_OF_NUM_SUM_NUMSEG REAL_SUB_0 REAL_SUB_LE
   REAL_SUB_RZERO RIGHT_ADD_DISTRIB RIGHT_OR_DISTRIB SING_GSPEC SUBSET
   SUBSET_INTER_ABSORPTION SUB_0 SUB_ADD SUB_EQ_0 SUB_REFL SUC_INJ SUC_SUB1
   SUM_ADD SUM_ADD_NUMSEG SUM_DIFFS_ALT SUM_EQ_0_NUMSEG SUM_LMUL SUM_NEG
   SUM_RMUL SUM_SUB SUM_SUB_NUMSEG UNION_EMPTY UNWIND_THM2 bool_INDUCT
   divides int_divides int_of_num num_CASES num_INDUCTION num_congruent
   num_divides numseg o_DEF : thm)

/-- The definitional principles, state, decision procedures, conversions and
    syntax functions words.ml uses.  Rules that can fail are in `ExceptT`. -/
structure WordsDeps where
  -- definitions and type abbreviations
  new_definition : String → ExceptT String IO thm
  new_type_definition : String → String × String → thm → ExceptT String IO thm
  new_type_abbrev : String → hol_type → IO Unit
  define : String → ExceptT String IO thm
  -- words.ml's refs (65-69)
  word_sizes : IO.Ref (List thm)
  word_pow2sizes : IO.Ref (List thm)
  word_SIZE_CONV : IO.Ref ioconv
  word_POW2SIZE_CONV : IO.Ref ioconv
  -- decision procedures and other Session rules and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  ASM_INT_ARITH_TAC : tactic
  ASM_MESON_TAC : List thm → tactic
  HAS_SIZE_DIMINDEX_RULE : hol_type → ExceptT String IO thm
  INDUCT_TAC : tactic
  INTEGER_RULE : term → ExceptT String IO thm
  INT_ARITH : term → ExceptT String IO thm
  INT_ARITH_TAC : tactic
  INT_RING : term → ExceptT String IO thm
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  NUMBER_RULE : term → ExceptT String IO thm
  REAL_ARITH : term → ExceptT String IO thm
  REAL_ARITH_TAC : tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  mk_small_numeral : Int → Except String term
  /-- int.ml's `mk_intconst`. -/
  mk_intconst : Rat → Except String term
  -- conversions
  BITS_ELIM_CONV : ioconv
  DIMINDEX_CONV : ioconv
  EXPAND_CASES_CONV : ioconv
  EXPAND_NSUM_CONV : ioconv
  INT_ABS_CONV : ioconv
  INT_DIV_CONV : ioconv
  INT_GE_CONV : ioconv
  INT_GT_CONV : ioconv
  INT_LE_CONV : ioconv
  INT_LT_CONV : ioconv
  INT_MUL_CONV : ioconv
  INT_POLY_CONV : ioconv
  INT_POW_CONV : ioconv
  INT_REDUCE_CONV : ioconv
  INT_RED_CONV : ioconv
  INT_REM_CONV : ioconv
  INT_REM_DOWN_CONV : ioconv
  INT_SGN_CONV : ioconv
  INT_SUB_CONV : ioconv
  MOD_DOWN_CONV : ioconv
  NUM_ADD_CONV : ioconv
  NUM_DIV_CONV : ioconv
  NUM_EQ_CONV : ioconv
  NUM_EVEN_CONV : ioconv
  NUM_EXP_CONV : ioconv
  NUM_GE_CONV : ioconv
  NUM_GT_CONV : ioconv
  NUM_LE_CONV : ioconv
  NUM_LT_CONV : ioconv
  NUM_MAX_CONV : ioconv
  NUM_MIN_CONV : ioconv
  NUM_MOD_CONV : ioconv
  NUM_MULT_CONV : ioconv
  NUM_ODD_CONV : ioconv
  NUM_REDUCE_CONV : ioconv
  NUM_RED_CONV : ioconv
  NUM_SUB_CONV : ioconv
  NUM_SUC_CONV : ioconv
  /-- calc_num.ml's `num_CONV`: `|- NUMERAL n = SUC (NUMERAL (n-1))`. -/
  num_CONV : ioconv
  /-- define.ml's `prove_general_recursive_function_exists`. -/
  prove_general_recursive_function_exists : ioconv
  /-- `Compute.bool_compset ()`. -/
  bool_compset : IO (Except String HolMath.Compute.compset)
  /-- `Compute.set_skip`. -/
  set_skip : HolMath.Compute.compset → term → Option Int → IO (Except String Unit)
  /-- `Compute.add_conv (cst, arity, conv)`. -/
  add_conv : term → Int → ioconv → HolMath.Compute.compset → IO (Except String Unit)
  /-- `Compute.WEAK_CBV_CONV`. -/
  WEAK_CBV_CONV : HolMath.Compute.compset → ioconv
  /-- pair.ml's `let_CONV`. -/
  let_CONV : ioconv
  /-- bdd.ml's `BDD_DEFTAUT ivars`. -/
  BDD_DEFTAUT : List term → ioconv
  REAL_POLY_CONV : ioconv
  -- theorems
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3
  core4 : CoreThms4

/- ------------------------------------------------------------------------- -/
/- Some common word sizes.                                                   -/
/- ------------------------------------------------------------------------- -/

/-- The recursive `conv` of `add_word_sizes` (words.ml 74-76). -/
partial def wordSizeConv [HolBase] (sumconv NUM_ADD_CONV DIMINDEX_CONV : ioconv) : ioconv :=
  fun tm =>
    ((sumconv THENC BINOP_CONV (wordSizeConv sumconv NUM_ADD_CONV DIMINDEX_CONV) THENC
      NUM_ADD_CONV) ORELSEC DIMINDEX_CONV) tm

structure WordSizes where
  HAS_SIZE_8 : thm
  HAS_SIZE_16 : thm
  HAS_SIZE_32 : thm
  HAS_SIZE_64 : thm
  HAS_SIZE_128 : thm
  HAS_SIZE_256 : thm
  HAS_SIZE_512 : thm
  DIMINDEX_8 : thm
  DIMINDEX_16 : thm
  DIMINDEX_32 : thm
  DIMINDEX_64 : thm
  DIMINDEX_128 : thm
  DIMINDEX_256 : thm
  DIMINDEX_512 : thm
  /-- `add_word_sizes` (words.ml 71-91). -/
  add_word_sizes : List thm → ExceptT String IO Unit
  deriving Inhabited

@[nospecialize]
def setupWordSizes [HolBase] (D : WordsDeps) : ExceptT String IO WordSizes := do
  let { HAS_SIZE_DIMINDEX_RULE, NUM_ADD_CONV, NUM_EXP_CONV, DIMINDEX_CONV, .. } := D
  let { DIMINDEX_1, DIMINDEX_2, DIMINDEX_3, DIMINDEX_4, DIMINDEX_FINITE_SUM,
        DIMINDEX_UNIQUE, .. } := D.core1

  let HAS_SIZE_8 ← HAS_SIZE_DIMINDEX_RULE (← qty "8")
  let HAS_SIZE_16 ← HAS_SIZE_DIMINDEX_RULE (← qty "16")
  let HAS_SIZE_32 ← HAS_SIZE_DIMINDEX_RULE (← qty "32")
  let HAS_SIZE_64 ← HAS_SIZE_DIMINDEX_RULE (← qty "64")
  let HAS_SIZE_128 ← HAS_SIZE_DIMINDEX_RULE (← qty "128")
  let HAS_SIZE_256 ← HAS_SIZE_DIMINDEX_RULE (← qty "256")
  let HAS_SIZE_512 ← HAS_SIZE_DIMINDEX_RULE (← qty "512")

  let DIMINDEX_8 ← MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_8
  let DIMINDEX_16 ← MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_16
  let DIMINDEX_32 ← MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_32
  let DIMINDEX_64 ← MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_64
  let DIMINDEX_128 ← MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_128
  let DIMINDEX_256 ← MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_256
  let DIMINDEX_512 ← MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_512

  /- ----------------------------------------------------------------------- -/
  /- Pre-cache some sizes to speed up computation (only affects efficiency).   -/
  /- ----------------------------------------------------------------------- -/

  let add_word_sizes ← do
    let ptm ← q "(EXP) 2"
    let sumconv ← GEN_REWRITE_CONV_NET id [DIMINDEX_FINITE_SUM]
    let conv := wordSizeConv sumconv NUM_ADD_CONV DIMINDEX_CONV
    let conv2 : ioconv := fun tm =>
      match tm with
      | .Comb t _ => if t == ptm then (RAND_CONV conv THENC NUM_EXP_CONV) tm
                     else pure (.error "conv2")
      | _ => pure (.error "conv2")
    D.word_SIZE_CONV.set conv
    D.word_POW2SIZE_CONV.set conv2
    pure fun (l : List thm) => do
      let m ← D.word_sizes.get
      let m2 ← D.word_pow2sizes.get
      let l2 ← l.mapM (CONV_RULE (RAND_CONV NUM_EXP_CONV) o AP_TERM ptm)
      if subset l m then pure () else do
        D.word_sizes.set (union l m)
        D.word_pow2sizes.set (union l2 m2)
        D.word_SIZE_CONV.set
          ((← GEN_REWRITE_CONV_NET id (← D.word_sizes.get)) ORELSEC conv)
        D.word_POW2SIZE_CONV.set
          ((← GEN_REWRITE_CONV_NET id (← D.word_pow2sizes.get)) ORELSEC conv2)

  add_word_sizes [DIMINDEX_1, DIMINDEX_2, DIMINDEX_3, DIMINDEX_4]

  add_word_sizes [DIMINDEX_8, DIMINDEX_16, DIMINDEX_32, DIMINDEX_64]

  add_word_sizes [DIMINDEX_128, DIMINDEX_256, DIMINDEX_512]

  return { HAS_SIZE_8, HAS_SIZE_16, HAS_SIZE_32, HAS_SIZE_64, HAS_SIZE_128,
           HAS_SIZE_256, HAS_SIZE_512, DIMINDEX_8, DIMINDEX_16, DIMINDEX_32,
           DIMINDEX_64, DIMINDEX_128, DIMINDEX_256, DIMINDEX_512, add_word_sizes }

/- ------------------------------------------------------------------------- -/
/- Some generic lemmas about digit sums.                                     -/
/- ------------------------------------------------------------------------- -/

structure Digitsum where
  DIGITSUM_WORKS_GEN : thm
  DIGITSUM_WORKS : thm
  DIGITSUM_BOUND : thm
  DIGITSUM_SPLIT : thm
  DIGITSUM_DIV : thm
  DIGITSUM_MOD : thm
  DIGITSUM_MOD_NUMSEG : thm
  DIGITSUM_DIV_NUMSEG : thm
  DIGITSUM_DIV_MOD : thm
  DIGITSUM_UNIQUE : thm
  deriving Inhabited

@[nospecialize]
def setupDigitsum [HolBase] (D : WordsDeps) : ExceptT String IO Digitsum := do
  let { ARITH_RULE, ARITH_TAC, MESON, MESON_TAC, ASM_MESON_TAC, SET_RULE, SET_TAC,
        INDUCT_TAC, .. } := D
  let { ADD_SUB, ARITH, CONJ_ASSOC, DIVMOD_UNIQ, DIV_0, DIV_MOD, EMPTY_GSPEC,
        EQ_ADD_RCANCEL, EXP, EXP_ADD, EXTENSION, .. } := D.core1
  let { FINITE_NUMSEG_LT, FINITE_RESTRICT, IN_ELIM_THM, IN_IMAGE, .. } := D.core2
  let { LE_1, LE_MULT_LCANCEL, LT, LT_REFL, MOD_0, MOD_1, MOD_LT, MOD_MULT_MOD,
        MULT_ASSOC, MULT_CLAUSES, MULT_SYM, NOT_IN_EMPTY, NOT_LT, NSUM_CLAUSES,
        NSUM_CLAUSES_NUMSEG_LT, NSUM_EQ, NSUM_IMAGE, NSUM_LMUL, NSUM_RESTRICT_SET,
        NSUM_SING, NSUM_UNION_EQ, NUMSEG_CLAUSES_LT, .. } := D.core3
  let { SING_GSPEC, SUB_REFL, UNWIND_THM2, o_DEF, num_INDUCTION, .. } := D.core4

  let DIGITSUM_WORKS_GEN ← prove
   r"!B n k.
    nsum {i | i < k} (\i. B EXP i * n DIV (B EXP i) MOD B) = n MOD (B EXP k)"
   (GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
    SIMP_TAC [NUMSEG_CLAUSES_LT, NSUM_CLAUSES, MOD_1, EXP, FINITE_NUMSEG_LT] THEN
    X_GEN_TAC (← q "k:num") THEN DISCH_TAC THEN REWRITE_TAC [IN_ELIM_THM, LT_REFL] THEN
    MESON_TAC [MOD_MULT_MOD, MULT_SYM])

  let DIGITSUM_WORKS ← prove
   r"!B n k.
        n < B EXP k
        ==> nsum {i | i < k} (\i. B EXP i * n DIV (B EXP i) MOD B) = n"
   (SIMP_TAC [DIGITSUM_WORKS_GEN, MOD_LT])

  let DIGITSUM_BOUND ← prove
   r"!B b k. (!i. i < k ==> b i < B)
           ==> nsum {i | i < k} (\i. B EXP i * b i) < B EXP k"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [NSUM_CLAUSES_NUMSEG_LT, EXP, ARITH] THEN
    REWRITE_TAC [LT] THEN DISCH_TAC THEN
    MATCH_MP_TAC (← ARITH_RULE
     (← q r"s < e /\ e * (x + 1) <= e * b ==> s + e * x < b * e")) THEN
    ASM_SIMP_TAC [LE_MULT_LCANCEL, ← ARITH_RULE (← q r"b + 1 <= c <=> b < c")])

  let DIGITSUM_SPLIT ← prove
   r"!B b s n.
        FINITE s
        ==> B EXP n * nsum {i | i IN s /\ n <= i} (\i. B EXP (i - n) * b i) +
            nsum {i | i IN s /\ i < n} (\i. B EXP i * b i) =
            nsum s (\i. B EXP i * b i)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [← GSYM NSUM_LMUL, MULT_ASSOC, ← GSYM EXP_ADD] THEN
    SIMP_TAC [← ARITH_RULE (← q r"n:num <= i ==> n + i - n = i")] THEN
    MATCH_MP_TAC NSUM_UNION_EQ THEN ASM_REWRITE_TAC [← GSYM NOT_LT] THEN
    SET_TAC [])

  -- let DIGITSUM_DIV,DIGITSUM_MOD = (CONJ_PAIR o prove) (`...`, tac).  The
  -- three printing rules, in OCaml's order: the second THENL branch is
  -- evaluated first (its MESON before its SET_RULE), then the first branch.
  let mesonB ← MESON [MULT_CLAUSES]
     (← q r"(if p then a * b else 0) = a * (if p then b else 0)")
  let setA ← SET_RULE
     (← q r"{x | x IN s /\ P x} = {x | x IN {y | P y} /\ x IN s}")
  let setC ← SET_RULE (← q r"(!x. ~(x IN s)) <=> s = {}")
  let (DIGITSUM_DIV, DIGITSUM_MOD) ← CONJ_PAIR (← prove
   r"(!B b s n.
        FINITE s /\ (!i. i IN s ==> b i < B)
        ==> nsum s (\i. B EXP i * b i) DIV (B EXP n) =
            nsum {i | i IN s /\ n <= i} (\i. B EXP (i - n) * b i)) /\
   (!B b s n.
        FINITE s /\ (!i. i IN s ==> b i < B)
        ==> nsum s (\i. B EXP i * b i) MOD (B EXP n) =
            nsum {i | i IN s /\ i < n} (\i. B EXP i * b i))"
   (REWRITE_TAC [D.core1.AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q "B = 0") THENL
     [ASM_REWRITE_TAC [← CONJUNCT1 LT, setC] THEN
      SIMP_TAC [EMPTY_GSPEC, NOT_IN_EMPTY, ← CONJUNCT1 NSUM_CLAUSES] THEN
      REWRITE_TAC [DIV_0, MOD_0],
      ALL_TAC] THEN
    REWRITE_TAC [← TAUT (← q r"(p ==> q) /\ (p ==> r) <=> p ==> q /\ r")] THEN
    STRIP_TAC THEN MATCH_MP_TAC DIVMOD_UNIQ THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [MULT_SYM] THEN
      MATCH_MP_TAC (← GSYM DIGITSUM_SPLIT) THEN ASM_REWRITE_TAC [],
      ONCE_REWRITE_TAC [setA] THEN
      REWRITE_TAC [NSUM_RESTRICT_SET, mesonB] THEN
      MATCH_MP_TAC DIGITSUM_BOUND THEN ASM_MESON_TAC [LE_1]]))

  let DIGITSUM_MOD_NUMSEG ← prove
   r"!B b m n.
        (!i. i < m ==> b i < B)
        ==> nsum {i | i < m} (\i. B EXP i * b i) MOD (B EXP n) =
            nsum {i | i < MIN m n} (\i. B EXP i * b i)"
   (SIMP_TAC [DIGITSUM_MOD, FINITE_NUMSEG_LT, IN_ELIM_THM] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"i < MIN m n <=> i < m /\ i < n")])

  let DIGITSUM_DIV_NUMSEG ← prove
   r"!B b m n.
        (!i. i < m ==> b i < B)
        ==> nsum {i | i < m} (\i. B EXP i * b i) DIV (B EXP n) =
            nsum {i | i < m - n} (\i. B EXP i * b(i + n))"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [DIGITSUM_DIV, FINITE_NUMSEG_LT, IN_ELIM_THM] THEN
    SUBGOAL_THEN
     (← q r"{i:num | i < m /\ n <= i} = IMAGE (\i. i + n) {i | i < m - n}")
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM, ← ARITH_RULE
       (← q r"x:num = y + n <=> y = x - n /\ n <= x")] THEN
      REWRITE_TAC [← GSYM CONJ_ASSOC, UNWIND_THM2] THEN ARITH_TAC,
      SIMP_TAC [NSUM_IMAGE, EQ_ADD_RCANCEL, o_DEF, ADD_SUB]])

  -- Two printing MESONs; the later one in the proof is evaluated first.
  let mesonY ← MESON [] (← q r"i IN s /\ i = n <=> n IN s /\ i = n")
  let mesonX ← MESON [EXP, MULT_SYM] (← q r"B EXP n * B = B EXP SUC n")
  let DIGITSUM_DIV_MOD ← prove
   r"!B b s n.
        FINITE s /\ (!i. i IN s ==> b i < B)
        ==> nsum s (\i. B EXP i * b i) DIV (B EXP n) MOD B =
            if n IN s then b n else 0"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [DIV_MOD] THEN
    REWRITE_TAC [mesonX] THEN
    ASM_SIMP_TAC [DIGITSUM_MOD] THEN
    ASM_SIMP_TAC [DIGITSUM_DIV, FINITE_RESTRICT, IN_ELIM_THM] THEN
    REWRITE_TAC [← GSYM CONJ_ASSOC, ← ARITH_RULE (← q r"i < SUC n /\ n <= i <=> i = n")] THEN
    REWRITE_TAC [mesonY] THEN
    ASM_CASES_TAC (← q "(n:num) IN s") THEN
    ASM_REWRITE_TAC [EMPTY_GSPEC, NSUM_CLAUSES] THEN
    REWRITE_TAC [SING_GSPEC, NSUM_SING, SUB_REFL, MULT_CLAUSES, EXP])

  let DIGITSUM_UNIQUE ← prove
   r"!B b c s.
     FINITE s /\
     (!i. i IN s ==> b i < B) /\
     (!i. i IN s ==> c i < B)
     ==> (nsum s (\i. B EXP i * b i) = nsum s (\i. B EXP i * c i) <=>
          !i. i IN s ==> b i = c i)"
   (MESON_TAC [DIGITSUM_DIV_MOD, NSUM_EQ])

  return { DIGITSUM_WORKS_GEN, DIGITSUM_WORKS, DIGITSUM_BOUND, DIGITSUM_SPLIT,
           DIGITSUM_DIV, DIGITSUM_MOD, DIGITSUM_MOD_NUMSEG, DIGITSUM_DIV_NUMSEG,
           DIGITSUM_DIV_MOD, DIGITSUM_UNIQUE }

/- ------------------------------------------------------------------------- -/
/- Mapping a Boolean to the natural number 1 (true) or 0 (false)             -/
/- ------------------------------------------------------------------------- -/

structure Bitval where
  bitval : thm
  BITVAL_CLAUSES : thm
  BITVAL_BOUND : thm
  BITVAL_BOUND_ALT : thm
  ODD_BITVAL : thm
  EVEN_BITVAL : thm
  NUM_AS_BITVAL : thm
  NUM_AS_BITVAL_ALT : thm
  BITVAL_EQ_0 : thm
  BITVAL_EQ_1 : thm
  BITVAL_POS : thm
  BITVAL_NOT : thm
  BITVAL_AND : thm
  BITVAL_OR : thm
  BITVAL_IFF : thm
  BITVAL_XOR : thm
  BITVAL_EXP : thm
  INT_BITVAL_NOT : thm
  INT_BITVAL_AND : thm
  INT_BITVAL_OR : thm
  INT_BITVAL_IMP : thm
  INT_BITVAL_IFF : thm
  INT_BITVAL_POW : thm
  REAL_BITVAL_NOT : thm
  BITVAL_ODD : thm
  LE_BITVAL : thm
  INT_LE_BITVAL : thm
  REAL_LE_BITVAL : thm
  EQ_BITVAL : thm
  INT_EQ_BITVAL : thm
  REAL_EQ_BITVAL : thm
  /-- `BINT_POLY_CONV` (words.ml 357-363). -/
  BINT_POLY_CONV : ioconv
  deriving Inhabited

@[nospecialize]
def setupBitval [HolBase] (D : WordsDeps) : ExceptT String IO Bitval := do
  let { new_definition, ARITH_RULE, ARITH_TAC, INT_ARITH_TAC, MESON_TAC,
        NUM_REDUCE_CONV, NUM_EQ_CONV, INT_POLY_CONV, .. } := D
  let { ARITH, COND_CLAUSES, COND_SWAP, EXISTS_BOOL_THM, EXP, EXP_ONE, EXP_ZERO, .. } := D.core1
  let { FORALL_BOOL_THM, INT_OF_NUM_CLAUSES, INT_OF_NUM_EQ, INT_OF_NUM_LE,
        INT_OF_NUM_SUB, .. } := D.core2
  let { LE_ANTISYM, MOD_2_CASES, NOT_EVEN, .. } := D.core3
  let { REAL_OF_NUM_EQ, REAL_OF_NUM_LE, REAL_OF_NUM_SUB, .. } := D.core4

  let bitval ← new_definition
   r"bitval b = if b then 1 else 0"

  let BITVAL_CLAUSES ← prove
   r"bitval F = 0 /\ bitval T = 1"
   (REWRITE_TAC [bitval])

  let BITVAL_BOUND ← prove
   r"!b. bitval b <= 1"
   (REWRITE_TAC [bitval] THEN ARITH_TAC)

  let BITVAL_BOUND_ALT ← prove
   r"!b. bitval b < 2"
   (REWRITE_TAC [bitval] THEN ARITH_TAC)

  let ODD_BITVAL ← prove
   r"!b. ODD(bitval b) <=> b"
   (REWRITE_TAC [FORALL_BOOL_THM, BITVAL_CLAUSES, ARITH])

  let EVEN_BITVAL ← prove
   r"!b. EVEN(bitval b) <=> ~b"
   (REWRITE_TAC [FORALL_BOOL_THM, BITVAL_CLAUSES, ARITH])

  let NUM_AS_BITVAL ← prove
   r"!n. n <= 1 <=> ?b. n = bitval b"
   (REWRITE_TAC [EXISTS_BOOL_THM, BITVAL_CLAUSES] THEN ARITH_TAC)

  let NUM_AS_BITVAL_ALT ← prove
   r"!n. n < 2 <=> ?b. n = bitval b"
   (REWRITE_TAC [EXISTS_BOOL_THM, BITVAL_CLAUSES] THEN ARITH_TAC)

  let BITVAL_EQ_0 ← prove
   r"!b. bitval b = 0 <=> ~b"
   (GEN_TAC THEN REWRITE_TAC [bitval] THEN
    ASM_CASES_TAC (← q "b:bool") THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC NUM_REDUCE_CONV)

  let BITVAL_EQ_1 ← prove
   r"!b. bitval b = 1 <=> b"
   (GEN_TAC THEN REWRITE_TAC [bitval] THEN
    ASM_CASES_TAC (← q "b:bool") THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC NUM_REDUCE_CONV)

  let BITVAL_POS ← prove
   r"!b. 0 < bitval b <=> b"
   (REWRITE_TAC [← ARITH_RULE (← q r"0 < a <=> ~(a = 0)"), BITVAL_EQ_0])

  let BITVAL_NOT ← prove
   r"!b. bitval(~b) = 1 - bitval b"
   (REWRITE_TAC [FORALL_BOOL_THM, BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV)

  let BITVAL_AND ← prove
   r"!b c. bitval(b /\ c) = bitval b * bitval c"
   (REWRITE_TAC [FORALL_BOOL_THM, BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV)

  let BITVAL_OR ← prove
   r"!b c. bitval(b \/ c) = (bitval b + bitval c) - bitval b * bitval c"
   (REWRITE_TAC [FORALL_BOOL_THM, BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV)

  let BITVAL_IFF ← prove
   r"!b c. bitval(b <=> c) =
         (1 + 2 * bitval b * bitval c) - (bitval b + bitval c)"
   (REWRITE_TAC [FORALL_BOOL_THM, BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV)

  let BITVAL_XOR ← prove
   r"!b c. bitval(~(b <=> c)) = (bitval b + bitval c) - 2 * bitval b * bitval c"
   (REWRITE_TAC [FORALL_BOOL_THM, BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV)

  let BITVAL_EXP ← prove
   r"!b k. bitval b EXP k = if k = 0 then 1 else bitval b"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [EXP] THEN
    REWRITE_TAC [bitval] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [EXP_ZERO, EXP_ONE])

  let INT_BITVAL_NOT ← prove
   r"!b. &(bitval(~b)):int = &1 - &(bitval b)"
   (SIMP_TAC [BITVAL_NOT, ← GSYM INT_OF_NUM_SUB, BITVAL_BOUND])

  let INT_BITVAL_AND ← prove
   r"!b c. &(bitval(b /\ c)):int = &(bitval b) * &(bitval c)"
   (REWRITE_TAC [BITVAL_AND, INT_OF_NUM_CLAUSES])

  let INT_BITVAL_OR ← prove
   r"!b c. &(bitval(b \/ c)):int =
         (&(bitval b) + &(bitval c)) - &(bitval b) * &(bitval c)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [bitval] THEN
    MAP_EVERY ASM_CASES_TAC [← q "b:bool", ← q "c:bool"] THEN
    ASM_REWRITE_TAC [BITVAL_CLAUSES] THEN INT_ARITH_TAC)

  let INT_BITVAL_IMP ← prove
   r"!b c. &(bitval(b ==> c)):int =
         (&1 - &(bitval b) + &(bitval c)) - (&1 - &(bitval b)) * &(bitval c)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [bitval] THEN
    MAP_EVERY ASM_CASES_TAC [← q "b:bool", ← q "c:bool"] THEN
    ASM_REWRITE_TAC [BITVAL_CLAUSES] THEN INT_ARITH_TAC)

  let INT_BITVAL_IFF ← prove
   r"!b c. &(bitval(b <=> c)):int =
         &1 - ((&(bitval b) + &(bitval c)) - &2 * &(bitval b) * &(bitval c))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [bitval] THEN
    MAP_EVERY ASM_CASES_TAC [← q "b:bool", ← q "c:bool"] THEN
    ASM_REWRITE_TAC [BITVAL_CLAUSES] THEN INT_ARITH_TAC)

  let INT_BITVAL_POW ← prove
   r"!b k. &(bitval b) pow k = if k = 0 then &1:int else &(bitval b)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [INT_OF_NUM_CLAUSES, BITVAL_EXP] THEN
    MESON_TAC [])

  let REAL_BITVAL_NOT ← prove
   r"!b. &(bitval(~b)):real = &1 - &(bitval b)"
   (SIMP_TAC [BITVAL_NOT, ← GSYM REAL_OF_NUM_SUB, BITVAL_BOUND])

  let BITVAL_ODD ← prove
   r"!n. bitval(ODD n) = n MOD 2"
   (REWRITE_TAC [bitval, ← GSYM NOT_EVEN, MOD_2_CASES, COND_SWAP])

  let LE_BITVAL ← prove
   r"!b c. bitval b <= bitval c <=> b ==> c"
   (REPEAT GEN_TAC THEN REWRITE_TAC [bitval] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC NUM_REDUCE_CONV)

  let INT_LE_BITVAL ← prove
   r"!b c. &(bitval b):int <= &(bitval c) <=> b ==> c"
   (REWRITE_TAC [INT_OF_NUM_LE, LE_BITVAL])

  let REAL_LE_BITVAL ← prove
   r"!b c. &(bitval b):real <= &(bitval c) <=> b ==> c"
   (REWRITE_TAC [REAL_OF_NUM_LE, LE_BITVAL])

  let EQ_BITVAL ← prove
   r"!b c. (bitval b = bitval c) <=> (b <=> c)"
   (REWRITE_TAC [← GSYM LE_ANTISYM, LE_BITVAL] THEN CONV_TAC (fun t => (TAUT t).run))

  let INT_EQ_BITVAL ← prove
   r"!b c. &(bitval b):int = &(bitval c) <=> (b <=> c)"
   (REWRITE_TAC [INT_OF_NUM_EQ, EQ_BITVAL])

  let REAL_EQ_BITVAL ← prove
   r"!b c. &(bitval b):real = &(bitval c) <=> (b <=> c)"
   (REWRITE_TAC [REAL_OF_NUM_EQ, EQ_BITVAL])

  let BINT_POLY_CONV ← do
    let bitpow_conv :=
      (← GEN_REWRITE_CONV_NET id [INT_BITVAL_POW]) THENC
      RATOR_CONV (LAND_CONV NUM_EQ_CONV) THENC
      (← GEN_REWRITE_CONV_NET id [COND_CLAUSES])
    pure (INT_POLY_CONV THENC
          ONCE_DEPTH_CONV bitpow_conv THENC
          INT_POLY_CONV)

  return { bitval, BITVAL_CLAUSES, BITVAL_BOUND, BITVAL_BOUND_ALT, ODD_BITVAL,
           EVEN_BITVAL, NUM_AS_BITVAL, NUM_AS_BITVAL_ALT, BITVAL_EQ_0, BITVAL_EQ_1,
           BITVAL_POS, BITVAL_NOT, BITVAL_AND, BITVAL_OR, BITVAL_IFF, BITVAL_XOR,
           BITVAL_EXP, INT_BITVAL_NOT, INT_BITVAL_AND, INT_BITVAL_OR, INT_BITVAL_IMP,
           INT_BITVAL_IFF, INT_BITVAL_POW, REAL_BITVAL_NOT, BITVAL_ODD, LE_BITVAL,
           INT_LE_BITVAL, REAL_LE_BITVAL, EQ_BITVAL, INT_EQ_BITVAL, REAL_EQ_BITVAL,
           BINT_POLY_CONV }

/- ------------------------------------------------------------------------- -/
/- Some more binary-specific lemmas.                                         -/
/- ------------------------------------------------------------------------- -/

structure Binary where
  ODD_MOD_POW2 : thm
  BINARY_DIGITSUM_BOUND : thm
  BINARY_DIGITSUM_SPLIT : thm
  BINARY_DIGITSUM_DIV : thm
  BINARY_DIGITSUM_MOD : thm
  deriving Inhabited

@[nospecialize]
def setupBinary [HolBase] (D : WordsDeps) (G : Digitsum) (V : Bitval) :
    ExceptT String IO Binary := do
  let { ARITH, EVEN_EXP, EXP, .. } := D.core1
  let { MOD_1, ODD, ODD_MOD_EVEN, .. } := D.core3
  let { DIGITSUM_BOUND, DIGITSUM_SPLIT, DIGITSUM_DIV, DIGITSUM_MOD, .. } := G
  let { BITVAL_BOUND_ALT, .. } := V

  let ODD_MOD_POW2 ← prove
   r"!n k. ODD(n MOD 2 EXP k) <=> ~(k = 0) /\ ODD n"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "k = 0") THEN
    ASM_REWRITE_TAC [MOD_1, EXP, ODD] THEN
    ASM_SIMP_TAC [ODD_MOD_EVEN, EVEN_EXP, ARITH])

  let BINARY_DIGITSUM_BOUND ← prove
   r"!b k. nsum {i | i < k} (\i. 2 EXP i * bitval(b i)) < 2 EXP k"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC DIGITSUM_BOUND THEN
    REWRITE_TAC [BITVAL_BOUND_ALT])

  let BINARY_DIGITSUM_SPLIT ← prove
   r"!b s n.
        FINITE s
        ==> 2 EXP n *
            nsum {i | i IN s /\ n <= i} (\i. 2 EXP (i - n) * bitval(b i)) +
            nsum {i | i IN s /\ i < n} (\i. 2 EXP i * bitval(b i)) =
            nsum s (\i. 2 EXP i * bitval(b i))"
   (MATCH_ACCEPT_TAC DIGITSUM_SPLIT)

  let BINARY_DIGITSUM_DIV ← prove
   r"!b s n.
        FINITE s
        ==> nsum s (\i. 2 EXP i * bitval(b i)) DIV (2 EXP n) =
            nsum {i | i IN s /\ n <= i} (\i. 2 EXP (i - n) * bitval(b i))"
   (SIMP_TAC [DIGITSUM_DIV, BITVAL_BOUND_ALT])

  let BINARY_DIGITSUM_MOD ← prove
   r"!b s n.
        FINITE s
        ==> nsum s (\i. 2 EXP i * bitval(b i)) MOD (2 EXP n) =
            nsum {i | i IN s /\ i < n} (\i. 2 EXP i * bitval(b i))"
   (SIMP_TAC [DIGITSUM_MOD, BITVAL_BOUND_ALT])

  return { ODD_MOD_POW2, BINARY_DIGITSUM_BOUND, BINARY_DIGITSUM_SPLIT,
           BINARY_DIGITSUM_DIV, BINARY_DIGITSUM_MOD }

/- ------------------------------------------------------------------------- -/
/- Destructors and constructors for the N-bit word type from nums.           -/
/- ------------------------------------------------------------------------- -/

/-- `dest_word_ty ty` (words.ml 422-425). -/
def dest_word_ty : hol_type → Except String Rat
  | .Tyapp "word" [n] => dest_finty n
  | _ => .error "dest_word_ty"

/-- `mk_word_ty n` (words.ml 427). -/
def mk_word_ty (n : Rat) : ExceptT String IO hol_type := do
  ExceptT.mk (mk_type "word" [← ExceptT.mk (mk_finty n)])

/- ------------------------------------------------------------------------- -/
/- The type "N word" is in bijection with "bool^N"; specific sizes; and      -/
/- individual selection of bits, indexing from 0 as usual.                   -/
/- ------------------------------------------------------------------------- -/

structure WordType where
  word_tybij : thm
  WORD_EQ_BITVECTOR : thm
  bit : thm
  WORD_EQ_BITS_ALT : thm
  WORD_EQ_BITS : thm
  BIT_TRIVIAL : thm
  BIT_GUARD : thm
  deriving Inhabited

@[nospecialize]
def setupWordType [HolBase] (D : WordsDeps) : ExceptT String IO WordType := do
  let { new_definition, new_type_definition, new_type_abbrev, ARITH_RULE, MESON_TAC,
        .. } := D
  let { CART_EQ, .. } := D.core1
  let { NOT_LT, .. } := D.core3

  let word_tybij ← do
    let th ← prove r"?x:bool^N. T" (REWRITE_TAC [])
    REWRITE_RULE []
     (← new_type_definition "word" ("mk_word", "bitvector") th)

  let WORD_EQ_BITVECTOR ← prove
   r"!v w:N word. v = w <=> bitvector v = bitvector w"
   (MESON_TAC [word_tybij])

  /- Set up some specific sizes that we want (words.ml 432-437). -/
  new_type_abbrev "nybble" (← qty "(4)word")
  new_type_abbrev "byte" (← qty "(8)word")
  new_type_abbrev "int16" (← qty "(16)word")
  new_type_abbrev "int32" (← qty "(32)word")
  new_type_abbrev "int64" (← qty "(64)word")
  new_type_abbrev "int128" (← qty "(128)word")

  let bit ← new_definition
   r"bit i (w:N word) =
    if i < dimindex(:N) then (bitvector w)$(i + 1)
    else F"

  let WORD_EQ_BITS_ALT ← prove
   r"!v w:N word. v = w <=> !i. i < dimindex(:N) ==> bit i v = bit i w"
   (REPEAT GEN_TAC THEN SIMP_TAC [WORD_EQ_BITVECTOR, bit, CART_EQ] THEN
    MESON_TAC [← ARITH_RULE (← q r"i < n ==> 1 <= i + 1 /\ i + 1 <= n"),
               ← ARITH_RULE (← q r"1 <= i /\ i <= n ==> i = (i - 1) + 1 /\ i - 1 < n")])

  let WORD_EQ_BITS ← prove
   r"!v w:N word. v = w <=> !i. bit i v = bit i w"
   (MESON_TAC [bit, WORD_EQ_BITS_ALT])

  let BIT_TRIVIAL ← prove
   r"!w:(N)word i. dimindex(:N) <= i ==> (bit i w <=> F)"
   (SIMP_TAC [← GSYM NOT_LT, bit])

  let BIT_GUARD ← prove
   r"!(x:N word) i. bit i x <=> i < dimindex(:N) /\ bit i x"
   (MESON_TAC [NOT_LT, BIT_TRIVIAL])

  return { word_tybij, WORD_EQ_BITVECTOR, bit, WORD_EQ_BITS_ALT, WORD_EQ_BITS,
           BIT_TRIVIAL, BIT_GUARD }

/- ------------------------------------------------------------------------- -/
/- Mappings to and from sets of bits.                                        -/
/- ------------------------------------------------------------------------- -/

structure BitsOfWord where
  bits_of_word : thm
  word_of_bits : thm
  IN_BITS_OF_WORD : thm
  BIT_WORD_OF_BITS : thm
  WORD_OF_BITS_EQ : thm
  WORD_OF_BITS_OF_WORD : thm
  BITS_OF_WORD_OF_BITS : thm
  BITS_OF_WORD_EQ : thm
  WORD_OF_BITS : thm
  WORD_OF_BITS_ALT : thm
  FINITE_BITS_OF_WORD : thm
  BITS_OF_WORD_SUBSET : thm
  BITS_OF_WORD_SUBSET_ALT : thm
  BITS_OF_WORD_SUBSET_NUMSEG : thm
  deriving Inhabited

@[nospecialize]
def setupBitsOfWord [HolBase] (D : WordsDeps) (W : WordType) :
    ExceptT String IO BitsOfWord := do
  let { new_definition, ARITH_RULE, MESON_TAC, .. } := D
  let { ADD_SUB, EXTENSION, .. } := D.core1
  let { FINITE_NUMSEG_LT, FINITE_SUBSET, IN_ELIM_THM, IN_INTER, .. } := D.core2
  let { LAMBDA_BETA, NOT_LE, NOT_LT, .. } := D.core3
  let { SUBSET, .. } := D.core4
  let { word_tybij, bit, WORD_EQ_BITS_ALT, WORD_EQ_BITS, BIT_TRIVIAL, BIT_GUARD, .. } := W

  let bits_of_word ← new_definition
   r"bits_of_word (w:N word) = {i | bit i w}"

  let word_of_bits ← new_definition
   r"word_of_bits s:N word = mk_word(lambda i. (i - 1) IN s)"

  let IN_BITS_OF_WORD ← prove
   r"!(w:N word) i. i IN bits_of_word w <=> bit i w"
   (REWRITE_TAC [bits_of_word, IN_ELIM_THM])

  let BIT_WORD_OF_BITS ← prove
   r"!s i. bit i (word_of_bits s:N word) <=> i < dimindex(:N) /\ i IN s"
   (REPEAT GEN_TAC THEN REWRITE_TAC [bit, word_of_bits] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [word_tybij] THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP (← ARITH_RULE
     (← q r"i < n ==> 1 <= i + 1 /\ i + 1 <= n"))) THEN
    ASM_SIMP_TAC [LAMBDA_BETA, ADD_SUB])

  let WORD_OF_BITS_EQ ← prove
   r"!s t. word_of_bits s:N word = word_of_bits t <=>
         !i. i < dimindex(:N) ==> (i IN s <=> i IN t)"
   (SIMP_TAC [WORD_EQ_BITS, BIT_WORD_OF_BITS] THEN MESON_TAC [])

  let WORD_OF_BITS_OF_WORD ← prove
   r"!w:N word. word_of_bits(bits_of_word w) = w"
   (SIMP_TAC [WORD_EQ_BITS_ALT, BIT_WORD_OF_BITS, bits_of_word, IN_ELIM_THM])

  let BITS_OF_WORD_OF_BITS ← prove
   r"!s. bits_of_word(word_of_bits s:N word) = s INTER {i | i < dimindex(:N)}"
   (GEN_TAC THEN REWRITE_TAC [bits_of_word] THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INTER, BIT_WORD_OF_BITS] THEN
    CONV_TAC (fun t => (TAUT t).run))

  let BITS_OF_WORD_EQ ← prove
   r"!v w:N word. bits_of_word v = bits_of_word w <=> v = w"
   (MESON_TAC [WORD_OF_BITS_OF_WORD])

  let WORD_OF_BITS ← prove
   r"!w:N word. w = word_of_bits {i | bit i w}"
   (REWRITE_TAC [← GSYM bits_of_word, WORD_OF_BITS_OF_WORD])

  let WORD_OF_BITS_ALT ← prove
   r"!w:N word. w = word_of_bits {i | i < dimindex(:N) /\ bit i w}"
   (SIMP_TAC [WORD_EQ_BITS, BIT_WORD_OF_BITS, IN_ELIM_THM] THEN
    MESON_TAC [BIT_TRIVIAL, NOT_LE])

  let FINITE_BITS_OF_WORD ← prove
   r"!w:N word. FINITE(bits_of_word w)"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC (← q r"{i | i < dimindex(:N)}") THEN
    REWRITE_TAC [bits_of_word, FINITE_NUMSEG_LT, SUBSET, IN_ELIM_THM] THEN
    MESON_TAC [BIT_TRIVIAL, NOT_LT])

  let BITS_OF_WORD_SUBSET ← prove
   r"!(x:M word) (y:N word).
        bits_of_word x SUBSET bits_of_word y <=> !i. bit i x ==> bit i y"
   (REWRITE_TAC [SUBSET, IN_BITS_OF_WORD])

  let BITS_OF_WORD_SUBSET_ALT ← prove
   r"!(x:M word) (y:N word).
        bits_of_word x SUBSET bits_of_word y <=>
        !i. i < dimindex(:M) /\ bit i x ==> bit i y"
   (REWRITE_TAC [← GSYM BIT_GUARD, BITS_OF_WORD_SUBSET])

  let BITS_OF_WORD_SUBSET_NUMSEG ← prove
   r"!x:N word. bits_of_word x SUBSET {i | i < dimindex(:N)}"
   (REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_BITS_OF_WORD] THEN
    MESON_TAC [BIT_GUARD])

  return { bits_of_word, word_of_bits, IN_BITS_OF_WORD, BIT_WORD_OF_BITS,
           WORD_OF_BITS_EQ, WORD_OF_BITS_OF_WORD, BITS_OF_WORD_OF_BITS,
           BITS_OF_WORD_EQ, WORD_OF_BITS, WORD_OF_BITS_ALT, FINITE_BITS_OF_WORD,
           BITS_OF_WORD_SUBSET, BITS_OF_WORD_SUBSET_ALT, BITS_OF_WORD_SUBSET_NUMSEG }

/- ------------------------------------------------------------------------- -/
/- Mapping to and from natural number values (treating as unsigned word).    -/
/- ------------------------------------------------------------------------- -/

structure Val where
  val_def : thm
  VAL : thm
  word : thm
  BIT_WORD : thm
  BIT_LSB_WORD : thm
  BIT_WORD_0 : thm
  BITS_OF_WORD_0 : thm
  BITS_OF_WORD_EQ_EMPTY : thm
  WORD_OF_BITS_EMPTY : thm
  BITVAL_BIT_WORD : thm
  WORD_VAL : thm
  VAL_WORD : thm
  MOD_VAL_WORD : thm
  DIVIDES_VAL_WORD : thm
  VAL_WORD_LE : thm
  VAL_WORD_LT : thm
  FORALL_WORD : thm
  EXISTS_WORD : thm
  VAL_WORD_0 : thm
  VAL_WORD_1 : thm
  WORD_BITVAL : thm
  VAL_WORD_BITVAL : thm
  VAL_WORD_EQ : thm
  VAL_EQ : thm
  VAL_EQ_0 : thm
  VAL_EQ_1 : thm
  VAL_EQ_BITVAL : thm
  WORD_BITVAL_EQ_0 : thm
  WORD_BITVAL_EQ_1 : thm
  WORD_NE_10 : thm
  WORD_EQ : thm
  WORD_EQ_IMP : thm
  WORD_EQ_0 : thm
  VAL_BOUND : thm
  INT_VAL_BOUND : thm
  VAL_MOD_REFL : thm
  VAL_WORD_EQ_EQ : thm
  FORALL_VAL_GEN : thm
  FORALL_VAL : thm
  VAL_CONG : thm
  WORD_MOD_SIZE : thm
  VAL_WORD_CONG : thm
  VAL_WORD_GALOIS : thm
  WORD_VAL_GALOIS : thm
  DIVIDES_VAL_WORD_EQ : thm
  BIT_VAL : thm
  BIT_VAL_MOD : thm
  BIT_LSB : thm
  TWICE_MSB : thm
  MSB_VAL : thm
  MSB_INT_VAL : thm
  BITVAL_MSB : thm
  BLOCK_BITS_ZERO_ALT : thm
  BLOCK_BITS_ZERO : thm
  LOWER_BITS_ZERO : thm
  UPPER_BITS_ZERO : thm
  UPPER_BITS_ZERO_ALT : thm
  VAL_WORD_OF_BITS : thm
  WORD_OF_BITS_AS_WORD : thm
  WORD_OF_BITS_AS_WORD_FINITE : thm
  WORD_OF_BITS_SING_AS_WORD : thm
  VAL_WORD_OF_BITS_SING : thm
  WORD_OF_BITS_MASK : thm
  BIT_MASK_WORD : thm
  BIT_WORD_POW2 : thm
  BIT_WORD_1 : thm
  BIT_WORD_BITVAL : thm
  WORD_OF_BITS_SING_AS_WORD_1 : thm
  BITS_OF_WORD_1 : thm
  BIT_WORD_OF_BITS_SING : thm
  VAL_MOD : thm
  VAL_MOD_2 : thm
  VAL_MOD_STEP : thm
  VAL_DIV : thm
  VAL_DIV_ALT : thm
  VAL_LE_BITS : thm
  VAL_LE_SUBSET : thm
  deriving Inhabited

@[nospecialize]
def setupVal [HolBase] (D : WordsDeps) (Bn : Binary) (V : Bitval) (W : WordType)
    (BW : BitsOfWord) : ExceptT String IO Val := do
  let { new_definition, ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, INDUCT_TAC, MESON,
        MESON_TAC, NUMBER_RULE, SET_RULE, SET_TAC, NUM_REDUCE_CONV, .. } := D
  let { ADD_SUB, ARITH_EQ, COND_ID, COND_RAND, CONG, CONG_NSUM, CONJ_SYM,
        DIMINDEX_GE_1, DIMINDEX_NONZERO, DIVIDES_LE, DIVIDES_MOD, DIV_0, DIV_1,
        DIV_EQ_0, DIV_MOD, EMPTY_GSPEC, EVEN, EVEN_ADD, EVEN_EXP, EVEN_MOD,
        EVEN_MULT, EXP, EXP_1, EXP_ADD, EXP_EQ_0, EXP_LT_0, .. } := D.core1
  let { FINITE_NUMSEG_LT, FINITE_RESTRICT, FINITE_SING, FORALL_BOOL_THM,
        IMP_CONJ, INT_OF_NUM_LE, INT_OF_NUM_LT, INT_OF_NUM_POW, INT_POW,
        IN_ELIM_THM, IN_NUMSEG, IN_SING, .. } := D.core2
  let { LAMBDA_BETA, LEFT_IMP_EXISTS_THM, LET_TRANS, LE_1, LE_EXISTS, LE_EXP,
        LE_MULT_LCANCEL, LTE_TRANS, LT_EXP, LT_IMP_LE, LT_REFL, MOD_0, MOD_1,
        MOD_LE, MOD_LT, MOD_MOD_EXP_MIN, MOD_MOD_REFL, MOD_MULT_MOD, MULT_CLAUSES,
        MULT_EQ_0, MULT_SYM, NOT_EVEN, NOT_IN_EMPTY, NOT_LE, NOT_LT, NOT_ODD,
        NSUM_CLAUSES, NSUM_CLAUSES_LEFT, NSUM_CLAUSES_NUMSEG_LT, NSUM_CLOSED,
        NSUM_DELTA, NSUM_EQ_0_IFF, NSUM_EQ_GENERAL_INVERSES, NSUM_LE,
        NSUM_RESTRICT_SET, NSUM_SING, NSUM_SUPERSET, NUMSEG_LT, ODD, ODD_ADD,
        ODD_MOD, .. } := D.core3
  let { RDIV_LT_EQ, SING_GSPEC, SUBSET, SUB_ADD, SUB_REFL, bool_INDUCT, numseg,
        .. } := D.core4
  let { BINARY_DIGITSUM_BOUND, BINARY_DIGITSUM_DIV, BINARY_DIGITSUM_MOD, .. } := Bn
  let { bitval, BITVAL_CLAUSES, BITVAL_EQ_0, BITVAL_EQ_1, LE_BITVAL, .. } := V
  let { word_tybij, bit, WORD_EQ_BITS_ALT, BIT_TRIVIAL, .. } := W
  let { bits_of_word, BIT_WORD_OF_BITS, BITS_OF_WORD_EQ, BITS_OF_WORD_SUBSET_ALT, .. } := BW

  let val_def ← new_definition
   r"val (w:N word) =
    nsum {i | i < dimindex(:N)} (\i. 2 EXP i * bitval(bit i w))"

  let VAL ← prove
   r"!x:N word.
       val(x) = nsum(0..dimindex(:N)-1) (\i. 2 EXP i * bitval(bit i x))"
   (REWRITE_TAC [val_def, NUMSEG_LT, DIMINDEX_NONZERO])

  let word ← new_definition
   r"(word:num->N word) n =
    mk_word(lambda i. ODD(n DIV (2 EXP (i - 1))))"

  let BIT_WORD ← prove
   r"!i n. bit i (word n:N word) <=> i < dimindex(:N) /\ ODD(n DIV (2 EXP i))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [bit] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [word, word_tybij] THEN
    ASM_SIMP_TAC [LAMBDA_BETA, ADD_SUB, ← ARITH_RULE (← q r"1 <= i + 1"),
                  ← ARITH_RULE (← q r"i < n ==> i + 1 <= n")])

  let BIT_LSB_WORD ← prove
   r"!n. bit 0 (word n) <=> ODD n"
   (SIMP_TAC [BIT_WORD, DIV_1, EXP, DIMINDEX_GE_1, LE_1])

  let BIT_WORD_0 ← prove
   r"!i. bit i (word 0:N word) <=> F"
   (REWRITE_TAC [BIT_WORD, DIV_0, ODD])

  let BITS_OF_WORD_0 ← prove
   r"bits_of_word(word 0:N word) = {}"
   (REWRITE_TAC [bits_of_word, BIT_WORD_0, EMPTY_GSPEC])

  let BITS_OF_WORD_EQ_EMPTY ← prove
   r"!w:N word. bits_of_word w = {} <=> w = word 0"
   (REWRITE_TAC [← GSYM BITS_OF_WORD_EQ, BITS_OF_WORD_0])

  let WORD_OF_BITS_EMPTY ← prove
   r"word_of_bits {}:N word = word 0"
   (REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_0, BIT_WORD_OF_BITS] THEN
    REWRITE_TAC [NOT_IN_EMPTY])

  let BITVAL_BIT_WORD ← prove
   r"!i n. bitval(bit i (word n:N word)) =
         if i < dimindex(:N) then (n DIV (2 EXP i)) MOD 2 else 0"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [BIT_WORD, bitval, ODD_MOD] THEN
    ARITH_TAC)

  let WORD_VAL ← prove
   r"!w:N word. word(val w) = w"
   (GEN_TAC THEN SIMP_TAC [WORD_EQ_BITS_ALT, val_def, BIT_WORD] THEN
    X_GEN_TAC (← q "k:num") THEN DISCH_TAC THEN
    SIMP_TAC [BINARY_DIGITSUM_DIV, FINITE_NUMSEG_LT] THEN
    ASM_SIMP_TAC [IN_ELIM_THM, ← GSYM numseg, ← ARITH_RULE
     (← q r"k < n ==> (i < n /\ k <= i <=> k <= i /\ i <= n - 1)")] THEN
    ASM_SIMP_TAC [NSUM_CLAUSES_LEFT, ← ARITH_RULE (← q r"k < n ==> k <= n - 1")] THEN
    MATCH_MP_TAC (← MESON [ODD, ODD_ADD]
     (← q r"~ODD n /\ (ODD m <=> p) ==> (ODD(m + n) <=> p)")) THEN
    REWRITE_TAC [SUB_REFL, EXP, NOT_ODD, MULT_CLAUSES] THEN CONJ_TAC THENL
     [MATCH_MP_TAC NSUM_CLOSED THEN
      SIMP_TAC [EVEN, EVEN_ADD, EVEN_MULT, EVEN_EXP, IN_NUMSEG] THEN
      ASM_ARITH_TAC,
      REWRITE_TAC [bitval] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV])

  let VAL_WORD ← prove
   r"!n. val(word n:N word) = n MOD (2 EXP (dimindex(:N)))"
   (GEN_TAC THEN SIMP_TAC [val_def, BITVAL_BIT_WORD] THEN
    SPEC_TAC (← q "dimindex(:N)", ← q "k:num") THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [NSUM_CLAUSES_NUMSEG_LT, EXP, MOD_1] THEN
    ONCE_REWRITE_TAC [MULT_SYM] THEN REWRITE_TAC [MOD_MULT_MOD] THEN ARITH_TAC)

  let MOD_VAL_WORD ← prove
   r"!n k. k <= dimindex(:N) ==> val(word n:N word) MOD 2 EXP k = n MOD 2 EXP k"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [VAL_WORD, MOD_MOD_EXP_MIN] THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"k <= n ==> MIN n k = k")])

  let DIVIDES_VAL_WORD ← prove
   r"!n x. n <= dimindex(:N)
         ==> (2 EXP n divides val(word x:N word) <=> 2 EXP n divides x)"
   (SIMP_TAC [MOD_VAL_WORD, DIVIDES_MOD])

  let VAL_WORD_LE ← prove
   r"!n k. n <= k ==> val(word n:N word) <= k"
   (REWRITE_TAC [VAL_WORD] THEN MESON_TAC [D.core3.LE_TRANS, MOD_LE])

  let VAL_WORD_LT ← prove
   r"!n k. n < k ==> val(word n:N word) < k"
   (REWRITE_TAC [VAL_WORD] THEN MESON_TAC [LET_TRANS, MOD_LE])

  let FORALL_WORD ← prove
   r"!P. (!x:N word. P x) <=> (!n. P(word n))"
   (MESON_TAC [WORD_VAL])

  let EXISTS_WORD ← prove
   r"!P. (?x:N word. P x) <=> (?n. P(word n))"
   (MESON_TAC [WORD_VAL])

  let VAL_WORD_0 ← prove
   r"val(word 0:(N)word) = 0"
   (SIMP_TAC [VAL_WORD, MOD_0, EXP_EQ_0, ARITH_EQ])

  let VAL_WORD_1 ← prove
   r"val(word 1:(N)word) = 1"
   (REWRITE_TAC [VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN
    GEN_REWRITE_TAC LAND_CONV [← ARITH_RULE (← q r"1 = 2 EXP 0")] THEN
    SIMP_TAC [LT_EXP, LE_1, DIMINDEX_GE_1] THEN ARITH_TAC)

  let WORD_BITVAL ← prove
   r"!b. word(bitval b) = if b then word 1 else word 0"
   (REWRITE_TAC [bitval] THEN MESON_TAC [])

  let VAL_WORD_BITVAL ← prove
   r"!b. val(word(bitval b)) = bitval b"
   (MATCH_MP_TAC bool_INDUCT THEN
    REWRITE_TAC [VAL_WORD_1, VAL_WORD_0, BITVAL_CLAUSES])

  let VAL_WORD_EQ ← prove
   r"!n. n < 2 EXP dimindex(:N) ==> val(word n :(N)word) = n"
   (SIMP_TAC [VAL_WORD, MOD_LT])

  let VAL_EQ ← prove
   r"!(v:N word) (w:N word). val v = val w <=> v = w"
   (MESON_TAC [WORD_VAL])

  let VAL_EQ_0 ← prove
   r"!w:(N)word. val w = 0 <=> w = word 0"
   (MESON_TAC [VAL_WORD_0, VAL_EQ])

  let VAL_EQ_1 ← prove
   r"!w:(N)word. val w = 1 <=> w = word 1"
   (MESON_TAC [VAL_WORD_1, VAL_EQ])

  let VAL_EQ_BITVAL ← prove
   r"!w:(N)word b. val w = bitval b <=> w = word(bitval b)"
   (REWRITE_TAC [FORALL_BOOL_THM, BITVAL_CLAUSES, VAL_EQ_0, VAL_EQ_1])

  let WORD_BITVAL_EQ_0 ← prove
   r"!b. word(bitval b):N word = word 0 <=> ~b"
   (REWRITE_TAC [← GSYM VAL_EQ_0, VAL_WORD_BITVAL, BITVAL_EQ_0])

  let WORD_BITVAL_EQ_1 ← prove
   r"!b. word(bitval b):N word = word 1 <=> b"
   (REWRITE_TAC [← GSYM VAL_EQ_1, VAL_WORD_BITVAL, BITVAL_EQ_1])

  let WORD_NE_10 ← prove
   r"~(word 1:N word = word 0)"
   (REWRITE_TAC [← GSYM VAL_EQ_0, VAL_WORD_1] THEN CONV_TAC NUM_REDUCE_CONV)

  let WORD_EQ ← prove
   r"!x y. word x:(N)word = word y <=> (x == y) (mod (2 EXP dimindex(:N)))"
   (MESON_TAC [VAL_WORD, WORD_VAL, CONG])

  let WORD_EQ_IMP ← prove
   r"!m n. m < 2 EXP dimindex(:N) /\ n < 2 EXP dimindex(:N)
         ==> (word m:N word = word n <=> m = n)"
   (REWRITE_TAC [WORD_EQ, CONG] THEN SIMP_TAC [MOD_LT])

  let WORD_EQ_0 ← prove
   r"!m. m < 2 EXP dimindex(:N) ==> (word m:N word = word 0 <=> m = 0)"
   (SIMP_TAC [WORD_EQ_IMP, EXP_LT_0, ARITH_EQ])

  let VAL_BOUND ← prove
   r"!w:N word. val w < 2 EXP dimindex(:N)"
   (REWRITE_TAC [val_def, BINARY_DIGITSUM_BOUND])

  let INT_VAL_BOUND ← prove
   r"!w:N word. &(val w):int < &2 pow dimindex(:N)"
   (REWRITE_TAC [INT_OF_NUM_POW, INT_OF_NUM_LT, VAL_BOUND])

  let VAL_MOD_REFL ← prove
   r"!x:(N)word. (val x) MOD (2 EXP dimindex(:N)) = val x"
   (MESON_TAC [MOD_LT, VAL_BOUND])

  let VAL_WORD_EQ_EQ ← prove
   r"!n. val(word n:N word) = n <=> n < 2 EXP dimindex(:N)"
   (MESON_TAC [VAL_WORD_EQ, VAL_BOUND])

  let FORALL_VAL_GEN ← prove
   r"!P. (!x:N word. P (val x) x) <=>
       !n. n < 2 EXP dimindex(:N) ==> P n (word n)"
   (MESON_TAC [VAL_WORD_EQ, WORD_VAL, VAL_BOUND])

  let FORALL_VAL ← prove
   r"!P. (!x:N word. P(val x)) <=> (!n. n < 2 EXP dimindex(:N) ==> P n)"
   (REWRITE_TAC [FORALL_VAL_GEN])

  let VAL_CONG ← prove
   r"!(v:N word) (w:N word).
        (val v == val w) (mod (2 EXP dimindex(:N))) <=> v = w"
   (REWRITE_TAC [← GSYM VAL_EQ, CONG, MOD_MOD_REFL, VAL_MOD_REFL])

  let WORD_MOD_SIZE ← prove
   r"!n. word(n MOD (2 EXP dimindex(:N))):N word = word n"
   (REWRITE_TAC [WORD_EQ, CONG, MOD_MOD_REFL])

  let VAL_WORD_CONG ← prove
   r"!x. (val(word x:N word) == x) (mod (2 EXP (dimindex(:N))))"
   (REWRITE_TAC [VAL_WORD, CONG, MOD_MOD_REFL])

  let VAL_WORD_GALOIS ← prove
   r"!(w:N word) n. val w = n <=> n < 2 EXP dimindex(:N) /\ w = word n"
   (MESON_TAC [WORD_VAL, VAL_WORD_EQ, VAL_BOUND])

  let WORD_VAL_GALOIS ← prove
   r"!(w:N word) n. word n = w <=> n MOD 2 EXP dimindex(:N) = val w"
   (MESON_TAC [VAL_WORD, WORD_MOD_SIZE, WORD_VAL])

  let DIVIDES_VAL_WORD_EQ ← prove
   r"!n x. 2 EXP n divides val(word x:N word) <=>
         if n < dimindex(:N) then 2 EXP n divides x
         else word x:N word = word 0"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [DIVIDES_VAL_WORD, LT_IMP_LE] THEN
    EQ_TAC THEN SIMP_TAC [VAL_WORD_0, ← NUMBER_RULE (← q r"n divides 0")] THEN
    DISCH_THEN (MP_TAC o MATCH_MP DIVIDES_LE) THEN
    REWRITE_TAC [VAL_EQ_0] THEN MATCH_MP_TAC (← TAUT (← q r"~p ==> p \/ q ==> q")) THEN
    REWRITE_TAC [NOT_LE] THEN TRANS_TAC LTE_TRANS (← q "2 EXP dimindex(:N)") THEN
    REWRITE_TAC [VAL_BOUND, LE_EXP] THEN ASM_ARITH_TAC)

  let BIT_VAL ← prove
   r"!(x:N word) i. bit i x <=> ODD(val x DIV (2 EXP i))"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM WORD_VAL] THEN
    REWRITE_TAC [BIT_WORD, ← TAUT (← q r"(p /\ q <=> q) <=> (~p ==> ~q)")] THEN
    REWRITE_TAC [NOT_LT] THEN DISCH_TAC THEN
    MATCH_MP_TAC (← MESON [ODD] (← q r"n = 0 ==> ~ODD n")) THEN
    ASM_SIMP_TAC [DIV_EQ_0, EXP_EQ_0, ARITH_EQ] THEN
    TRANS_TAC LTE_TRANS (← q "2 EXP dimindex(:N)") THEN
    ASM_REWRITE_TAC [VAL_BOUND, LE_EXP, DIMINDEX_NONZERO, COND_ID])

  let BIT_VAL_MOD ← prove
   r"!(x:N word) k.
        bit k x <=> 2 EXP k <= val(x) MOD 2 EXP (k + 1)"
   (REWRITE_TAC [BIT_VAL, ← GSYM NOT_EVEN, EVEN_MOD, EXP_ADD, EXP_1, DIV_MOD] THEN
    SIMP_TAC [DIV_EQ_0, NOT_LT, EXP_EQ_0, ARITH_EQ])

  let BIT_LSB ← prove
   r"!x:N word. bit 0 x <=> ODD(val x)"
   (REWRITE_TAC [BIT_VAL, EXP, DIV_1])

  let TWICE_MSB ← prove
   r"2 EXP dimindex(:N) = 2 * 2 EXP (dimindex(:N) - 1) /\
   (&2:int) pow dimindex(:N) = &2 * &2 pow (dimindex(:N) - 1)"
   (REWRITE_TAC [← GSYM (← CONJUNCT2 EXP), ← GSYM (← CONJUNCT2 INT_POW)] THEN
    SIMP_TAC [DIMINDEX_GE_1, ← ARITH_RULE (← q r"1 <= n ==> SUC(n - 1) = n")])

  let MSB_VAL ← prove
   r"!w:N word. bit (dimindex(:N) - 1) w <=> 2 EXP (dimindex(:N) - 1) <= val w"
   (SIMP_TAC [BIT_VAL_MOD, SUB_ADD, DIMINDEX_GE_1, VAL_MOD_REFL])

  let MSB_INT_VAL ← prove
   r"!w:N word.
    bit (dimindex(:N) - 1) w <=> (&2 pow (dimindex(:N) - 1)):int <= &(val w)"
   (REWRITE_TAC [INT_OF_NUM_POW, INT_OF_NUM_LE, MSB_VAL])

  let BITVAL_MSB ← prove
   r"!x:N word. bitval(bit (dimindex(:N)-1) x) =
              val x DIV 2 EXP (dimindex(:N)-1)"
   (GEN_TAC THEN REWRITE_TAC [MSB_VAL] THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC [bitval] THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC (← ARITH_RULE (← q r"n < 2 /\ ~(n = 0) ==> n = 1")), ALL_TAC] THEN
    ASM_SIMP_TAC [DIV_EQ_0, EXP_EQ_0, ARITH_EQ, RDIV_LT_EQ] THEN
    ASM_REWRITE_TAC [← GSYM NOT_LE] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN
    SIMP_TAC [← GSYM (← CONJUNCT2 EXP), NOT_LE] THEN
    SIMP_TAC [DIMINDEX_NONZERO, ← ARITH_RULE (← q r"~(n = 0) ==> SUC(n - 1) = n")] THEN
    REWRITE_TAC [VAL_BOUND])

  let BLOCK_BITS_ZERO_ALT ← prove
   r"!(x:N word) m n.
        (!i. m <= i /\ i < n ==> ~bit i x) <=>
        (val x MOD 2 EXP n) DIV 2 EXP m = 0"
   (SIMP_TAC [val_def, BINARY_DIGITSUM_DIV, BINARY_DIGITSUM_MOD,
              FINITE_NUMSEG_LT, FINITE_RESTRICT, NSUM_EQ_0_IFF] THEN
    REWRITE_TAC [MULT_EQ_0, EXP_EQ_0, ARITH_EQ, BITVAL_EQ_0, IN_ELIM_THM] THEN
    MESON_TAC [NOT_LT, BIT_TRIVIAL])

  let BLOCK_BITS_ZERO ← prove
   r"!(x:N word) m n.
        (!i. m <= i /\ i < n ==> ~bit i x) <=>
        val x MOD 2 EXP n < 2 EXP m"
   (SIMP_TAC [BLOCK_BITS_ZERO_ALT, DIV_EQ_0, EXP_EQ_0, ARITH_EQ])

  let LOWER_BITS_ZERO ← prove
   r"!(x:N word) n. (!i. i < n ==> ~bit i x) <=> val x MOD 2 EXP n = 0"
   (ONCE_REWRITE_TAC [← ARITH_RULE (← q r"i < n <=> 0 <= i /\ i < n")] THEN
    REWRITE_TAC [BLOCK_BITS_ZERO_ALT, EXP, DIV_1])

  let UPPER_BITS_ZERO ← prove
   r"!(x:N word) n. (!i. n <= i ==> ~bit i x) <=> val x < 2 EXP n"
   (REPEAT GEN_TAC THEN MP_TAC (← ISPECL
     [← q "x:N word", ← q "n:num", ← q "dimindex(:N)"] BLOCK_BITS_ZERO) THEN
    REWRITE_TAC [VAL_MOD_REFL] THEN MESON_TAC [NOT_LT, BIT_TRIVIAL])

  let UPPER_BITS_ZERO_ALT ← prove
   r"!(x:N word) n. (!i. n <= i ==> ~bit i x) <=> val x DIV 2 EXP n = 0"
   (SIMP_TAC [UPPER_BITS_ZERO, DIV_EQ_0, EXP_EQ_0, ARITH_EQ])

  let VAL_WORD_OF_BITS ← prove
   r"!s. val(word_of_bits s:N word) =
       nsum {i | i < dimindex(:N) /\ i IN s} (\i. 2 EXP i)"
   (GEN_TAC THEN SIMP_TAC [val_def, BIT_WORD_OF_BITS, bitval] THEN
    REWRITE_TAC [COND_RAND, MULT_CLAUSES, ← GSYM NSUM_RESTRICT_SET] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC [])

  let WORD_OF_BITS_AS_WORD ← prove
   r"!s. word_of_bits s:N word =
       word(nsum {i | i < dimindex(:N) /\ i IN s} (\i. 2 EXP i))"
   (GEN_TAC THEN REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_OF_BITS, VAL_WORD] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC [← GSYM VAL_WORD_OF_BITS, VAL_BOUND])

  -- Two printing NUMBER_RULEs; the later one is evaluated first.
  let nrB ← NUMBER_RULE (← q r"(0 == n) (mod p) <=> p divides n")
  let nrA ← NUMBER_RULE (← q r"(n:num == n) (mod p)")
  let WORD_OF_BITS_AS_WORD_FINITE ← prove
   r"!s. FINITE s ==> word_of_bits s:N word = word(nsum s (\i. 2 EXP i))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [WORD_EQ, WORD_OF_BITS_AS_WORD] THEN
    ONCE_REWRITE_TAC [CONJ_SYM] THEN REWRITE_TAC [NSUM_RESTRICT_SET] THEN
    MATCH_MP_TAC CONG_NSUM THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q "i:num") THEN DISCH_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC [nrA] THEN
    REWRITE_TAC [nrB] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [NOT_LT]) THEN
    SIMP_TAC [LE_EXISTS, EXP_ADD, LEFT_IMP_EXISTS_THM] THEN
    REPEAT STRIP_TAC THEN CONV_TAC (fun t => (NUMBER_RULE t).run))

  let WORD_OF_BITS_SING_AS_WORD ← prove
   r"!i. word_of_bits {i}:N word = word(2 EXP i)"
   (SIMP_TAC [WORD_OF_BITS_AS_WORD_FINITE, FINITE_SING, NSUM_SING])

  let VAL_WORD_OF_BITS_SING ← prove
   r"!i. val(word_of_bits {i}:N word) = if i < dimindex(:N) then 2 EXP i else 0"
   (GEN_TAC THEN SIMP_TAC [val_def, BIT_WORD_OF_BITS, IN_SING, bitval] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [COND_RAND] THEN
    SIMP_TAC [MULT_CLAUSES, NSUM_DELTA, IN_ELIM_THM])

  let WORD_OF_BITS_MASK ← prove
   r"!n. word_of_bits {i | i < n}:N word = word(2 EXP n - 1)"
   (GEN_TAC THEN SIMP_TAC [WORD_OF_BITS_AS_WORD_FINITE, FINITE_NUMSEG_LT] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC (← ARITH_RULE (← q r"n + 1 = m ==> n = m - 1")) THEN
    SPEC_TAC (← q "n:num", ← q "n:num") THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC [NSUM_CLAUSES_NUMSEG_LT, EXP] THEN
    ASM_ARITH_TAC)

  let BIT_MASK_WORD ← prove
   r"!k i. bit i (word(2 EXP k - 1):N word) <=> i < dimindex(:N) /\ i < k"
   (REWRITE_TAC [← GSYM WORD_OF_BITS_MASK, IN_ELIM_THM, BIT_WORD_OF_BITS])

  let BIT_WORD_POW2 ← prove
   r"!k i. bit i (word (2 EXP k):N word) <=> i = k /\ k < dimindex(:N)"
   (REWRITE_TAC [← GSYM WORD_OF_BITS_SING_AS_WORD, BIT_WORD_OF_BITS] THEN
    SET_TAC [])

  let BIT_WORD_1 ← prove
   r"!i. bit i (word 1:N word) <=> i = 0"
   (GEN_TAC THEN REWRITE_TAC [← ARITH_RULE (← q r"1 = 2 EXP 0")] THEN
    SIMP_TAC [BIT_WORD_POW2, LE_1, DIMINDEX_GE_1])

  let BIT_WORD_BITVAL ← prove
   r"!b i. bit i (word(bitval b):N word) <=> i = 0 /\ b"
   (REPEAT GEN_TAC THEN REWRITE_TAC [bitval] THEN
    COND_CASES_TAC THEN REWRITE_TAC [BIT_WORD_0, BIT_WORD_1])

  let WORD_OF_BITS_SING_AS_WORD_1 ← prove
   r"word_of_bits {0}:N word = word 1"
   (REWRITE_TAC [WORD_OF_BITS_SING_AS_WORD, EXP])

  let BITS_OF_WORD_1 ← prove
   r"bits_of_word (word 1:N word) = {0}"
   (REWRITE_TAC [bits_of_word, BIT_WORD_1] THEN SET_TAC [])

  let BIT_WORD_OF_BITS_SING ← prove
   r"!k i. bit i (word_of_bits {k}:N word) <=> k < dimindex(:N) /\ i = k"
   (REWRITE_TAC [BIT_WORD_OF_BITS, IN_SING] THEN MESON_TAC [])

  let VAL_MOD ← prove
   r"!(x:N word) k.
        val x MOD 2 EXP k = nsum {i | i < k} (\i. 2 EXP i * bitval(bit i x))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [val_def] THEN
    SIMP_TAC [BINARY_DIGITSUM_MOD, FINITE_NUMSEG_LT] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_SUPERSET THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM, IMP_CONJ, MULT_EQ_0, BITVAL_EQ_0, NOT_LT] THEN
    MESON_TAC [BIT_TRIVIAL])

  let VAL_MOD_2 ← prove
   r"!x:N word. val x MOD 2 = bitval(bit 0 x)"
   (ONCE_REWRITE_TAC [← ARITH_RULE (← q r"2 = 2 EXP 1")] THEN
    REWRITE_TAC [VAL_MOD, ← ARITH_RULE (← q r"i < 1 <=> i = 0"), SING_GSPEC] THEN
    REWRITE_TAC [NSUM_SING, EXP, MULT_CLAUSES])

  let VAL_MOD_STEP ← prove
   r"!(x:N word) k.
      val x MOD 2 EXP (k + 1) = 2 EXP k * bitval(bit k x) + val x MOD 2 EXP k"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [VAL_MOD, ← ARITH_RULE (← q r"i < k + 1 <=> i = k \/ i < k")] THEN
    REWRITE_TAC [← SET_RULE (← q r"{x | x = a \/ P x} = a INSERT {x | P x}")] THEN
    SIMP_TAC [NSUM_CLAUSES, FINITE_NUMSEG_LT, IN_ELIM_THM, LT_REFL])

  let VAL_DIV ← prove
   r"!(x:N word) k.
        val x DIV 2 EXP k =
        nsum {i | k <= i /\ i < dimindex(:N)}
             (\i. 2 EXP (i - k) * bitval(bit i x))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [val_def] THEN
    SIMP_TAC [BINARY_DIGITSUM_DIV, FINITE_NUMSEG_LT] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN REWRITE_TAC [CONJ_SYM])

  let VAL_DIV_ALT ← prove
   r"!(x:N word) k.
        val x DIV 2 EXP k =
        nsum {i | i < dimindex(:N) - k}
             (\i. 2 EXP i * bitval(bit (i + k) x))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [VAL_DIV] THEN
    MATCH_MP_TAC NSUM_EQ_GENERAL_INVERSES THEN
    EXISTS_TAC (← q r"\i:num. i - k") THEN
    EXISTS_TAC (← q r"\i:num. i + k") THEN
    SIMP_TAC [IN_ELIM_THM, SUB_ADD] THEN ARITH_TAC)

  let VAL_LE_BITS ← prove
   r"!(x:N word) (y:N word).
        (!i. i < dimindex(:N) /\ bit i x ==> bit i y)
        ==> val x <= val y"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [val_def] THEN
    MATCH_MP_TAC NSUM_LE THEN REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN
    ASM_SIMP_TAC [LE_MULT_LCANCEL, LE_BITVAL])

  let VAL_LE_SUBSET ← prove
   r"!(x:N word) (y:N word).
        bits_of_word x SUBSET bits_of_word y ==> val x <= val y"
   (REWRITE_TAC [BITS_OF_WORD_SUBSET_ALT, VAL_LE_BITS])

  return { val_def, VAL, word, BIT_WORD, BIT_LSB_WORD, BIT_WORD_0, BITS_OF_WORD_0,
           BITS_OF_WORD_EQ_EMPTY, WORD_OF_BITS_EMPTY, BITVAL_BIT_WORD, WORD_VAL,
           VAL_WORD, MOD_VAL_WORD, DIVIDES_VAL_WORD, VAL_WORD_LE, VAL_WORD_LT,
           FORALL_WORD, EXISTS_WORD, VAL_WORD_0, VAL_WORD_1, WORD_BITVAL,
           VAL_WORD_BITVAL, VAL_WORD_EQ, VAL_EQ, VAL_EQ_0, VAL_EQ_1, VAL_EQ_BITVAL,
           WORD_BITVAL_EQ_0, WORD_BITVAL_EQ_1, WORD_NE_10, WORD_EQ, WORD_EQ_IMP,
           WORD_EQ_0, VAL_BOUND, INT_VAL_BOUND, VAL_MOD_REFL, VAL_WORD_EQ_EQ,
           FORALL_VAL_GEN, FORALL_VAL, VAL_CONG, WORD_MOD_SIZE, VAL_WORD_CONG,
           VAL_WORD_GALOIS, WORD_VAL_GALOIS, DIVIDES_VAL_WORD_EQ, BIT_VAL, BIT_VAL_MOD,
           BIT_LSB, TWICE_MSB, MSB_VAL, MSB_INT_VAL, BITVAL_MSB, BLOCK_BITS_ZERO_ALT,
           BLOCK_BITS_ZERO, LOWER_BITS_ZERO, UPPER_BITS_ZERO, UPPER_BITS_ZERO_ALT,
           VAL_WORD_OF_BITS, WORD_OF_BITS_AS_WORD, WORD_OF_BITS_AS_WORD_FINITE,
           WORD_OF_BITS_SING_AS_WORD, VAL_WORD_OF_BITS_SING, WORD_OF_BITS_MASK,
           BIT_MASK_WORD, BIT_WORD_POW2, BIT_WORD_1, BIT_WORD_BITVAL,
           WORD_OF_BITS_SING_AS_WORD_1, BITS_OF_WORD_1, BIT_WORD_OF_BITS_SING, VAL_MOD,
           VAL_MOD_2, VAL_MOD_STEP, VAL_DIV, VAL_DIV_ALT, VAL_LE_BITS, VAL_LE_SUBSET }

/- ------------------------------------------------------------------------- -/
/- Corresponding signed 2s-complement mappings to and from integers.         -/
/- ------------------------------------------------------------------------- -/

structure Ival where
  ival : thm
  iword : thm
  word_sgn : thm
  INT_IVAL : thm
  WORD_IWORD : thm
  IVAL_VAL : thm
  VAL_IVAL : thm
  IVAL_EQ_VAL : thm
  INT_VAL_IWORD : thm
  INT_VAL_IWORD_EQ : thm
  MSB_IVAL : thm
  IVAL_BOUND : thm
  IVAL_WORD_0 : thm
  IVAL_WORD_1 : thm
  IVAL_VAL_CONG : thm
  IVAL_CONG : thm
  IVAL_EQ : thm
  IVAL_EQ_0 : thm
  IVAL_EQ_1 : thm
  IWORD_EQ : thm
  IWORD_REM_SIZE : thm
  IVAL_IWORD_CONG : thm
  VAL_IWORD_CONG : thm
  IVAL_WORD_CONG : thm
  IVAL_IWORD : thm
  IWORD_IVAL : thm
  IVAL_IWORD_GALOIS : thm
  BIT_IVAL : thm
  BIT_IWORD : thm
  INT_REM_IVAL : thm
  VAL_IVAL_REM : thm
  INT_REM_IVAL_IWORD : thm
  INT_DIVIDES_IVAL_IWORD : thm
  FORALL_IVAL_GEN : thm
  FORALL_IVAL : thm
  FORALL_IWORD : thm
  EXISTS_IWORD : thm
  IVAL_REM_2 : thm
  BIT_LSB_IWORD : thm
  TWOS_COMPLEMENT_GEN : thm
  TWOS_COMPLEMENT : thm
  deriving Inhabited

@[nospecialize]
def setupIval [HolBase] (D : WordsDeps) (V : Bitval) (Vl : Val) :
    ExceptT String IO Ival := do
  let { new_definition, ARITH_RULE, ASM_INT_ARITH_TAC, INTEGER_RULE, INT_ARITH,
        INT_ARITH_TAC, MESON, MESON_TAC, NUMBER_RULE, NUM_REDUCE_CONV,
        INT_REDUCE_CONV, .. } := D
  let { ARITH, ARITH_EQ, CONG, COND_ID, COND_SWAP, DIMINDEX_GE_1, DIMINDEX_NONZERO,
        DIV_EQ_0, EQ_TRANS, EVEN_EXISTS, EVEN_EXP, EXP_EQ_0, EXP_LT_0, .. } := D.core1
  let { IMP_CONJ, INT_ABS_NUM, INT_ABS_POW, INT_ADD_RID, INT_CONG_DIV2,
        INT_CONG_IMP_EQ, INT_DIVISION, INT_DIV_EQ_0, INT_DIV_MUL_ADD, INT_EQ_SUB_RADD,
        INT_FORALL_POS, INT_MUL_RID, INT_MUL_RZERO, INT_MUL_SYM, INT_NOT_LT,
        INT_OF_NUM_CLAUSES, INT_OF_NUM_DIV, INT_OF_NUM_EQ, INT_OF_NUM_LE,
        INT_OF_NUM_LT, INT_OF_NUM_OF_INT, INT_OF_NUM_POW, INT_OF_NUM_REM,
        INT_OF_NUM_SUB, INT_POS, INT_POW, INT_POW_ADD, INT_POW_EQ_0, INT_POW_LE,
        INT_POW_MONO, INT_REM_EQ, INT_REM_EQ_0, INT_REM_MOD_SELF, INT_REM_REM,
        INT_REM_REM_POW_MIN, INT_REM_UNIQUE, .. } := D.core2
  let { LEFT_IMP_EXISTS_THM, LE_0, LE_1, LE_ADD, LE_EXISTS, LE_EXP, LTE_TRANS,
        LT_EXISTS, MOD_MOD_REFL, MULT_CLAUSES, NOT_EVEN, NOT_LE, NOT_LT,
        NUM_OF_INT_OF_NUM, ODD, .. } := D.core3
  let { SUB_ADD, SUC_SUB1, divides, num_CASES, num_congruent, num_divides,
        .. } := D.core4
  let { bitval, BITVAL_EQ_0, BITVAL_EQ_1, .. } := V
  let { BIT_VAL, MSB_VAL, VAL_BOUND, VAL_CONG, VAL_MOD_2, VAL_WORD, VAL_WORD_0,
        VAL_WORD_1, VAL_WORD_CONG, VAL_WORD_EQ, WORD_EQ, .. } := Vl

  let ival ← new_definition
   r"(ival:N word->int) w =
    if val(w) < 2 EXP (dimindex(:N) - 1) then &(val w)
    else &(val w) - &2 pow dimindex(:N)"

  let iword ← new_definition
   r"(iword:int->N word) x = word(num_of_int(x rem (&2 pow dimindex(:N))))"

  let word_sgn ← new_definition
   r"word_sgn (x:N word) = int_sgn(ival x)"

  let INT_IVAL ← prove
   r"!w:N word.
        ival w =
        if &(val w):int < &2 pow (dimindex(:N) - 1) then &(val w)
        else &(val w) - &2 pow dimindex(:N)"
   (REWRITE_TAC [ival, INT_OF_NUM_POW, INT_OF_NUM_LT])

  let WORD_IWORD ← prove
   r"!n. word n:N word = iword(&n)"
   (GEN_TAC THEN REWRITE_TAC [iword, WORD_EQ] THEN
    REWRITE_TAC [INT_OF_NUM_POW, INT_OF_NUM_REM, NUM_OF_INT_OF_NUM] THEN
    REWRITE_TAC [CONG, MOD_MOD_REFL])

  let IVAL_VAL ← prove
   r"!w:N word.
    ival w =
    &(val w) - &2 pow dimindex(:N) * &(bitval(bit (dimindex(:N) - 1) w))"
   (GEN_TAC THEN REWRITE_TAC [ival, ← GSYM NOT_LE, ← GSYM MSB_VAL, COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [bitval] THEN INT_ARITH_TAC)

  let VAL_IVAL ← prove
   r"!w:N word.
    &(val w) =
    ival w + &2 pow dimindex(:N) * &(bitval (bit (dimindex (:N) - 1) w))"
   (REWRITE_TAC [IVAL_VAL] THEN CONV_TAC (fun t => (INT_ARITH t).run))

  let IVAL_EQ_VAL ← prove
   r"!x:N word. val(x) < 2 EXP (dimindex(:N)-1) ==> ival x = &(val x)"
   (SIMP_TAC [ival])

  let INT_VAL_IWORD ← prove
   r"!x. &0 <= x /\ x < &2 pow dimindex(:N) ==> &(val(iword x:N word)) = x"
   (SIMP_TAC [IMP_CONJ, ← GSYM INT_FORALL_POS] THEN
    REWRITE_TAC [← GSYM WORD_IWORD, INT_OF_NUM_CLAUSES, VAL_WORD_EQ])

  let INT_VAL_IWORD_EQ ← prove
   r"!x. &(val(iword x:N word)) = x <=>
       &0 <= x /\ x < &2 pow dimindex(:N)"
   (GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [INT_VAL_IWORD] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [INT_OF_NUM_CLAUSES, LE_0, VAL_BOUND])

  let MSB_IVAL ← prove
   r"!(w:N word).
        bit (dimindex(:N) - 1) w <=> ival w < &0"
   (GEN_TAC THEN REWRITE_TAC [ival, MSB_VAL] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [← GSYM NOT_LT] THEN
    REWRITE_TAC [INT_NOT_LT, INT_OF_NUM_LE, LE_0] THEN
    REWRITE_TAC [← INT_ARITH (← q r"a - b:int < &0 <=> a < b")] THEN
    REWRITE_TAC [INT_OF_NUM_LT, INT_OF_NUM_POW, VAL_BOUND])

  let IVAL_BOUND ← prove
   r"!w:(N)word.
        --(&2 pow (dimindex(:N) - 1)) <= ival w /\
        ival w < &2 pow (dimindex(:N) - 1)"
   (GEN_TAC THEN MP_TAC (← ISPEC (← q "w:N word") VAL_BOUND) THEN
    REWRITE_TAC [ival, ← GSYM INT_OF_NUM_LT, ← GSYM INT_OF_NUM_POW] THEN
    SUBGOAL_THEN (← q r"?n. dimindex(:N) = SUC n") (CHOOSE_THEN SUBST1_TAC) THENL
     [MESON_TAC [DIMINDEX_NONZERO, num_CASES], ALL_TAC] THEN
    REWRITE_TAC [SUC_SUB1, INT_POW] THEN INT_ARITH_TAC)

  let IVAL_WORD_0 ← prove
   r"ival(word 0) = &0"
   (REWRITE_TAC [ival, VAL_WORD_0, EXP_LT_0] THEN CONV_TAC NUM_REDUCE_CONV)

  let IVAL_WORD_1 ← prove
   r"ival(word 1:N word) = if dimindex(:N) = 1 then -- &1 else &1"
   (REWRITE_TAC [ival, VAL_WORD_1] THEN
    ONCE_REWRITE_TAC [← ARITH_RULE (← q r"1 < x <=> 2 EXP 1 <= x")] THEN
    REWRITE_TAC [LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC [DIMINDEX_NONZERO, ← ARITH_RULE
     (← q r"1 <= n - 1 <=> ~(n = 0 \/ n = 1)")] THEN
    ASM_CASES_TAC (← q "dimindex(:N) = 1") THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC INT_REDUCE_CONV)

  let IVAL_VAL_CONG ← prove
   r"!(w:N word). (ival w == &(val w)) (mod (&2 pow (dimindex(:N))))"
   (GEN_TAC THEN REWRITE_TAC [ival] THEN COND_CASES_TAC THEN
    CONV_TAC (fun t => (INTEGER_RULE t).run))

  let IVAL_CONG ← prove
   r"!(v:N word) (w:N word).
      (ival v == ival w) (mod (&2 pow (dimindex(:N)))) <=> v = w"
   (REWRITE_TAC [← GSYM VAL_CONG, num_congruent, ← GSYM INT_OF_NUM_POW] THEN
    REPEAT GEN_TAC THEN MATCH_MP_TAC (← INTEGER_RULE
     (← q r"(x:int == x') (mod n) /\ (y == y') (mod n)
    ==> ((x == y) (mod n) <=> (x' == y') (mod n))")) THEN
    REWRITE_TAC [IVAL_VAL_CONG])

  let IVAL_EQ ← prove
   r"!(v:N word) (w:N word). ival v = ival w <=> v = w"
   (MESON_TAC [← NUMBER_RULE (← q r"(x:int == x) (mod n)"), IVAL_CONG])

  let IVAL_EQ_0 ← prove
   r"!(w:N word). ival w = &0 <=> w = word 0"
   (REWRITE_TAC [← GSYM IVAL_EQ, IVAL_WORD_0])

  let IVAL_EQ_1 ← prove
   r"!w:N word. ival w = &1 <=> 2 <= dimindex(:N) /\ w = word 1"
   (GEN_TAC THEN REWRITE_TAC [← GSYM IVAL_EQ, IVAL_WORD_1] THEN
    SIMP_TAC [DIMINDEX_GE_1, ← ARITH_RULE (← q r"1 <= n ==> (2 <= n <=> ~(n = 1))")] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MP_TAC (← SPEC (← q "w:N word") IVAL_BOUND) THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV)

  let IWORD_EQ ← prove
   r"!x y. iword x:N word = iword y <=> (x == y) (mod (&2 pow (dimindex(:N))))"
   (REWRITE_TAC [iword, WORD_EQ, num_congruent, ← GSYM INT_OF_NUM_POW] THEN
    SIMP_TAC [INT_OF_NUM_OF_INT, INT_DIVISION, INT_POW_EQ_0,
              INT_OF_NUM_EQ, ARITH_EQ] THEN
    REWRITE_TAC [← GSYM INT_REM_EQ, INT_REM_REM])

  let IWORD_REM_SIZE ← prove
   r"!n. iword(n rem (&2 pow dimindex(:N))):N word = iword n"
   (REWRITE_TAC [IWORD_EQ, INT_REM_MOD_SELF])

  -- Two printing INTEGER_RULEs; the later one is evaluated first.
  let irB ← INTEGER_RULE
   (← q r"(&(val(word w:N word)):int == &w) (mod n) /\ (&w:int == z) (mod n)
    ==> (&(val(word w:N word)) == z) (mod n)")
  let irA ← INTEGER_RULE
   (← q r"(y:int == z) (mod n) ==> (x == y) (mod n) ==> (x == z) (mod n)")
  let IVAL_IWORD_CONG ← prove
   r"!x. (ival(iword x:N word) == x) (mod (&2 pow (dimindex(:N))))"
   (GEN_TAC THEN MP_TAC (← SPEC (← q "iword x:N word") IVAL_VAL_CONG) THEN
    MATCH_MP_TAC irA THEN
    REWRITE_TAC [iword] THEN MATCH_MP_TAC irB THEN
    CONJ_TAC THENL
     [REWRITE_TAC [INT_OF_NUM_POW, ← GSYM num_congruent] THEN
      REWRITE_TAC [VAL_WORD, CONG, MOD_MOD_REFL],
      SIMP_TAC [INT_OF_NUM_OF_INT, INT_DIVISION, INT_POW_EQ_0,
                INT_OF_NUM_EQ, ARITH_EQ] THEN
      REWRITE_TAC [← GSYM INT_REM_EQ, INT_REM_REM]])

  let VAL_IWORD_CONG ← prove
   r"!x. (&(val(iword x:N word)) == x) (mod (&2 pow dimindex(:N)))"
   (REWRITE_TAC [← GSYM INT_REM_EQ] THEN
    REWRITE_TAC [← GSYM (← REWRITE_RULE [← GSYM INT_REM_EQ] IVAL_VAL_CONG)] THEN
    REWRITE_TAC [INT_REM_EQ, IVAL_IWORD_CONG])

  let IVAL_WORD_CONG ← prove
   r"!n. (ival(word n:N word) == &n) (mod (&2 pow dimindex(:N)))"
   (MESON_TAC [IVAL_VAL_CONG, VAL_WORD_CONG, INT_OF_NUM_POW, num_congruent,
               ← INTEGER_RULE (← q r"(x:int == y) (mod n) /\ (y == z) (mod n)
                          ==> (x == z) (mod n)")])

  let IVAL_IWORD ← prove
   r"!n. --(&2 pow (dimindex (:N) - 1)) <= n /\ n < &2 pow (dimindex (:N) - 1)
       ==> ival(iword n:N word) = n"
   (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q "n:int") IVAL_IWORD_CONG) THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] INT_CONG_IMP_EQ) THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← INT_ARITH
     (← q r"n:int < e1
    ==> --e1 <= n /\ --e1 <= n' /\ n' < e1 /\ &2 * e1 = e
        ==> abs(n' - n) < e"))) THEN
    ASM_REWRITE_TAC [IVAL_BOUND, ← GSYM (← CONJUNCT2 INT_POW)] THEN
    SIMP_TAC [DIMINDEX_GE_1, ← ARITH_RULE (← q r"1 <= n ==> SUC(n - 1) = n")])

  let IWORD_IVAL ← prove
   r"!w:N word. iword(ival w) = w"
   (REWRITE_TAC [← GSYM IVAL_CONG, IVAL_IWORD_CONG])

  let IVAL_IWORD_GALOIS ← prove
   r"!(w:N word) n.
        ival w = n <=>
        --(&2 pow (dimindex(:N) - 1)) <= n /\
        n < &2 pow (dimindex(:N) - 1) /\
        w = iword n"
   (MESON_TAC [IVAL_IWORD, IWORD_IVAL, IVAL_BOUND])

  -- OCaml order: the second THENL branch's MESON, then the first branch's
  -- INTEGER_RULEs, the later one first.
  let mesonO ← MESON [ODD] (← q r"n = 0 ==> ~ODD n")
  let irD ← INTEGER_RULE
   (← q r"!m. (x:int == y) (mod m) /\ n divides m ==> (y == x) (mod n)")
  let irC ← INTEGER_RULE
   (← q r"(x:int == y) (mod n) ==> (n divides x <=> n divides y)")
  let BIT_IVAL ← prove
   r"!(x:N word) i.
    bit i x <=> i < dimindex(:N) /\ ~(&2 divides (ival x div &2 pow i))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [BIT_VAL] THEN
    ASM_CASES_TAC (← q "i < dimindex(:N)") THEN ASM_REWRITE_TAC [] THENL
     [REWRITE_TAC [← GSYM NOT_EVEN, EVEN_EXISTS, ← GSYM divides] THEN
      AP_TERM_TAC THEN REWRITE_TAC [num_divides] THEN MATCH_MP_TAC irC THEN
      REWRITE_TAC [← GSYM INT_OF_NUM_DIV, ← GSYM INT_OF_NUM_POW] THEN
      MATCH_MP_TAC INT_CONG_DIV2 THEN SIMP_TAC [INT_POW_LE, INT_POS] THEN
      MATCH_MP_TAC irD THEN
      EXISTS_TAC (← q r"(&2:int) pow dimindex(:N)") THEN REWRITE_TAC [IVAL_VAL_CONG] THEN
      ONCE_REWRITE_TAC [INT_MUL_SYM] THEN
      REWRITE_TAC [← GSYM (← CONJUNCT2 INT_POW)] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [LT_EXISTS]) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [INT_POW_ADD, INT_POW] THEN
      CONV_TAC (fun t => (INTEGER_RULE t).run),
      RULE_ASSUM_TAC (REWRITE_RULE [NOT_LT]) THEN
      MATCH_MP_TAC mesonO THEN
      SIMP_TAC [DIV_EQ_0, ARITH_EQ, EXP_EQ_0] THEN
      TRANS_TAC LTE_TRANS (← q "2 EXP dimindex(:N)") THEN
      ASM_REWRITE_TAC [VAL_BOUND, LE_EXP, DIMINDEX_NONZERO, COND_ID]])

  let irF ← INTEGER_RULE
   (← q r"!m. (x:int == y) (mod m) /\ n divides m ==> (x == y) (mod n)")
  let irE ← INTEGER_RULE
   (← q r"(x:int == y) (mod n) ==> (n divides x <=> n divides y)")
  let BIT_IWORD ← prove
   r"!i x. bit i (iword x:N word) <=>
         i < dimindex(:N) /\ ~(&2 divides (x div (&2 pow i)))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [BIT_IVAL] THEN
    ASM_CASES_TAC (← q "i < dimindex(:N)") THEN ASM_REWRITE_TAC [] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC irE THEN
    MATCH_MP_TAC INT_CONG_DIV2 THEN SIMP_TAC [INT_POW_LE, INT_POS] THEN
    MATCH_MP_TAC irF THEN
    EXISTS_TAC (← q r"(&2:int) pow dimindex(:N)") THEN
    REWRITE_TAC [IVAL_IWORD_CONG] THEN
      ONCE_REWRITE_TAC [INT_MUL_SYM] THEN
      REWRITE_TAC [← GSYM (← CONJUNCT2 INT_POW)] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [LT_EXISTS]) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [INT_POW_ADD, INT_POW] THEN
      CONV_TAC (fun t => (INTEGER_RULE t).run))

  let INT_REM_IVAL ← prove
   r"!(w:N word) k.
        k <= dimindex(:N) ==> (ival w) rem (&2 pow k) = &(val w MOD 2 EXP k)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM INT_OF_NUM_REM] THEN
    REWRITE_TAC [← GSYM INT_OF_NUM_POW, INT_REM_EQ] THEN
    MATCH_MP_TAC (← INTEGER_RULE
     (← q r"!n:int. (x == y) (mod n) /\ m divides n ==> (x == y) (mod m)")) THEN
    EXISTS_TAC (← q r"(&2:int) pow dimindex(:N)") THEN REWRITE_TAC [IVAL_VAL_CONG] THEN
    POP_ASSUM MP_TAC THEN
    SIMP_TAC [LE_EXISTS, INT_POW_ADD, LEFT_IMP_EXISTS_THM] THEN
    REPEAT STRIP_TAC THEN CONV_TAC (fun t => (INTEGER_RULE t).run))

  let VAL_IVAL_REM ← prove
   r"!x:N word. &(val x) = ival x rem &2 pow dimindex(:N)"
   (GEN_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC [INT_REM_UNIQUE] THEN
    REWRITE_TAC [INT_ABS_POW, INT_ABS_NUM, INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC [LE_0, VAL_BOUND] THEN
    REWRITE_TAC [← GSYM INT_OF_NUM_CLAUSES, IVAL_VAL_CONG])

  let INT_REM_IVAL_IWORD ← prove
   r"!x k. k <= dimindex(:N)
         ==> ival(iword x:N word) rem &2 pow k = x rem &2 pow k"
   (REPEAT STRIP_TAC THEN
    TRANS_TAC EQ_TRANS (← q r"x rem &2 pow dimindex(:N) rem &2 pow k") THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC [← GSYM (← REWRITE_RULE [← GSYM INT_REM_EQ] IVAL_IWORD_CONG)],
      ALL_TAC] THEN
    ASM_SIMP_TAC [INT_REM_REM_POW_MIN, ← ARITH_RULE (← q r"k <= n ==> MIN n k = k")])

  let INT_DIVIDES_IVAL_IWORD ← prove
   r"!n x. n <= dimindex(:N)
         ==> (&2 pow n divides ival(iword x:N word) <=> &2 pow n divides x)"
   (SIMP_TAC [INT_REM_IVAL_IWORD, ← GSYM INT_REM_EQ_0])

  let FORALL_IVAL_GEN ← prove
   r"!P. (!x:N word. P (ival x) x) <=>
       (!n. --(&2 pow (dimindex (:N) - 1)) <= n /\
            n < &2 pow (dimindex (:N) - 1)
            ==> P n (iword n))"
   (MESON_TAC [IVAL_IWORD, IWORD_IVAL, IVAL_BOUND])

  let FORALL_IVAL ← prove
   r"!P. (!x:N word. P(ival x)) <=>
       (!n. --(&2 pow (dimindex (:N) - 1)) <= n /\
            n < &2 pow (dimindex (:N) - 1)
            ==> P n)"
   (REWRITE_TAC [FORALL_IVAL_GEN])

  let FORALL_IWORD ← prove
   r"!P. (!x:N word. P x) <=> (!n. P(iword n))"
   (MESON_TAC [IWORD_IVAL])

  let EXISTS_IWORD ← prove
   r"!P. (?x:N word. P x) <=> (?n. P(iword n))"
   (MESON_TAC [IWORD_IVAL])

  let IVAL_REM_2 ← prove
   r"!x:N word. ival(x) rem &2 = &(bitval(bit 0 x))"
   (GEN_TAC THEN REWRITE_TAC [← GSYM VAL_MOD_2, ← GSYM INT_OF_NUM_REM] THEN
    REWRITE_TAC [INT_REM_EQ] THEN MATCH_MP_TAC (← INTEGER_RULE
     (← q r"!m:int. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)")) THEN
    EXISTS_TAC (← q r"(&2:int) pow dimindex(:N)") THEN REWRITE_TAC [IVAL_VAL_CONG] THEN
    REWRITE_TAC [INT_OF_NUM_CLAUSES, ← GSYM num_divides] THEN
    REWRITE_TAC [divides, ← GSYM EVEN_EXISTS] THEN
    REWRITE_TAC [EVEN_EXP, ARITH, DIMINDEX_NONZERO])

  let BIT_LSB_IWORD ← prove
   r"!x. bit 0 (iword x:N word) = x rem &2 = &1"
   (GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM BITVAL_EQ_1] THEN
    REWRITE_TAC [← GSYM INT_OF_NUM_EQ, ← GSYM IVAL_REM_2] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [INT_REM_EQ] THEN
    MATCH_MP_TAC (← INTEGER_RULE
     (← q r"!m:int. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)")) THEN
    EXISTS_TAC (← q r"(&2:int) pow dimindex(:N)") THEN REWRITE_TAC [IVAL_IWORD_CONG] THEN
    REWRITE_TAC [INT_OF_NUM_CLAUSES, ← GSYM num_divides] THEN
    REWRITE_TAC [divides, ← GSYM EVEN_EXISTS] THEN
    REWRITE_TAC [EVEN_EXP, ARITH, DIMINDEX_NONZERO])

  let TWOS_COMPLEMENT_GEN ← prove
   r"!p k n x:int.
        (&n == x) (mod (&2 pow (p + k))) /\
        n < 2 EXP (p + k) /\ --(&2 pow p) <= x /\ x < &2 pow p
        ==> n DIV 2 EXP p = (2 EXP k - 1) * bitval(x < &0) /\
            &n - &2 pow (p + k) * &(bitval(x < &0)) = x"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [bitval] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC [INT_MUL_RZERO, INT_MUL_RID, INT_EQ_SUB_RADD,
                     ← GSYM INT_OF_NUM_CLAUSES, ← GSYM INT_OF_NUM_DIV] THEN
    SIMP_TAC [← GSYM INT_OF_NUM_SUB, LE_1, EXP_EQ_0, ARITH_EQ,
              ← GSYM INT_OF_NUM_POW, INT_ADD_RID] THEN
    MATCH_MP_TAC (← TAUT (← q r"q /\ (q ==> p) ==> p /\ q")) THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC (← q r"(&2:int) pow (p + k)") THEN
       ASM_REWRITE_TAC [← INTEGER_RULE
        (← q r"(n:int == x + p) (mod p) <=> (n == x) (mod p)")] THEN
       MATCH_MP_TAC (← INT_ARITH
        (← q r"&0 <= x /\ x < p /\ &0 <= y /\ y < p
          ==> abs(x - y:int) < p")) THEN
       ASM_REWRITE_TAC [INT_OF_NUM_CLAUSES, LE_0] THEN
       MP_TAC (← SPECL [← q "p:num", ← q "p + k:num", ← q "&2:int"] INT_POW_MONO) THEN
       CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC [LE_ADD] THEN
       REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [← GSYM INT_OF_NUM_CLAUSES] THEN
       INT_ARITH_TAC,
       DISCH_THEN SUBST1_TAC])
    THENL [ALL_TAC, REWRITE_TAC [INT_DIV_EQ_0] THEN ASM_INT_ARITH_TAC] THEN
    SIMP_TAC [INT_POW_ADD, INT_DIV_MUL_ADD, INT_POW_EQ_0, INT_OF_NUM_EQ, ARITH_EQ,
              ← INT_ARITH (← q r"x + k:int = k - &1 <=> x + &1 = &0")] THEN
    TRANS_TAC EQ_TRANS (← q r"(x + &1 * &2 pow p) div &2 pow p") THEN CONJ_TAC THENL
     [SIMP_TAC [INT_POW_ADD, INT_DIV_MUL_ADD, INT_POW_EQ_0, INT_OF_NUM_EQ,
                ARITH_EQ],
      REWRITE_TAC [INT_DIV_EQ_0] THEN ASM_INT_ARITH_TAC])

  let TWOS_COMPLEMENT ← prove
   r"!p n x:int.
        (&n == x) (mod (&2 pow p)) /\
        ~(p = 0) /\ n < 2 EXP p /\
        --(&2 pow (p - 1)) <= x /\ x < &2 pow (p - 1)
        ==> (2 EXP (p - 1) <= n <=> x < &0) /\
            n DIV (2 EXP (p - 1)) = bitval(x < &0) /\
            &n - &2 pow p * &(bitval(x < &0)) = x"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← SPECL [← q "p - 1", ← q "1", ← q "n:num", ← q "x:int"] TWOS_COMPLEMENT_GEN) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC [LE_1, SUB_ADD, MULT_CLAUSES] THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"\x. x = 0") o CONJUNCT1) THEN
    SIMP_TAC [DIV_EQ_0, EXP_EQ_0, ARITH_EQ, BITVAL_EQ_0] THEN
    REWRITE_TAC [← GSYM NOT_LT] THEN CONV_TAC (fun t => (TAUT t).run))

  return { ival, iword, word_sgn, INT_IVAL, WORD_IWORD, IVAL_VAL, VAL_IVAL,
           IVAL_EQ_VAL, INT_VAL_IWORD, INT_VAL_IWORD_EQ, MSB_IVAL, IVAL_BOUND,
           IVAL_WORD_0, IVAL_WORD_1, IVAL_VAL_CONG, IVAL_CONG, IVAL_EQ, IVAL_EQ_0,
           IVAL_EQ_1, IWORD_EQ, IWORD_REM_SIZE, IVAL_IWORD_CONG, VAL_IWORD_CONG,
           IVAL_WORD_CONG, IVAL_IWORD, IWORD_IVAL, IVAL_IWORD_GALOIS, BIT_IVAL,
           BIT_IWORD, INT_REM_IVAL, VAL_IVAL_REM, INT_REM_IVAL_IWORD,
           INT_DIVIDES_IVAL_IWORD, FORALL_IVAL_GEN, FORALL_IVAL, FORALL_IWORD,
           EXISTS_IWORD, IVAL_REM_2, BIT_LSB_IWORD, TWOS_COMPLEMENT_GEN,
           TWOS_COMPLEMENT }

/- ------------------------------------------------------------------------- -/
/- Bit operations on `num`.                                                  -/
/- ------------------------------------------------------------------------- -/

/-- The terms and proformas `BIT_PRED`/`NUMBIT_CONV` close over
    (words.ml 1338-1365). -/
structure NumbitCtx where
  i : term
  j : term
  n : term
  B0 : term
  B1 : term
  B00 : thm
  th_0 : thm
  th00 : thm
  th01 : thm
  thB1S : thm
  thB10 : thm
  thB11 : thm
  thSB1 : thm
  thB00 : thm
  thB01 : thm
  th0B00 : thm
  th0B01 : thm
  thN : thm
  deriving Inhabited

/-- `mk_pred` of words.ml 1367-1373, exported as `BIT_PRED`: for a raw
    numeral `i`, `(None, |- i = _0)` or `(Some j, |- i = SUC j)`. -/
partial def bitPred (K : NumbitCtx) : term → Except String (Option term × thm)
  | .Comb (.Const "BIT0" _) i' => do
    match ← bitPred K i' with
    | (some j', th) =>
      let th1 ← Equal.PROVE_HYP th (← HolCore.Kernel.INST [(i', K.i), (j', K.j)] K.thSB1)
      pure (some (← rand (← rhs (concl th1))), th1)
    | (none, th) => pure (none, ← HolCore.Kernel.TRANS (← Equal.AP_TERM K.B0 th) K.B00)
  | .Comb (.Const "BIT1" _) i' => do
    let th1 ← HolCore.Kernel.INST [(i', K.i)] K.thB1S
    pure (some (← rand (← rhs (concl th1))), th1)
  | i'@(.Const "_0" _) => pure (none, REFL i')
  | _ => .error "BIT_PRED"

mutual
/-- `go` of words.ml 1374-1388.  `TRANS (INST ..) (go ..)`: the arguments
    are evaluated right to left, `go` first. -/
partial def numbitGo (K : NumbitCtx) : term × term → Except String thm
  | (i', .Const "_0" _) => HolCore.Kernel.INST [(i', K.i)] K.th_0
  | (.Const "_0" _, .Comb (.Const "BIT0" _) n') => HolCore.Kernel.INST [(n', K.n)] K.th00
  | (.Const "_0" _, .Comb (.Const "BIT1" _) n') => HolCore.Kernel.INST [(n', K.n)] K.th01
  | (.Comb (.Const "BIT0" _) i', .Comb (.Const "BIT0" _) n') =>
    numbitGoB0 K K.th0B00 K.thB00 i' n'
  | (.Comb (.Const "BIT0" _) i', .Comb (.Const "BIT1" _) n') =>
    numbitGoB0 K K.th0B01 K.thB01 i' n'
  | (.Comb (.Const "BIT1" _) i', .Comb (.Const "BIT0" _) n') => do
    let r ← numbitGo K (← mk_comb K.B0 i', n')
    HolCore.Kernel.TRANS (← HolCore.Kernel.INST [(i', K.i), (n', K.n)] K.thB10) r
  | (.Comb (.Const "BIT1" _) i', .Comb (.Const "BIT1" _) n') => do
    let r ← numbitGo K (← mk_comb K.B0 i', n')
    HolCore.Kernel.TRANS (← HolCore.Kernel.INST [(i', K.i), (n', K.n)] K.thB11) r
  | _ => .error "NUMBIT_CONV"

/-- `go_B0` of words.ml 1389-1394. -/
partial def numbitGoB0 (K : NumbitCtx) (th0 thS : thm) (i' n' : term) : Except String thm := do
  match ← bitPred K i' with
  | (some j', th) =>
    let th' ← Equal.PROVE_HYP th
      (← HolCore.Kernel.INST [(i', K.i), (j', K.j), (n', K.n)] thS)
    HolCore.Kernel.TRANS th' (← numbitGo K (← mk_comb K.B1 j', n'))
  | (none, th) => Equal.PROVE_HYP th (← HolCore.Kernel.INST [(i', K.i), (n', K.n)] th0)
end

/-- `NUMBIT_CONV` (words.ml 1395-1399). -/
def numbitConv (K : NumbitCtx) : term → Except String thm
  | .Comb (.Comb (.Const "numbit" _) (.Comb (.Const "NUMERAL" _) i'))
          (.Comb (.Const "NUMERAL" _) n') => do
    let r ← numbitGo K (i', n')
    HolCore.Kernel.TRANS (← HolCore.Kernel.INST [(i', K.i), (n', K.n)] K.thN) r
  | .Comb (.Comb (.Const "numbit" _) i') n' => numbitGo K (i', n')
  | _ => .error "NUMBIT_CONV"

structure NumBits where
  numbit : thm
  NUMBIT_VAL : thm
  /-- The context of `BIT_PRED` and `NUMBIT_CONV`. -/
  numbitCtx : NumbitCtx
  bits_of_num : thm
  IN_BITS_OF_NUM : thm
  BITS_OF_NUM_SUBSET_NUMSEG_LT : thm
  FINITE_BITS_OF_NUM : thm
  NSUM_BITS_OF_NUM : thm
  BITS_OF_NUM_NSUM : thm
  BITS_OF_NUM_EQ : thm
  BITS_OF_NUM_GALOIS : thm
  NSUM_BITS_DIV : thm
  NSUM_BITS_MOD : thm
  NSUM_BITS_EQ : thm
  BITSUM_BOUND : thm
  BITS_OF_NUM_SUBSET_NUMSEG_EQ : thm
  BITSUM_DIVIDES : thm
  BITS_OF_NUM_DISJOINT_NUMSEG_EQ : thm
  BITS_OF_NUM_0 : thm
  BITS_OF_NUM_POW2 : thm
  BITS_OF_NUM_1 : thm
  BITS_OF_NUM_DIV : thm
  BITS_OF_NUM_MOD : thm
  BITS_OF_NUM_MUL_ALT : thm
  BITS_OF_NUM_MUL : thm
  BITS_OF_NUM_ADD : thm
  DISJOINT_BITS_HILO : thm
  DISJOINT_BITS_CLAUSES : thm
  DIV_MOD_DISJOINT_BITS : thm
  BITS_OF_WORD_WORD : thm
  BITS_OF_NUM_VAL : thm
  deriving Inhabited

/-- `BIT_PRED` (words.ml 1337). -/
def NumBits.BIT_PRED (N : NumBits) : term → Except String (Option term × thm) :=
  bitPred N.numbitCtx
/-- `NUMBIT_CONV` (words.ml 1337). -/
def NumBits.NUMBIT_CONV (N : NumBits) : ioconv := fun t => pure (numbitConv N.numbitCtx t)

@[nospecialize]
def setupNumBits [HolBase] (D : WordsDeps) (G : Digitsum) (BW : BitsOfWord) (Vl : Val) :
    ExceptT String IO NumBits := do
  let { new_definition, ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, MESON_TAC, NUMBER_RULE,
        SET_RULE, SET_TAC, BITS_ELIM_CONV, .. } := D
  let { ADD_SUB2, ARITH, ARITH_EQ, ARITH_ODD, ARITH_SUC, ARITH_ZERO, COND_RAND,
        COND_SWAP, CONJ_ASSOC, DISJOINT_SYM, DIVIDES_DIV_MULT, DIV_0, DIV_1, DIV_DIV,
        DIV_EQ_0, DIV_EXP, DIV_LT, DIV_MULT2, EQ_IMP, EVEN, EXP, EXP_ADD, EXP_EQ_0,
        EXTENSION, .. } := D.core1
  let { FINITE_NUMSEG_LT, FINITE_RESTRICT, FINITE_SUBSET, FINITE_UNION, IN_ELIM_THM,
        IN_IMAGE, IN_SING, .. } := D.core2
  let { LEFT_IMP_EXISTS_THM, LET_TRANS, LE_EXISTS, LT_POW2_REFL, MOD_2_CASES, MOD_LT,
        MULT_CLAUSES, MULT_SYM, NOT_EVEN, NOT_IN_EMPTY, NOT_LE, NOT_ODD, NSUM_EQ_0_IFF,
        NSUM_RESTRICT_SET, NSUM_RMUL, NSUM_UNION, NUMERAL, ODD, ODD_EXP, ODD_MOD,
        .. } := D.core3
  let { SUBSET, SUB_ADD, .. } := D.core4
  let { DIGITSUM_WORKS_GEN, DIGITSUM_DIV_MOD, DIGITSUM_DIV, DIGITSUM_MOD, .. } := G
  let { bits_of_word, .. } := BW
  let { BIT_VAL, BIT_WORD, .. } := Vl

  let numbit ← new_definition r"numbit i n = ODD(n DIV (2 EXP i))"

  let NUMBIT_VAL ← prove r"numbit i (val (e:N word)) = bit i e"
   (REWRITE_TAC [numbit, BIT_VAL])

  let numbitCtx ← do
    let i ← q "i:num"
    let j ← q "j:num"
    let n ← q "n:num"
    let B0 ← q "BIT0"
    let B1 ← q "BIT1"
    let B00 ← CONJUNCT2 ARITH_ZERO
    let th_0 ← PURE_REWRITE_RULE [NUMERAL] (← prove
     r"numbit i 0 = F" (REWRITE_TAC [numbit, DIV_0, ODD]))
    let (th00, th01) ← CONJ_PAIR (← PURE_REWRITE_RULE [NUMERAL] (← prove
     r"numbit 0 (BIT0 n) = F /\ numbit 0 (BIT1 n) = T"
     (REWRITE_TAC [numbit, EXP, DIV_1, ARITH_ODD])))
    let (thS0, thS1) ← CONJ_PAIR (← UNDISCH (← prove r"i = SUC j ==>
    numbit i (BIT0 n) = numbit j n /\ numbit i (BIT1 n) = numbit j n"
     (DISCH_THEN SUBST1_TAC THEN CONV_TAC BITS_ELIM_CONV THEN
      REWRITE_TAC [numbit, EXP, ← GSYM DIV_DIV,
        ← ARITH_RULE (← q r"(2 * n + 1) DIV 2 = n /\ (2 * n) DIV 2 = n")])))
    let thB1S ← prove r"BIT1 i = SUC (BIT0 i)" (REWRITE_TAC [ARITH_SUC])
    let thB10 ← MATCH_MP (← DISCH_ALL thS0) thB1S
    let thB11 ← MATCH_MP (← DISCH_ALL thS1) thB1S
    let thSB1 ← UNDISCH (← prove r"i = SUC j ==> BIT0 i = SUC (BIT1 j)"
     (DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [ARITH_SUC]))
    let thB00 ← PROVE_HYP thSB1 (← INST [(← q "BIT0 i", i), (← q "BIT1 j", j)] thS0)
    let thB01 ← PROVE_HYP thSB1 (← INST [(← q "BIT0 i", i), (← q "BIT1 j", j)] thS1)
    let (th0B00, th0B01) ← do
      let th ← AP_TERM (← q "numbit") (← TRANS (← AP_TERM (← q "BIT0") (← ASSUME (← q "i = _0"))) B00)
      pure (← TRANS (← AP_THM th (← q "BIT0 n")) th00, ← TRANS (← AP_THM th (← q "BIT1 n")) th01)
    let thN ← prove r"numbit (NUMERAL i) (NUMERAL n) = numbit i n" (REWRITE_TAC [NUMERAL])
    pure { i, j, n, B0, B1, B00, th_0, th00, th01, thB1S, thB10, thB11, thSB1, thB00,
           thB01, th0B00, th0B01, thN : NumbitCtx }

  let bits_of_num ← new_definition
   r"bits_of_num n = {i | numbit i n}"

  let IN_BITS_OF_NUM ← prove
   r"!n i. i IN bits_of_num n <=> ODD(n DIV 2 EXP i)"
   (REWRITE_TAC [bits_of_num, numbit, IN_ELIM_THM])

  let BITS_OF_NUM_SUBSET_NUMSEG_LT ← prove
   r"!n. bits_of_num n SUBSET {i | i < n}"
   (REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_BITS_OF_NUM] THEN
    MESON_TAC [DIV_LT, EVEN, LT_POW2_REFL, LET_TRANS, NOT_LE, NOT_EVEN])

  let FINITE_BITS_OF_NUM ← prove
   r"!n. FINITE(bits_of_num n)"
   (MESON_TAC [BITS_OF_NUM_SUBSET_NUMSEG_LT, FINITE_NUMSEG_LT, FINITE_SUBSET])

  let NSUM_BITS_OF_NUM ← prove
   r"!n. nsum (bits_of_num n) (\i. 2 EXP i) = n"
   (GEN_TAC THEN MP_TAC (← SPECL [← q "2", ← q "n:num", ← q "n:num"] DIGITSUM_WORKS_GEN) THEN
    REWRITE_TAC [MOD_2_CASES, COND_RAND, MULT_CLAUSES] THEN
    REWRITE_TAC [← GSYM NOT_ODD, COND_SWAP, ← GSYM NSUM_RESTRICT_SET] THEN
    SIMP_TAC [MOD_LT, LT_POW2_REFL] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC (← SPEC (← q "n:num") BITS_OF_NUM_SUBSET_NUMSEG_LT) THEN
    REWRITE_TAC [bits_of_num, numbit] THEN SET_TAC [])

  let BITS_OF_NUM_NSUM ← prove
   r"!s. FINITE s ==> bits_of_num (nsum s (\i. 2 EXP i)) = s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [EXTENSION, IN_BITS_OF_NUM, ODD_MOD] THEN
    X_GEN_TAC (← q "k:num") THEN MP_TAC (← SPECL
      [← q "2", ← q r"\i:num. 1", ← q "s:num->bool", ← q "k:num"] DIGITSUM_DIV_MOD) THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q "1 < 2"), MULT_CLAUSES] THEN ARITH_TAC)

  let BITS_OF_NUM_EQ ← prove
   r"!m n. bits_of_num m = bits_of_num n <=> m = n"
   (MESON_TAC [NSUM_BITS_OF_NUM])

  let BITS_OF_NUM_GALOIS ← prove
   r"!n s. bits_of_num n = s <=> FINITE s /\ nsum s (\i. 2 EXP i) = n"
   (MESON_TAC [FINITE_BITS_OF_NUM, BITS_OF_NUM_NSUM, NSUM_BITS_OF_NUM])

  let NSUM_BITS_DIV ← prove
   r"!s k. FINITE s
         ==> nsum s (\i. 2 EXP i) DIV 2 EXP k =
             nsum {i | i IN s /\ k <= i} (\i. 2 EXP (i - k))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q "2", ← q r"\i:num. 1", ← q "s:num->bool", ← q "k:num"] DIGITSUM_DIV) THEN
    ASM_REWRITE_TAC [← ARITH_RULE (← q "1 < 2"), MULT_CLAUSES])

  let NSUM_BITS_MOD ← prove
   r"!s k. FINITE s
         ==> nsum s (\i. 2 EXP i) MOD 2 EXP k =
             nsum {i | i IN s /\ i < k} (\i. 2 EXP i)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q "2", ← q r"\i:num. 1", ← q "s:num->bool", ← q "k:num"] DIGITSUM_MOD) THEN
    ASM_REWRITE_TAC [← ARITH_RULE (← q "1 < 2"), MULT_CLAUSES])

  let NSUM_BITS_EQ ← prove
   r"!s t. FINITE s /\ FINITE t
         ==> (nsum s (\i. 2 EXP i) = nsum t (\i. 2 EXP i) <=> s = t)"
   (MESON_TAC [BITS_OF_NUM_NSUM])

  let BITSUM_BOUND ← prove
   r"!s k. FINITE s
         ==> (nsum s (\i. 2 EXP i) < 2 EXP k <=> s SUBSET {i | i < k})"
   (SIMP_TAC [← CONV_RULE (RAND_CONV SYM_CONV) (← SPEC_ALL DIV_EQ_0), FINITE_RESTRICT,
              EXP_EQ_0, ARITH_EQ, NSUM_BITS_DIV, NSUM_EQ_0_IFF] THEN
    REWRITE_TAC [← GSYM NOT_LE] THEN SET_TAC [])

  let BITS_OF_NUM_SUBSET_NUMSEG_EQ ← prove
   r"!n k. bits_of_num n SUBSET {i | i < k} <=> n < 2 EXP k"
   (SIMP_TAC [← GSYM BITSUM_BOUND, FINITE_BITS_OF_NUM, NSUM_BITS_OF_NUM])

  let BITSUM_DIVIDES ← prove
   r"!s k. FINITE s
         ==> (2 EXP k divides nsum s (\i. 2 EXP i) <=>
              DISJOINT {i | i < k} s)"
   (SIMP_TAC [DIVIDES_DIV_MULT, NSUM_BITS_DIV, ← GSYM NSUM_RMUL, ← GSYM EXP_ADD] THEN
    SIMP_TAC [SUB_ADD, NSUM_BITS_EQ, FINITE_RESTRICT, FINITE_NUMSEG_LT] THEN
    REWRITE_TAC [← GSYM NOT_LE] THEN SET_TAC [])

  let BITS_OF_NUM_DISJOINT_NUMSEG_EQ ← prove
   r"!n k. DISJOINT {i | i < k} (bits_of_num n) <=> 2 EXP k divides n"
   (SIMP_TAC [← GSYM BITSUM_DIVIDES, FINITE_BITS_OF_NUM, NSUM_BITS_OF_NUM])

  let BITS_OF_NUM_0 ← prove
   r"bits_of_num 0 = {}"
   (REWRITE_TAC [IN_BITS_OF_NUM, EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY] THEN
    REWRITE_TAC [DIV_0, ODD])

  let BITS_OF_NUM_POW2 ← prove
   r"!k. bits_of_num(2 EXP k) = {k}"
   (REWRITE_TAC [IN_BITS_OF_NUM, EXTENSION, IN_ELIM_THM, IN_SING] THEN
    REPEAT GEN_TAC THEN SIMP_TAC [DIV_EXP, ARITH_EQ] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [ODD_EXP, ARITH] THEN ASM_ARITH_TAC)

  let BITS_OF_NUM_1 ← prove
   r"bits_of_num 1 = {0}"
   (REWRITE_TAC [← GSYM BITS_OF_NUM_POW2, EXP])

  let BITS_OF_NUM_DIV ← prove
   r"!n k. bits_of_num (n DIV 2 EXP k) = {i | (k + i) IN bits_of_num n}"
   (REWRITE_TAC [bits_of_num, numbit, IN_ELIM_THM, DIV_DIV, EXP_ADD])

  let BITS_OF_NUM_MOD ← prove
   r"!n k. bits_of_num (n MOD 2 EXP k) = {i | i IN bits_of_num n /\ i < k}"
   (SIMP_TAC [BITS_OF_NUM_GALOIS, FINITE_RESTRICT, FINITE_BITS_OF_NUM,
              ← GSYM NSUM_BITS_MOD, NSUM_BITS_OF_NUM])

  let BITS_OF_NUM_MUL_ALT ← prove
   r"(!n k. bits_of_num(2 EXP k * n) = {i | k <= i /\ i - k IN bits_of_num n}) /\
   (!n k. bits_of_num(n * 2 EXP k) = {i | k <= i /\ i - k IN bits_of_num n})"
   (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
    REWRITE_TAC [] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC (← SET_RULE
     (← q r"DISJOINT {i | ~P i} s /\ (!i. P i ==> (i IN s <=> Q i))
    ==> s = {i | P i /\ Q i}")) THEN
    REWRITE_TAC [NOT_LE, BITS_OF_NUM_DISJOINT_NUMSEG_EQ] THEN
    SIMP_TAC [LE_EXISTS, LEFT_IMP_EXISTS_THM, IN_BITS_OF_NUM, EXP_ADD] THEN
    SIMP_TAC [ADD_SUB2, DIV_MULT2, EXP_EQ_0, ARITH_EQ] THEN
    CONV_TAC (fun t => (NUMBER_RULE t).run))

  let BITS_OF_NUM_MUL ← prove
   r"(!n k. bits_of_num(2 EXP k * n) = IMAGE (\i. k + i) (bits_of_num n)) /\
   (!n k. bits_of_num(n * 2 EXP k) = IMAGE (\i. k + i) (bits_of_num n))"
   (REWRITE_TAC [BITS_OF_NUM_MUL_ALT] THEN
    REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN
    MESON_TAC [LE_EXISTS, ADD_SUB2])

  let BITS_OF_NUM_ADD ← prove
   r"!m n. DISJOINT (bits_of_num m) (bits_of_num n)
         ==> bits_of_num(m + n) = (bits_of_num m) UNION (bits_of_num n)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [BITS_OF_NUM_GALOIS, FINITE_UNION, FINITE_BITS_OF_NUM] THEN
    ASM_SIMP_TAC [NSUM_UNION, FINITE_BITS_OF_NUM, NSUM_BITS_OF_NUM])

  let DISJOINT_BITS_HILO ← prove
   r"!k h l. l < 2 EXP k
           ==> DISJOINT (bits_of_num(2 EXP k * h)) (bits_of_num l)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ] THEN
    MATCH_MP_TAC (← SET_RULE (← q r"DISJOINT t u ==> s SUBSET t ==> DISJOINT u s")) THEN
    REWRITE_TAC [BITS_OF_NUM_DISJOINT_NUMSEG_EQ] THEN
    CONV_TAC (fun t => (NUMBER_RULE t).run))

  let DISJOINT_BITS_CLAUSES ← prove
   r"(!k h l. l < 2 EXP k
            ==> DISJOINT (bits_of_num(2 EXP k * h)) (bits_of_num l)) /\
   (!k h l. l < 2 EXP k
            ==> DISJOINT (bits_of_num(h * 2 EXP k)) (bits_of_num l)) /\
   (!k h l. l < 2 EXP k
            ==> DISJOINT (bits_of_num l) (bits_of_num(2 EXP k * h))) /\
   (!k h l. l < 2 EXP k
            ==> DISJOINT (bits_of_num l) (bits_of_num(h * 2 EXP k))) /\
   (!m n k. DISJOINT (bits_of_num m) (bits_of_num n)
            ==> DISJOINT (bits_of_num(2 EXP k * m))
                         (bits_of_num(2 EXP k * n))) /\
   (!m n k. DISJOINT (bits_of_num m) (bits_of_num n)
            ==> DISJOINT (bits_of_num(m * 2 EXP k))
                         (bits_of_num(n * 2 EXP k))) /\
   (!m n k. DISJOINT (bits_of_num m) (bits_of_num n)
            ==> DISJOINT (bits_of_num(m DIV 2 EXP k))
                         (bits_of_num(n DIV 2 EXP k))) /\
   (!m n k. DISJOINT (bits_of_num m) (bits_of_num n)
            ==> DISJOINT (bits_of_num(m MOD 2 EXP k))
                         (bits_of_num(n MOD 2 EXP k)))"
   (REPLICATE_TAC 3 (GEN_REWRITE_TAC id [CONJ_ASSOC]) THEN CONJ_TAC THENL
     [MESON_TAC [DISJOINT_BITS_HILO, MULT_SYM, DISJOINT_SYM],
      SIMP_TAC [BITS_OF_NUM_DIV, BITS_OF_NUM_MOD, BITS_OF_NUM_MUL_ALT] THEN
      SET_TAC []])

  let DIV_MOD_DISJOINT_BITS ← prove
   r"(!m n. DISJOINT (bits_of_num m) (bits_of_num n)
          ==> (m + n) DIV 2 EXP k = m DIV 2 EXP k + n DIV 2 EXP k) /\
   (!m n. DISJOINT (bits_of_num m) (bits_of_num n)
          ==> (m + n) MOD 2 EXP k = m MOD 2 EXP k + n MOD 2 EXP k)"
   (SIMP_TAC [← GSYM BITS_OF_NUM_EQ, BITS_OF_NUM_ADD, DISJOINT_BITS_CLAUSES,
              BITS_OF_NUM_DIV, BITS_OF_NUM_MOD] THEN
    SET_TAC [])

  let BITS_OF_WORD_WORD ← prove
   r"!n. bits_of_word(word n:N word) =
       {i | i < dimindex(:N)} INTER bits_of_num n"
   (REWRITE_TAC [bits_of_num, bits_of_word, BIT_WORD, numbit] THEN SET_TAC [])

  let BITS_OF_NUM_VAL ← prove
   r"!x:N word. bits_of_num(val x) = bits_of_word(x)"
   (REWRITE_TAC [bits_of_num, bits_of_word, NUMBIT_VAL])

  return { numbit, NUMBIT_VAL, numbitCtx, bits_of_num, IN_BITS_OF_NUM,
           BITS_OF_NUM_SUBSET_NUMSEG_LT, FINITE_BITS_OF_NUM, NSUM_BITS_OF_NUM,
           BITS_OF_NUM_NSUM, BITS_OF_NUM_EQ, BITS_OF_NUM_GALOIS, NSUM_BITS_DIV,
           NSUM_BITS_MOD, NSUM_BITS_EQ, BITSUM_BOUND, BITS_OF_NUM_SUBSET_NUMSEG_EQ,
           BITSUM_DIVIDES, BITS_OF_NUM_DISJOINT_NUMSEG_EQ, BITS_OF_NUM_0,
           BITS_OF_NUM_POW2, BITS_OF_NUM_1, BITS_OF_NUM_DIV, BITS_OF_NUM_MOD,
           BITS_OF_NUM_MUL_ALT, BITS_OF_NUM_MUL, BITS_OF_NUM_ADD, DISJOINT_BITS_HILO,
           DISJOINT_BITS_CLAUSES, DIV_MOD_DISJOINT_BITS, BITS_OF_WORD_WORD,
           BITS_OF_NUM_VAL }

/- ------------------------------------------------------------------------- -/
/- A primitive operation for splitting numerals along powers of 2.           -/
/- ------------------------------------------------------------------------- -/

/-- The terms and proformas `NUM_SHIFT_ADD_CORE` closes over
    (words.ml 1629-1641, 1665-1668). -/
structure NsaCtx where
  N : NumbitCtx
  i : term
  j : term
  a : term
  b : term
  e : term
  i0 : thm
  B0S : thm
  B1S : thm
  ZS : thm
  B00 : thm
  Z0 : thm
  pthn : thm
  deriving Inhabited

/-- `go` of words.ml 1642-1664, exported as `NUM_SHIFT_ADD_CORE`. -/
partial def nsaGo (K : NsaCtx) (a' b' i' : term) : Except String thm := do
  match ← bitPred K.N i' with
  | (none, th) =>
    Equal.PROVE_HYP th (← HolCore.Kernel.INST [(i', K.i), (a', K.a), (b', K.b)] K.i0)
  | (some j', th) =>
    let r ← (match a' with
      | .Comb (.Const "BIT0" _) a'' => do
        let th' ← nsaGo K a'' b' j'
        let x ← (match ← rhs (concl th') with
          | .Const "_0" _ =>
            HolCore.Kernel.INST [(i', K.i), (j', K.j), (a'', K.a), (b', K.b)] K.B00
          | e' =>
            HolCore.Kernel.INST [(e', K.e), (i', K.i), (j', K.j), (a'', K.a), (b', K.b)] K.B0S)
        Equal.PROVE_HYP th' x
      | .Comb (.Const "BIT1" _) a'' => do
        let th' ← nsaGo K a'' b' j'
        let e' ← rhs (concl th')
        Equal.PROVE_HYP th'
          (← HolCore.Kernel.INST [(e', K.e), (i', K.i), (j', K.j), (a'', K.a), (b', K.b)] K.B1S)
      | .Const "_0" _ => do
        let th' ← nsaGo K a' b' j'
        let x ← (match ← rhs (concl th') with
          | .Const "_0" _ =>
            HolCore.Kernel.INST [(i', K.i), (j', K.j), (a', K.a), (b', K.b)] K.Z0
          | e' =>
            HolCore.Kernel.INST [(e', K.e), (i', K.i), (j', K.j), (a', K.a), (b', K.b)] K.ZS)
        Equal.PROVE_HYP th' x
      | _ => .error "NUM_SHIFT_ADD_CORE"
      : Except String thm)
    Equal.PROVE_HYP th r

/-- `NUM_SHIFT_ADD_CONV` (words.ml 1669-1675). -/
def nsaConv (K : NsaCtx) : term → Except String thm
  | .Comb (.Comb (.Comb (.Const "num_shift_add" _) (.Comb (.Const "NUMERAL" _) a'))
            (.Comb (.Const "NUMERAL" _) b')) (.Comb (.Const "NUMERAL" _) i') => do
    let th ← nsaGo K a' b' i'
    Equal.PROVE_HYP th
      (← HolCore.Kernel.INST [(a', K.a), (b', K.b), (i', K.i), (← rhs (concl th), K.e)] K.pthn)
  | .Comb (.Comb (.Comb (.Const "num_shift_add" _) a') b') i' => nsaGo K a' b' i'
  | _ => .error "NUM_SHIFT_ADD_CONV"

structure NumShiftAdd where
  num_shift_add : thm
  num_shift_add_0 : thm
  EXP_2_MOD_LT : thm
  num_shift_add_SUC : thm
  num_shift_add_lt : thm
  num_shift_add_mod : thm
  /-- The context of `NUM_SHIFT_ADD_CORE` and `NUM_SHIFT_ADD_CONV`. -/
  nsaCtx : NsaCtx
  deriving Inhabited

/-- `NUM_SHIFT_ADD_CORE a b i` (words.ml 1628). -/
def NumShiftAdd.NUM_SHIFT_ADD_CORE (S : NumShiftAdd) (a b i : term) : Except String thm :=
  nsaGo S.nsaCtx a b i
/-- `NUM_SHIFT_ADD_CONV` (words.ml 1628). -/
def NumShiftAdd.NUM_SHIFT_ADD_CONV (S : NumShiftAdd) : ioconv := fun t => pure (nsaConv S.nsaCtx t)

@[nospecialize]
def setupNumShiftAdd [HolBase] (D : WordsDeps) (NB : NumBits) :
    ExceptT String IO NumShiftAdd := do
  let { new_definition, ARITH_RULE, BITS_ELIM_CONV, .. } := D
  let { ADD, ADD_AC, ADD_SYM, ARITH_ZERO, EQ_ADD_LCANCEL, EXP, EXP_2_NE_0, EXP_ADD, .. } := D.core1
  let { LEFT_ADD_DISTRIB, LE_MULT_RCANCEL, LE_SUC_LT, LTE_TRANS, LT_ADD_LCANCEL,
        MOD_1, MOD_ADD_MOD, MOD_LT, MOD_LT_EQ, MOD_MOD_REFL, MOD_MULT2, MULT_AC,
        MULT_CLAUSES, MULT_SYM, NUMERAL, .. } := D.core3

  let num_shift_add ← new_definition
   r"num_shift_add a b n = a MOD 2 EXP n + b * 2 EXP n"

  let num_shift_add_0 ← prove
   r"num_shift_add a b 0 = b"
   (REWRITE_TAC [num_shift_add, EXP, MOD_1, MULT_CLAUSES, ADD])

  let EXP_2_MOD_LT ←
    GEN_ALL (← REWRITE_RULE [← GSYM (← SPEC (← q "a:num") MOD_LT_EQ)] EXP_2_NE_0)

  let num_shift_add_SUC ← prove
   r"num_shift_add (BIT0 a) b (SUC n) = BIT0 (num_shift_add a b n) /\
   num_shift_add (BIT1 a) b (SUC n) = BIT1 (num_shift_add a b n)"
   (REWRITE_TAC [num_shift_add, EXP] THEN CONV_TAC BITS_ELIM_CONV THEN
    REWRITE_TAC [LEFT_ADD_DISTRIB, MOD_MULT2, MULT_AC] THEN
    REWRITE_TAC [ADD_AC, EQ_ADD_LCANCEL] THEN
    ONCE_REWRITE_TAC [← SYM (← MATCH_MP MOD_LT
      (← MATCH_MP (← ARITH_RULE (← q r"a < b ==> a * 2 + 1 < b * 2"))
        (← SPECL [← q "a:num", ← q "n:num"] EXP_2_MOD_LT)))] THEN
    ONCE_REWRITE_TAC [← GSYM MOD_ADD_MOD] THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [MULT_SYM] MOD_MULT2, MOD_MOD_REFL])

  let num_shift_add_lt ← prove
   r"!a b n i. b < 2 EXP i ==> num_shift_add a b n < 2 EXP (i + n)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [num_shift_add, EXP_ADD] THEN
    DISCH_TAC THEN MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC (← q r"SUC b * 2 EXP n") THEN
    ASM_REWRITE_TAC [LE_MULT_RCANCEL, MULT_CLAUSES, ADD_SYM, LT_ADD_LCANCEL,
      EXP_2_MOD_LT, LE_SUC_LT])

  let num_shift_add_mod ← prove
   r"num_shift_add a (b MOD 2 EXP i) n = num_shift_add a b n MOD 2 EXP (i + n)"
   (ONCE_REWRITE_TAC [← (SYM o MATCH_MP MOD_LT o SPEC_ALL)
      (← MATCH_MP num_shift_add_lt (← SPECL [← q "b:num", ← q "i:num"] EXP_2_MOD_LT))] THEN
    REWRITE_TAC [num_shift_add, EXP_ADD] THEN
    ONCE_REWRITE_TAC [← GSYM MOD_ADD_MOD] THEN
    REWRITE_TAC [← GSYM (← ONCE_REWRITE_RULE [MULT_SYM] MOD_MULT2), MOD_MOD_REFL])

  let nsaCtx ← do
    let i ← q "i:num"
    let j ← q "j:num"
    let a ← q "a:num"
    let b ← q "b:num"
    let e ← q "e:num"
    let i0 ← UNDISCH (← prove r"i = _0 ==> num_shift_add a b i = b"
     (DISCH_THEN SUBST1_TAC THEN CONV_TAC BITS_ELIM_CONV THEN
      ACCEPT_TAC num_shift_add_0))
    let (B0S, B1S) ← CONJ_PAIR (← UNDISCH_ALL (← prove
     r"num_shift_add a b j = e ==> i = SUC j ==>
    num_shift_add (BIT0 a) b i = BIT0 e /\
    num_shift_add (BIT1 a) b i = BIT1 e"
     (DISCH_THEN (SUBST1_TAC o SYM) THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [num_shift_add_SUC])))
    let ZS ← REWRITE_RULE [ARITH_ZERO] (← INST [(← q "_0", a)] B0S)
    let B00 ← REWRITE_RULE [ARITH_ZERO] (← INST [(← q "_0", e)] B0S)
    let Z0 ← REWRITE_RULE [ARITH_ZERO] (← INST [(← q "_0", e)] ZS)
    let pthn ← UNDISCH (← prove
     r"num_shift_add a b i = e ==>
     num_shift_add (NUMERAL a) (NUMERAL b) (NUMERAL i) = NUMERAL e"
     (REWRITE_TAC [NUMERAL]))
    pure { N := NB.numbitCtx, i, j, a, b, e, i0, B0S, B1S, ZS, B00, Z0, pthn : NsaCtx }

  return { num_shift_add, num_shift_add_0, EXP_2_MOD_LT, num_shift_add_SUC,
           num_shift_add_lt, num_shift_add_mod, nsaCtx }

/- ------------------------------------------------------------------------- -/
/- Some "limiting" values with names in the style of C's "limits.h" macros,  -/
/- and saturating versions of the conversions from N and Z to words.         -/
/- ------------------------------------------------------------------------- -/

structure Limits where
  word_UINT_MAX : thm
  word_INT_MIN : thm
  word_INT_MAX : thm
  WORD_INT_MIN : thm
  WORD_INT_MAX : thm
  VAL_WORD_UINT_MAX : thm
  IVAL_WORD_INT_MIN : thm
  IVAL_WORD_INT_MAX : thm
  VAL_BOUND_ALT : thm
  IVAL_BOUND_ALT : thm
  VAL_WORD_INT_MIN : thm
  INT_VAL_WORD_INT_MIN : thm
  WORD_INT_MIN_ALT : thm
  BIT_WORD_INT_MIN : thm
  word_saturate : thm
  iword_saturate : thm
  deriving Inhabited

@[nospecialize]
def setupLimits [HolBase] (D : WordsDeps) (V : Bitval) (Vl : Val) (Iv : Ival) :
    ExceptT String IO Limits := do
  let { new_definition, ARITH_RULE, ARITH_TAC, INTEGER_RULE, INT_ARITH, INT_ARITH_TAC,
        .. } := D
  let { ARITH_EQ, DIMINDEX_GE_1, DIMINDEX_NONZERO, EXP_EQ_0, .. } := D.core1
  let { INT_LE_REFL, INT_LT_POW2, INT_MUL_RID, INT_NEG_LT0, INT_OF_NUM_EQ,
        INT_OF_NUM_POW, INT_OF_NUM_SUB, INT_POW, .. } := D.core2
  let { LE_1, MOD_LT, .. } := D.core3
  let { BITVAL_CLAUSES, .. } := V
  let { VAL_BOUND, VAL_EQ, VAL_WORD, VAL_WORD_OF_BITS_SING, BIT_WORD_OF_BITS_SING, .. } := Vl
  let { WORD_IWORD, IWORD_EQ, IVAL_IWORD, IVAL_BOUND, VAL_IVAL, MSB_IVAL, .. } := Iv

  let word_UINT_MAX ← new_definition
   r"word_UINT_MAX:N word = word(2 EXP dimindex(:N) - 1)"

  let word_INT_MIN ← new_definition
   r"word_INT_MIN:N word = iword(--(&2 pow (dimindex(:N) - 1)))"

  let word_INT_MAX ← new_definition
   r"word_INT_MAX:N word = iword(&2 pow (dimindex(:N) - 1) - &1)"

  let WORD_INT_MIN ← prove
   r"word_INT_MIN:N word = word(2 EXP (dimindex(:N) - 1))"
   (REWRITE_TAC [word_INT_MIN, WORD_IWORD, IWORD_EQ, ← GSYM INT_OF_NUM_POW] THEN
    MATCH_MP_TAC (← INTEGER_RULE (← q r"&2 * x:int = y ==> (--x == x) (mod y)")) THEN
    REWRITE_TAC [← GSYM (← CONJUNCT2 INT_POW)] THEN
    SIMP_TAC [DIMINDEX_NONZERO, ← ARITH_RULE (← q r"~(n = 0) ==> SUC(n - 1) = n")])

  let WORD_INT_MAX ← prove
   r"word_INT_MAX:N word = word(2 EXP (dimindex(:N) - 1) - 1)"
   (REWRITE_TAC [word_INT_MAX, WORD_IWORD] THEN AP_TERM_TAC THEN
    SIMP_TAC [INT_OF_NUM_SUB, INT_OF_NUM_POW, LE_1, EXP_EQ_0, ARITH_EQ])

  let VAL_WORD_UINT_MAX ← prove
   r"val(word_UINT_MAX:N word) = 2 EXP dimindex(:N) - 1"
   (REWRITE_TAC [word_UINT_MAX, VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC [← ARITH_RULE (← q r"n - 1 < n <=> ~(n = 0)"), EXP_EQ_0] THEN ARITH_TAC)

  let IVAL_WORD_INT_MIN ← prove
   r"ival(word_INT_MIN:N word) = --(&2 pow (dimindex(:N) - 1))"
   (REWRITE_TAC [word_INT_MIN] THEN MATCH_MP_TAC IVAL_IWORD THEN
    REWRITE_TAC [INT_LE_REFL, ← INT_ARITH (← q r"--a:int < a <=> &0 < a")] THEN
    SIMP_TAC [INT_LT_POW2])

  let IVAL_WORD_INT_MAX ← prove
   r"ival(word_INT_MAX:N word) = &2 pow (dimindex(:N) - 1) - &1"
   (REWRITE_TAC [word_INT_MAX] THEN MATCH_MP_TAC IVAL_IWORD THEN
    REWRITE_TAC [← INT_ARITH (← q r"x - &1:int < x")] THEN
    MATCH_MP_TAC (← INT_ARITH (← q r"&0:int < x ==> --x <= x - &1")) THEN
    SIMP_TAC [INT_LT_POW2])

  let VAL_BOUND_ALT ← prove
   r"!w:N word. val w <= val(word_UINT_MAX:N word)"
   (GEN_TAC THEN MP_TAC (← ISPEC (← q "w:N word") VAL_BOUND) THEN
    REWRITE_TAC [VAL_WORD_UINT_MAX] THEN ARITH_TAC)

  let IVAL_BOUND_ALT ← prove
   r"!w:N word. ival(word_INT_MIN:N word) <= ival w /\
              ival w <= ival(word_INT_MAX:N word)"
   (GEN_TAC THEN MP_TAC (← ISPEC (← q "w:N word") IVAL_BOUND) THEN
    REWRITE_TAC [IVAL_WORD_INT_MAX, IVAL_WORD_INT_MIN] THEN INT_ARITH_TAC)

  let VAL_WORD_INT_MIN ← prove
   r"val(word_INT_MIN:N word) = 2 EXP (dimindex(:N) - 1)"
   (REWRITE_TAC [← GSYM INT_OF_NUM_EQ, VAL_IVAL, ← GSYM INT_OF_NUM_POW] THEN
    REWRITE_TAC [MSB_IVAL, IVAL_WORD_INT_MIN] THEN
    SIMP_TAC [INT_NEG_LT0, INT_LT_POW2, BITVAL_CLAUSES, INT_MUL_RID] THEN
    REWRITE_TAC [← INT_ARITH (← q r"--x + y:int = x <=> &2 * x = y")] THEN
    SIMP_TAC [← GSYM (← CONJUNCT2 INT_POW)] THEN AP_TERM_TAC THEN
    REWRITE_TAC [← ARITH_RULE (← q r"SUC(n - 1) = n <=> ~(n = 0)"), DIMINDEX_NONZERO])

  let INT_VAL_WORD_INT_MIN ← prove
   r"&(val(word_INT_MIN:N word)):int = &2 pow (dimindex(:N) - 1)"
   (REWRITE_TAC [INT_OF_NUM_POW, INT_OF_NUM_EQ, VAL_WORD_INT_MIN])

  let WORD_INT_MIN_ALT ← prove
   r"word_INT_MIN:N word = word_of_bits {dimindex (:N) - 1}"
   (REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_INT_MIN, VAL_WORD_OF_BITS_SING] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"n - 1 < n <=> 1 <= n"), DIMINDEX_GE_1])

  let BIT_WORD_INT_MIN ← prove
   r"!i. bit i (word_INT_MIN:N word) <=> i = dimindex(:N) - 1"
   (REWRITE_TAC [WORD_INT_MIN_ALT, BIT_WORD_OF_BITS_SING] THEN
    REWRITE_TAC [DIMINDEX_GE_1, ← ARITH_RULE (← q r"n - 1 < n <=> 1 <= n")])

  let word_saturate ← new_definition
   r"(word_saturate:num->N word) n =
        if n > val(word_UINT_MAX:N word) then word_UINT_MAX
        else word n"

  let iword_saturate ← new_definition
   r"(iword_saturate:int->N word) x =
        if x < ival(word_INT_MIN:N word) then word_INT_MIN
        else if x > ival(word_INT_MAX:N word) then word_INT_MAX
        else iword x"

  return { word_UINT_MAX, word_INT_MIN, word_INT_MAX, WORD_INT_MIN, WORD_INT_MAX,
           VAL_WORD_UINT_MAX, IVAL_WORD_INT_MIN, IVAL_WORD_INT_MAX, VAL_BOUND_ALT,
           IVAL_BOUND_ALT, VAL_WORD_INT_MIN, INT_VAL_WORD_INT_MIN, WORD_INT_MIN_ALT,
           BIT_WORD_INT_MIN, word_saturate, iword_saturate }

/- ------------------------------------------------------------------------- -/
/- Population count (= number of 1s in a word), as a mathematical number,    -/
/- and parity (= evenness or oddity of the popcount).                        -/
/- ------------------------------------------------------------------------- -/

structure Popcount where
  word_popcount : thm
  HAS_SIZE_BITS_OF_WORD_POPCOUNT : thm
  WORD_POPCOUNT_BOUND : thm
  WORD_POPCOUNT_BOUND_SIZE : thm
  WORD_POPCOUNT_EQ_0 : thm
  WORD_POPCOUNT_0 : thm
  WORD_POPCOUNT_1 : thm
  WORD_POPCOUNT_BITVAL : thm
  WORD_POPCOUNT_NSUM : thm
  WORD_POPCOUNT_LE_BITS : thm
  WORD_POPCOUNT_WORD_OF_BITS_GEN : thm
  WORD_POPCOUNT_WORD_OF_BITS : thm
  word_evenparity : thm
  word_oddparity : thm
  NOT_WORD_EVENPARITY : thm
  NOT_WORD_ODDPARITY : thm
  WORD_EVENPARITY_0 : thm
  WORD_ODDPARITY_0 : thm
  WORD_EVENPARITY_1 : thm
  WORD_ODDPARITY_1 : thm
  deriving Inhabited

@[nospecialize]
def setupPopcount [HolBase] (D : WordsDeps) (V : Bitval) (W : WordType) (BW : BitsOfWord)
    (Vl : Val) : ExceptT String IO Popcount := do
  let { new_definition, ASM_MESON_TAC, MESON_TAC, NUM_REDUCE_CONV, .. } := D
  let { CARD_EQ_0, CARD_NUMSEG_LT, CARD_SING, CARD_SUBSET, EVEN, .. } := D.core1
  let { FINITE_NUMSEG_LT, FINITE_RESTRICT, HAS_SIZE, INTER_COMM, IN_ELIM_THM, .. } := D.core2
  let { LE_0, LE_REFL, MULT_CLAUSES, NOT_EVEN, NOT_LT, NOT_ODD, NSUM_CONST,
        NSUM_RESTRICT_SET, .. } := D.core3
  let { SUBSET, SUBSET_INTER_ABSORPTION, .. } := D.core4
  let { bitval, .. } := V
  let { BIT_TRIVIAL, BIT_GUARD, .. } := W
  let { bits_of_word, FINITE_BITS_OF_WORD, BITS_OF_WORD_SUBSET_ALT,
        BITS_OF_WORD_OF_BITS, .. } := BW
  let { UPPER_BITS_ZERO, BITS_OF_WORD_EQ_EMPTY, BITS_OF_WORD_1, .. } := Vl

  let word_popcount ← new_definition
   r"word_popcount (x:N word) = CARD(bits_of_word x)"

  let HAS_SIZE_BITS_OF_WORD_POPCOUNT ← prove
   r"!x:N word. (bits_of_word x) HAS_SIZE word_popcount x"
   (REWRITE_TAC [word_popcount, HAS_SIZE, FINITE_BITS_OF_WORD])

  let WORD_POPCOUNT_BOUND ← prove
   r"!x:N word. word_popcount x <= dimindex(:N)"
   (GEN_TAC THEN REWRITE_TAC [word_popcount, bits_of_word] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM CARD_NUMSEG_LT] THEN
    MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC [FINITE_NUMSEG_LT] THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN MESON_TAC [BIT_TRIVIAL, NOT_LT])

  let WORD_POPCOUNT_BOUND_SIZE ← prove
   r"!(x:N word) n. val x < 2 EXP n ==> word_popcount x <= n"
   (REWRITE_TAC [← GSYM UPPER_BITS_ZERO] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [word_popcount] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM CARD_NUMSEG_LT] THEN
    MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC [FINITE_NUMSEG_LT] THEN
    REWRITE_TAC [bits_of_word, SUBSET, IN_ELIM_THM] THEN
    ASM_MESON_TAC [NOT_LT])

  let WORD_POPCOUNT_EQ_0 ← prove
   r"!x:N word. word_popcount x = 0 <=> x = word 0"
   (SIMP_TAC [CARD_EQ_0, word_popcount, FINITE_BITS_OF_WORD] THEN
    REWRITE_TAC [BITS_OF_WORD_EQ_EMPTY])

  let WORD_POPCOUNT_0 ← prove
   r"word_popcount(word 0) = 0"
   (REWRITE_TAC [WORD_POPCOUNT_EQ_0])

  let WORD_POPCOUNT_1 ← prove
   r"word_popcount(word 1) = 1"
   (REWRITE_TAC [word_popcount, BITS_OF_WORD_1, CARD_SING])

  let WORD_POPCOUNT_BITVAL ← prove
   r"!b. word_popcount(word(bitval b):N word) <= 1"
   (GEN_TAC THEN REWRITE_TAC [bitval] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [WORD_POPCOUNT_0, WORD_POPCOUNT_1, LE_0, LE_REFL])

  let WORD_POPCOUNT_NSUM ← prove
   r"!x:N word.
        word_popcount x = nsum {i | i < dimindex(:N)} (\i. bitval(bit i x))"
   (GEN_TAC THEN REWRITE_TAC [bitval, ← GSYM NSUM_RESTRICT_SET] THEN
    SIMP_TAC [NSUM_CONST, FINITE_RESTRICT, FINITE_NUMSEG_LT] THEN
    REWRITE_TAC [word_popcount, ← GSYM BIT_GUARD, IN_ELIM_THM, MULT_CLAUSES] THEN
    REWRITE_TAC [bits_of_word])

  let WORD_POPCOUNT_LE_BITS ← prove
   r"!(x:M word) (y:N word).
     (!i. i < dimindex(:M) /\ bit i x ==> bit i y)
     ==> word_popcount x <= word_popcount y"
   (REWRITE_TAC [← GSYM BITS_OF_WORD_SUBSET_ALT, word_popcount] THEN
    SIMP_TAC [CARD_SUBSET, FINITE_BITS_OF_WORD])

  let WORD_POPCOUNT_WORD_OF_BITS_GEN ← prove
   r"!s. word_popcount(word_of_bits s:N word) =
       CARD({i | i < dimindex(:N)} INTER s)"
   (REWRITE_TAC [word_popcount, BITS_OF_WORD_OF_BITS, INTER_COMM])

  let WORD_POPCOUNT_WORD_OF_BITS ← prove
   r"!s. s SUBSET {i | i < dimindex(:N)}
       ==> word_popcount(word_of_bits s:N word) = CARD s"
   (REWRITE_TAC [WORD_POPCOUNT_WORD_OF_BITS_GEN] THEN
    MESON_TAC [SUBSET_INTER_ABSORPTION, INTER_COMM])

  let word_evenparity ← new_definition
   r"word_evenparity (x:N word) <=> EVEN(word_popcount x)"

  let word_oddparity ← new_definition
   r"word_oddparity (x:N word) <=> ODD(word_popcount x)"

  let NOT_WORD_EVENPARITY ← prove
   r"!x:N word. ~(word_evenparity x) <=> word_oddparity x"
   (REWRITE_TAC [word_evenparity, word_oddparity, NOT_EVEN])

  let NOT_WORD_ODDPARITY ← prove
   r"!x:N word. ~(word_oddparity x) <=> word_evenparity x"
   (REWRITE_TAC [word_evenparity, word_oddparity, NOT_ODD])

  let WORD_EVENPARITY_0 ← prove
   r"word_evenparity(word 0:N word)"
   (REWRITE_TAC [word_evenparity, WORD_POPCOUNT_0, EVEN])

  let WORD_ODDPARITY_0 ← prove
   r"~word_oddparity(word 0:N word)"
   (REWRITE_TAC [NOT_WORD_ODDPARITY, WORD_EVENPARITY_0])

  let WORD_EVENPARITY_1 ← prove
   r"~word_evenparity(word 1:N word)"
   (REWRITE_TAC [word_evenparity, WORD_POPCOUNT_1] THEN
    CONV_TAC NUM_REDUCE_CONV)

  let WORD_ODDPARITY_1 ← prove
   r"word_oddparity(word 1:N word)"
   (REWRITE_TAC [← GSYM NOT_WORD_EVENPARITY, WORD_EVENPARITY_1])

  return { word_popcount, HAS_SIZE_BITS_OF_WORD_POPCOUNT, WORD_POPCOUNT_BOUND,
           WORD_POPCOUNT_BOUND_SIZE, WORD_POPCOUNT_EQ_0, WORD_POPCOUNT_0,
           WORD_POPCOUNT_1, WORD_POPCOUNT_BITVAL, WORD_POPCOUNT_NSUM,
           WORD_POPCOUNT_LE_BITS, WORD_POPCOUNT_WORD_OF_BITS_GEN,
           WORD_POPCOUNT_WORD_OF_BITS, word_evenparity, word_oddparity,
           NOT_WORD_EVENPARITY, NOT_WORD_ODDPARITY, WORD_EVENPARITY_0,
           WORD_ODDPARITY_0, WORD_EVENPARITY_1, WORD_ODDPARITY_1 }

/- ------------------------------------------------------------------------- -/
/- Modular arithmetic operations in general, unsigned and signed;            -/
/- relational operations; bitwise operations.                                -/
/- ------------------------------------------------------------------------- -/

structure GeneralOps where
  modular : thm
  VAL_MODULAR : thm
  CONG_MODULAR : thm
  imodular : thm
  CONG_IMODULAR : thm
  relational2 : thm
  irelational2 : thm
  bitwise1 : thm
  bitwise2 : thm
  BIT_BITWISE1 : thm
  BIT_BITWISE2 : thm
  deriving Inhabited

@[nospecialize]
def setupGeneralOps [HolBase] (D : WordsDeps) (W : WordType) (Vl : Val) (Iv : Ival) :
    ExceptT String IO GeneralOps := do
  let { new_definition, ASM_ARITH_TAC, NUMBER_RULE, .. } := D
  let { CONG_LMOD, .. } := D.core1
  let { LAMBDA_BETA, .. } := D.core3
  let { word_tybij, bit, .. } := W
  let { VAL_WORD, .. } := Vl
  let { IVAL_IWORD_CONG, .. } := Iv

  let modular ← new_definition
   r"modular op (x:(N)word) (y:(N)word) = word(op (val x) (val y)):(N)word"

  let VAL_MODULAR ← prove
   r"!op x y:(N)word.
        val(modular op x y) = (op (val x) (val y)) MOD (2 EXP dimindex(:N))"
   (REWRITE_TAC [modular, VAL_WORD])

  let CONG_MODULAR ← prove
   r"!op x y:(N)word.
       (val(modular op x y) == op (val x) (val y))
       (mod (2 EXP dimindex(:N)))"
   (REWRITE_TAC [VAL_MODULAR, CONG_LMOD] THEN CONV_TAC (fun t => (NUMBER_RULE t).run))

  let imodular ← new_definition
   r"imodular op (x:(N)word) (y:(N)word) =
        iword(op (ival x) (ival y)):(N)word"

  let CONG_IMODULAR ← prove
   r"!op x y:(N)word.
       (ival(imodular op x y) == op (ival x) (ival y))
       (mod (&2 pow (dimindex(:N))))"
   (REWRITE_TAC [imodular, IVAL_IWORD_CONG])

  let relational2 ← new_definition
   r"relational2 r (x:(N)word) (y:(N)word) :bool = r (val x) (val y)"

  let irelational2 ← new_definition
   r"irelational2 r (x:(N)word) (y:(N)word) :bool = r (ival x) (ival y)"

  let bitwise1 ← new_definition
   r"(bitwise1 op:N word->N word) x = mk_word(lambda i. op(bitvector x$i))"

  let bitwise2 ← new_definition
   r"(bitwise2 op:N word->N word->N word) x y =
        mk_word(lambda i. op (bitvector x$i) (bitvector y$i))"

  let BIT_BITWISE1 ← prove
   r"!op (x:N word) k.
        bit k (bitwise1 op x) <=>
        k < dimindex(:N) /\ op(bit k x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [bit] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [bitwise1, word_tybij] THEN
    MATCH_MP_TAC LAMBDA_BETA THEN ASM_ARITH_TAC)

  let BIT_BITWISE2 ← prove
   r"!op (x:N word) (y:N word) k.
        bit k (bitwise2 op x y) <=>
        k < dimindex(:N) /\ op (bit k x) (bit k y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [bit] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [bitwise2, word_tybij] THEN
    MATCH_MP_TAC LAMBDA_BETA THEN ASM_ARITH_TAC)

  return { modular, VAL_MODULAR, CONG_MODULAR, imodular, CONG_IMODULAR, relational2,
           irelational2, bitwise1, bitwise2, BIT_BITWISE1, BIT_BITWISE2 }

/- ------------------------------------------------------------------------- -/
/- The main word operations. Where there is any meaningful difference        -/
/- between unsigned and signed we use a "u" or an "i" in the names.          -/
/- (words.ml 1938-2475: not, and, or, xor, add, sub, neg.)                   -/
/- ------------------------------------------------------------------------- -/

structure WordOps1 where
  word_not : thm
  BIT_WORD_NOT : thm
  BITS_OF_WORD_NOT : thm
  WORD_OF_BITS_DIFF : thm
  VAL_WORD_NOT : thm
  INT_VAL_WORD_NOT : thm
  REAL_VAL_WORD_NOT : thm
  WORD_POPCOUNT_NOT : thm
  word_and : thm
  BIT_WORD_AND : thm
  BIT_WORD_AND_ALT : thm
  BITS_OF_WORD_AND : thm
  WORD_AND_EQ_0 : thm
  WORD_OF_BITS_INTER : thm
  WORD_AND_WORD_OF_BITS_SING : thm
  WORD_OF_BITS_SING_AND_WORD : thm
  WORD_AND_POW2 : thm
  VAL_WORD_AND_POW2 : thm
  WORD_AND_POW2_BITVAL : thm
  VAL_WORD_AND_POW2_BITVAL : thm
  VAL_WORD_AND_LE : thm
  VAL_WORD_AND_LE_MIN : thm
  VAL_WORD_AND_WORD_LE : thm
  WORD_POPCOUNT_AND : thm
  word_or : thm
  BIT_WORD_OR : thm
  BIT_WORD_OR_ALT : thm
  BITS_OF_WORD_OR : thm
  WORD_OF_BITS_UNION : thm
  VAL_WORD_OR_LE : thm
  VAL_WORD_OR_LE_MAX : thm
  WORD_POPCOUNT_OR : thm
  WORD_POPCOUNT_OR_DISJOINT : thm
  word_xor : thm
  BIT_WORD_XOR : thm
  BIT_WORD_XOR_ALT : thm
  VAL_WORD_ADD_AND_XOR : thm
  VAL_WORD_ADD_AND_OR : thm
  VAL_WORD_OR_DISJOINT : thm
  VAL_WORD_OR_AND_XOR : thm
  REAL_VAL_WORD_XOR : thm
  word_add : thm
  VAL_WORD_ADD : thm
  VAL_WORD_ADD_CASES : thm
  VAL_WORD_ADC_CASES : thm
  INT_VAL_WORD_ADD_CASES : thm
  CONG_WORD_ADD : thm
  INT_CONG_WORD_ADD : thm
  WORD_ADD : thm
  ICONG_WORD_ADD : thm
  IWORD_INT_ADD : thm
  WORD_ADD_IMODULAR : thm
  ODD_VAL_WORD : thm
  EVEN_VAL_WORD : thm
  ODD_VAL_WORD_ADD : thm
  EVEN_VAL_WORD_ADD : thm
  word_sub : thm
  VAL_WORD_SUB : thm
  VAL_WORD_SUB_CASES : thm
  INT_VAL_WORD_SUB_CASES : thm
  CONG_WORD_SUB : thm
  INT_CONG_WORD_SUB : thm
  INT_VAL_WORD_SUB : thm
  ICONG_WORD_SUB : thm
  IWORD_INT_SUB : thm
  WORD_SUB_IMODULAR : thm
  WORD_SUB : thm
  word_neg : thm
  ODD_VAL_WORD_SUB : thm
  EVEN_VAL_WORD_SUB : thm
  VAL_WORD_NEG : thm
  VAL_WORD_NEG_CASES : thm
  INT_VAL_WORD_NEG_CASES : thm
  REAL_VAL_WORD_NEG_CASES : thm
  INT_VAL_WORD_NEG : thm
  REAL_VAL_WORD_NEG : thm
  CONG_WORD_NEG : thm
  INT_CONG_WORD_NEG : thm
  ICONG_WORD_NEG : thm
  IWORD_INT_NEG : thm
  WORD_NEG_AS_ADD : thm
  deriving Inhabited

@[nospecialize]
def setupWordOps1 [HolBase] (D : WordsDeps) (BBitval : Bitval) (BWordType : WordType) (BBitsOfWord : BitsOfWord) (BVal : Val) (BIval : Ival) (BPopcount : Popcount) (BGeneralOps : GeneralOps) :
    ExceptT String IO WordOps1 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, INTEGER_RULE,
        INT_ARITH_TAC, MESON_TAC, MOD_DOWN_CONV, NUMBER_RULE, NUM_REDUCE_CONV,
        REAL_ARITH_TAC, SET_RULE, SET_TAC, new_definition, .. } := D
  let { ADD_ASSOC, ADD_CLAUSES, AND_FORALL_THM, ARITH, CARD_NUMSEG_LT, CARD_UNION,
        CARD_UNION_EQ, CARD_UNION_LE, CONG, DIMINDEX_NONZERO, DISJOINT_EMPTY, EVEN_EXP,
        EXP, EXP_LT_0, EXTENSION, .. } := D.core1
  let { FINITE_NUMSEG_LT, FUN_EQ_THM, INT_OF_NUM_ADD, INT_OF_NUM_CLAUSES,
        INT_OF_NUM_EQ, INT_OF_NUM_LE, INT_OF_NUM_LT, INT_OF_NUM_POW, INT_OF_NUM_REM,
        INT_OF_NUM_SUB, INT_REM_EQ, INT_SUB_LZERO, IN_ELIM_THM, IN_INTER, IN_UNION, .. } := D.core2
  let { LE, LEFT_ADD_DISTRIB, LE_CASES, LE_MULT_LCANCEL, LE_REFL, LE_TRANS, LT_EXP,
        LT_IMP_LE, MOD_ADD_CASES, MOD_CASES, MOD_LT, MOD_MOD_REFL, MOD_UNIQ,
        MULT_CLAUSES, NOT_LE, NOT_LT, NOT_ODD, NSUM_ADD, NSUM_CLAUSES_NUMSEG_LT,
        NSUM_EQ, NSUM_LE, NSUM_LMUL, ODD_ADD, ODD_EXP, ODD_MOD_EVEN, ODD_SUB, .. } := D.core3
  let { REAL_OF_NUM_ADD, REAL_OF_NUM_CLAUSES, REAL_OF_NUM_EQ, REAL_OF_NUM_POW,
        REAL_OF_NUM_SUB, SUBSET, SUB_ADD, SUB_EQ_0, SUB_REFL, num_congruent, .. } := D.core4
  let { BITVAL_BOUND, BITVAL_CLAUSES, BITVAL_NOT, LE_BITVAL, bitval, .. } := BBitval
  let { BIT_TRIVIAL, WORD_EQ_BITS, .. } := BWordType
  let { BITS_OF_WORD_EQ, BITS_OF_WORD_OF_BITS, BIT_WORD_OF_BITS, FINITE_BITS_OF_WORD,
        bits_of_word, .. } := BBitsOfWord
  let { BITS_OF_WORD_0, BITS_OF_WORD_EQ_EMPTY, BIT_WORD_0, BIT_WORD_POW2, VAL_BOUND,
        VAL_CONG, VAL_EQ_0, VAL_LE_BITS, VAL_MOD_REFL, VAL_WORD, VAL_WORD_0,
        VAL_WORD_1, VAL_WORD_CONG, VAL_WORD_EQ, VAL_WORD_LE, val_def, .. } := BVal
  let { IVAL_CONG, IVAL_IWORD_CONG, IVAL_VAL_CONG, IVAL_WORD_0, WORD_IWORD, .. } := BIval
  let { WORD_POPCOUNT_LE_BITS, word_popcount, .. } := BPopcount
  let { BIT_BITWISE1, BIT_BITWISE2, CONG_IMODULAR, CONG_MODULAR, VAL_MODULAR, .. } := BGeneralOps
  -- @@SCOPE END

  let word_not ← new_definition
   r"word_not = bitwise1 (~)"

  let BIT_WORD_NOT ← prove
   r"!(x:N word) k. bit k (word_not x) <=> k < dimindex(:N) /\ ~bit k x"
   (REWRITE_TAC [word_not, BIT_BITWISE1])

  let BITS_OF_WORD_NOT ← prove
   r"!w:N word. bits_of_word(word_not w) =
              {i | i < dimindex(:N)} DIFF bits_of_word w"
   (REWRITE_TAC [bits_of_word, BIT_WORD_NOT] THEN SET_TAC [])

  let WORD_OF_BITS_DIFF ← prove
   r"!s t. {i | i < dimindex(:N)} SUBSET s
         ==> word_of_bits(s DIFF t):N word = word_not(word_of_bits t)"
   (REWRITE_TAC [← GSYM BITS_OF_WORD_EQ, BITS_OF_WORD_NOT] THEN
    REWRITE_TAC [BITS_OF_WORD_OF_BITS] THEN SET_TAC [])

  let VAL_WORD_NOT ← prove
   r"!w:N word. val(word_not w) = 2 EXP dimindex(:N) - 1 - val w"
   (GEN_TAC THEN
    MATCH_MP_TAC (← ARITH_RULE (← q r"(m + n) + 1 = p ==> m = p - 1 - n")) THEN
    SIMP_TAC [val_def, ← GSYM NSUM_ADD, FINITE_NUMSEG_LT] THEN
    SIMP_TAC [← GSYM LEFT_ADD_DISTRIB, BIT_WORD_NOT] THEN
    SIMP_TAC [BITVAL_NOT, BITVAL_BOUND, SUB_ADD, MULT_CLAUSES] THEN
    SPEC_TAC (← q "dimindex(:N)", ← q "k:num") THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [NSUM_CLAUSES_NUMSEG_LT, EXP, ADD_CLAUSES, MULT_CLAUSES] THEN
    ASM_ARITH_TAC)

  let INT_VAL_WORD_NOT ← prove
   r"!x:N word. &(val(word_not x)):int = &2 pow dimindex(:N) - &1 - &(val x)"
   (GEN_TAC THEN
    REWRITE_TAC [VAL_WORD_NOT, ← ARITH_RULE (← q r"n - 1 - m = n - (m + 1)")] THEN
    W (MP_TAC o PART_MATCH (rand o rand) INT_OF_NUM_SUB o lhand o snd) THEN
    REWRITE_TAC [VAL_BOUND, ← ARITH_RULE (← q r"x + 1 <= n <=> x < n")] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [← GSYM INT_OF_NUM_ADD, ← GSYM INT_OF_NUM_POW] THEN
    INT_ARITH_TAC)

  let REAL_VAL_WORD_NOT ← prove
   r"!x:N word. &(val(word_not x)):real = &2 pow dimindex(:N) - &1 - &(val x)"
   (GEN_TAC THEN
    REWRITE_TAC [VAL_WORD_NOT, ← ARITH_RULE (← q r"n - 1 - m = n - (m + 1)")] THEN
    W (MP_TAC o PART_MATCH (rand o rand) REAL_OF_NUM_SUB o lhand o snd) THEN
    REWRITE_TAC [VAL_BOUND, ← ARITH_RULE (← q r"x + 1 <= n <=> x < n")] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_ADD, ← GSYM REAL_OF_NUM_POW] THEN
    REAL_ARITH_TAC)

  let WORD_POPCOUNT_NOT ← prove
   r"!x:N word. word_popcount(word_not x) = dimindex(:N) - word_popcount x"
   (GEN_TAC THEN MATCH_MP_TAC (← ARITH_RULE
     (← q r"x + y:num = z ==> x = z - y")) THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM CARD_NUMSEG_LT] THEN
    REWRITE_TAC [word_popcount] THEN MATCH_MP_TAC CARD_UNION_EQ THEN
    REWRITE_TAC [FINITE_NUMSEG_LT, BITS_OF_WORD_NOT] THEN
    CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
    REWRITE_TAC [← SET_RULE (← q r"s DIFF t UNION t = s <=> t SUBSET s")] THEN
    REWRITE_TAC [bits_of_word, SUBSET, IN_ELIM_THM] THEN
    MESON_TAC [BIT_TRIVIAL, NOT_LT])

  let word_and ← new_definition
   r"word_and = bitwise2 (/\)"

  let BIT_WORD_AND ← prove
   r"!(x:N word) (y:N word) k.
        bit k (word_and x y) <=>
        k < dimindex(:N) /\ bit k x /\ bit k y"
   (REWRITE_TAC [word_and, BIT_BITWISE2])

  let BIT_WORD_AND_ALT ← prove
   r"!(x:N word) y k. bit k (word_and x y) <=> bit k x /\ bit k y"
   (MESON_TAC [BIT_WORD_AND, BIT_TRIVIAL, NOT_LT])

  let BITS_OF_WORD_AND ← prove
   r"!v w:N word.
        bits_of_word(word_and v w) = bits_of_word v INTER bits_of_word w"
   (REWRITE_TAC [bits_of_word, BIT_WORD_AND] THEN
    REWRITE_TAC [EXTENSION, IN_INTER, IN_ELIM_THM] THEN
    MESON_TAC [BIT_TRIVIAL, NOT_LE])

  let WORD_AND_EQ_0 ← prove
   r"!v w:N word.
        word_and v w = word 0 <=> DISJOINT (bits_of_word v) (bits_of_word w)"
   (REWRITE_TAC [← GSYM BITS_OF_WORD_EQ, BITS_OF_WORD_AND, BITS_OF_WORD_0] THEN
    SET_TAC [])

  let WORD_OF_BITS_INTER ← prove
   r"!s t. word_of_bits(s INTER t):N word =
         word_and (word_of_bits s) (word_of_bits t)"
   (REWRITE_TAC [← GSYM BITS_OF_WORD_EQ, BITS_OF_WORD_AND] THEN
    REWRITE_TAC [BITS_OF_WORD_OF_BITS] THEN SET_TAC [])

  let WORD_AND_WORD_OF_BITS_SING ← prove
   r"!(w:N word) k.
        word_and w (word_of_bits {k}) =
        if bit k w then word_of_bits {k} else word 0"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [WORD_EQ_BITS, BIT_WORD_AND, BIT_WORD_OF_BITS, BIT_WORD_0] THEN
    ASM SET_TAC [])

  let WORD_OF_BITS_SING_AND_WORD ← prove
   r"!(w:N word) k.
        word_and (word_of_bits {k}) w =
        if bit k w then word_of_bits {k} else word 0"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [WORD_EQ_BITS, BIT_WORD_AND, BIT_WORD_OF_BITS, BIT_WORD_0] THEN
    ASM SET_TAC [])

  let WORD_AND_POW2 ← prove
   r"(!(x:N word) k.
        word_and x (word(2 EXP k)) = word(2 EXP k * bitval(bit k x))) /\
   (!(x:N word) k.
        word_and (word(2 EXP k)) x = word(2 EXP k * bitval(bit k x)))"
   (REWRITE_TAC [AND_FORALL_THM, bitval] THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN
    REWRITE_TAC [WORD_EQ_BITS, BIT_WORD_AND, BIT_WORD_POW2, BIT_WORD_0] THEN
    ASM_MESON_TAC [])

  let VAL_WORD_AND_POW2 ← prove
   r"(!(x:N word) k.
        val(word_and x (word(2 EXP k))) = 2 EXP k * bitval(bit k x)) /\
   (!(x:N word) k.
        val(word_and (word(2 EXP k)) x) = 2 EXP k * bitval(bit k x))"
   (REWRITE_TAC [WORD_AND_POW2] THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC [bitval] THEN
    COND_CASES_TAC THEN REWRITE_TAC [MULT_CLAUSES, LT_EXP, EXP_LT_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC [BIT_TRIVIAL, NOT_LE])

  let WORD_AND_POW2_BITVAL ← prove
   r"(!(x:N word) k b.
        word_and x (word(2 EXP k * bitval b)) =
        word(2 EXP k * bitval(bit k x /\ b))) /\
   (!(x:N word) k b.
        word_and (word(2 EXP k * bitval b)) x =
        word(2 EXP k * bitval(b /\ bit k x)))"
   (REPEAT STRIP_TAC THEN BOOL_CASES_TAC (← q "b:bool") THEN
    ASM_REWRITE_TAC [BITVAL_CLAUSES, MULT_CLAUSES] THEN
    REWRITE_TAC [WORD_AND_POW2, WORD_AND_EQ_0, BITS_OF_WORD_0] THEN
    REWRITE_TAC [DISJOINT_EMPTY])

  let VAL_WORD_AND_POW2_BITVAL ← prove
   r"(!(x:N word) k b.
        val(word_and x (word(2 EXP k * bitval b))) =
        2 EXP k * bitval(bit k x /\ b)) /\
   (!(x:N word) k b.
        val(word_and (word(2 EXP k * bitval b)) x) =
        2 EXP k * bitval(b /\ bit k x))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [WORD_AND_POW2_BITVAL] THEN
    MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC [bitval] THEN
    COND_CASES_TAC THEN REWRITE_TAC [MULT_CLAUSES, LT_EXP, EXP_LT_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC [BIT_TRIVIAL, NOT_LE])

  let VAL_WORD_AND_LE ← prove
   r"(!x y:N word. val(word_and x y) <= val x) /\
   (!x y:N word. val(word_and x y) <= val y)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [val_def] THEN MATCH_MP_TAC NSUM_LE THEN
    REWRITE_TAC [FINITE_NUMSEG_LT] THEN X_GEN_TAC (← q "i:num") THEN
    SIMP_TAC [IN_ELIM_THM, BIT_WORD_AND, LE_MULT_LCANCEL, LE_BITVAL])

  let VAL_WORD_AND_LE_MIN ← prove
   r"!x y:N word. val(word_and x y) <= MIN (val x) (val y)"
   (REWRITE_TAC [← ARITH_RULE (← q r"x <= MIN y z <=> x <= y /\ x <= z")] THEN
    REWRITE_TAC [VAL_WORD_AND_LE])

  let VAL_WORD_AND_WORD_LE ← prove
   r"(!(x:N word) n. val(word_and x (word n)) <= n) /\
   (!(x:N word) n. val(word_and (word n) x) <= n)"
   (MESON_TAC [VAL_WORD_AND_LE, LE_TRANS, LE_REFL, VAL_WORD_LE])

  let WORD_POPCOUNT_AND ← prove
   r"!x y:N word.
      word_popcount(word_and x y) <= MIN (word_popcount x) (word_popcount y)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [← ARITH_RULE (← q r"x <= MIN a b <=> x <= a /\ x <= b")] THEN
    CONJ_TAC THEN MATCH_MP_TAC WORD_POPCOUNT_LE_BITS THEN
    SIMP_TAC [BIT_WORD_AND])

  let word_or ← new_definition
   r"word_or = bitwise2 (\/)"

  let BIT_WORD_OR ← prove
   r"!(x:N word) (y:N word) k.
        bit k (word_or x y) <=>
        k < dimindex(:N) /\ (bit k x \/ bit k y)"
   (REWRITE_TAC [word_or, BIT_BITWISE2])

  let BIT_WORD_OR_ALT ← prove
   r"!(x:N word) y k. bit k (word_or x y) <=> bit k x \/ bit k y"
   (MESON_TAC [BIT_WORD_OR, BIT_TRIVIAL, NOT_LT])

  let BITS_OF_WORD_OR ← prove
   r"!v w:N word.
        bits_of_word(word_or v w) = bits_of_word v UNION bits_of_word w"
   (REWRITE_TAC [bits_of_word, BIT_WORD_OR] THEN
    REWRITE_TAC [EXTENSION, IN_UNION, IN_ELIM_THM] THEN
    MESON_TAC [BIT_TRIVIAL, NOT_LE])

  let WORD_OF_BITS_UNION ← prove
   r"!s t. word_of_bits(s UNION t):N word =
         word_or (word_of_bits s) (word_of_bits t)"
   (REWRITE_TAC [← GSYM BITS_OF_WORD_EQ, BITS_OF_WORD_OR] THEN
    REWRITE_TAC [BITS_OF_WORD_OF_BITS] THEN SET_TAC [])

  let VAL_WORD_OR_LE ← prove
   r"(!x y:N word. val x <= val(word_or x y)) /\
   (!x y:N word. val y <= val(word_or x y))"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_LE_BITS THEN
    SIMP_TAC [BIT_WORD_OR])

  let VAL_WORD_OR_LE_MAX ← prove
   r"(!x y:N word. MAX (val x) (val y) <= val(word_or x y))"
   (REWRITE_TAC [← ARITH_RULE (← q r"MAX y z <= x <=> y <= x /\ z <= x")] THEN
    REWRITE_TAC [VAL_WORD_OR_LE])

  let WORD_POPCOUNT_OR ← prove
   r"!x y:N word.
      word_popcount(word_or x y) <= word_popcount x + word_popcount y"
   (REWRITE_TAC [word_popcount, BITS_OF_WORD_OR] THEN
    SIMP_TAC [CARD_UNION_LE, FINITE_BITS_OF_WORD])

  let WORD_POPCOUNT_OR_DISJOINT ← prove
   r"!x y:N word.
        word_and x y = word 0
        ==> word_popcount(word_or x y) = word_popcount x + word_popcount y"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM BITS_OF_WORD_EQ_EMPTY] THEN
    SIMP_TAC [word_popcount, BITS_OF_WORD_OR, BITS_OF_WORD_AND,
              CARD_UNION, FINITE_BITS_OF_WORD])

  let word_xor ← new_definition
   r"word_xor = bitwise2 (\x y. ~(x <=> y))"

  let BIT_WORD_XOR ← prove
   r"!(x:N word) (y:N word) k.
        bit k (word_xor x y) <=>
        k < dimindex(:N) /\ ~(bit k x <=> bit k y)"
   (REWRITE_TAC [word_xor, BIT_BITWISE2])

  let BIT_WORD_XOR_ALT ← prove
   r"!(x:N word) y k. bit k (word_xor x y) <=> ~(bit k x <=> bit k y)"
   (MESON_TAC [BIT_WORD_XOR, BIT_TRIVIAL, NOT_LT])

  let (VAL_WORD_ADD_AND_XOR, VAL_WORD_ADD_AND_OR) ← CONJ_PAIR (← prove
   r"(!x y:N word. val x + val y = 2 * val(word_and x y) + val(word_xor x y)) /\
   (!x y:N word. val x + val y = val(word_and x y) + val(word_or x y))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [val_def, ← GSYM NSUM_LMUL] THEN
    SIMP_TAC [← GSYM NSUM_ADD, FINITE_NUMSEG_LT] THEN MATCH_MP_TAC NSUM_EQ THEN
    REWRITE_TAC [IN_ELIM_THM, BIT_WORD_AND, BIT_WORD_XOR, BIT_WORD_OR] THEN
    X_GEN_TAC (← q "i:num") THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    MAP_EVERY ASM_CASES_TAC [← q "bit i (x:N word)", ← q "bit i (y:N word)"] THEN
    ASM_REWRITE_TAC [BITVAL_CLAUSES] THEN ARITH_TAC))

  let VAL_WORD_OR_DISJOINT ← prove
   r"!x y:N word.
        word_and x y = word 0 ==> val(word_or x y) = val x + val y"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [VAL_WORD_ADD_AND_OR] THEN
    ASM_REWRITE_TAC [VAL_WORD_0, ADD_CLAUSES])

  let VAL_WORD_OR_AND_XOR ← prove
   r"!x y:N word. val(word_or x y) = val(word_and x y) + val(word_xor x y)"
   (ONCE_REWRITE_TAC [← ARITH_RULE (← q r"a = b + c <=> b + a = 2 * b + c")] THEN
    MESON_TAC [VAL_WORD_ADD_AND_XOR, VAL_WORD_ADD_AND_OR])

  let REAL_VAL_WORD_XOR ← prove
   r"!x y:N word. &(val(word_xor x y)):real =
                (&(val x) + &(val y)) - &2 * &(val(word_and x y))"
   (REWRITE_TAC [REAL_OF_NUM_CLAUSES, VAL_WORD_ADD_AND_XOR] THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC)

  let word_add ← new_definition
   r"word_add = modular (+)"

  let VAL_WORD_ADD ← prove
   r"!x y:(N) word.
        val(word_add x y) = (val(x) + val(y)) MOD (2 EXP dimindex(:N))"
   (REWRITE_TAC [word_add, VAL_MODULAR])

  let VAL_WORD_ADD_CASES ← prove
   r"!x y:(N) word.
        val(word_add x y) =
        if val x + val y < 2 EXP dimindex(:N) then val x + val y
        else (val x + val y) - 2 EXP dimindex(:N)"
   (SIMP_TAC [VAL_WORD_ADD, VAL_BOUND, MOD_ADD_CASES])

  let VAL_WORD_ADC_CASES ← prove
   r"!c x y:(N) word.
        val(c) < 2
        ==> val(word_add (word_add x y) c) =
            if val x + val y + val c < 2 EXP dimindex(:N)
            then val x + val y + val c
            else (val x + val y + val c) - 2 EXP dimindex(:N)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [VAL_WORD_ADD] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC [← GSYM ADD_ASSOC] THEN
    MATCH_MP_TAC MOD_CASES THEN MATCH_MP_TAC (← ARITH_RULE
     (← q r"x < n /\ y < n /\ c < 2 ==> x + y + c < 2 * n")) THEN
    ASM_REWRITE_TAC [VAL_BOUND])

  let INT_VAL_WORD_ADD_CASES ← prove
   r"!x y:(N) word.
      &(val(word_add x y)):int =
      if &(val x) + &(val y):int < &2 pow dimindex(:N) then &(val x) + &(val y)
      else (&(val x) + &(val y)) - &2 pow dimindex(:N)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [VAL_WORD_ADD_CASES] THEN
    REWRITE_TAC [INT_OF_NUM_ADD, INT_OF_NUM_POW, INT_OF_NUM_LT] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [NOT_LT, INT_OF_NUM_SUB])

  let CONG_WORD_ADD ← prove
   r"!x y:(N)word.
        (val(word_add x y) == val x + val y) (mod (2 EXP dimindex(:N)))"
   (REWRITE_TAC [word_add, CONG_MODULAR])

  let INT_CONG_WORD_ADD ← prove
   r"!x y:N word.
    (&(val(word_add x y)):int == &(val x) + &(val y))
    (mod (&2 pow dimindex(:N)))"
   (REWRITE_TAC [INT_OF_NUM_CLAUSES, ← GSYM num_congruent, CONG_WORD_ADD])

  let WORD_ADD ← prove
   r"!x y. word(x + y):N word = word_add (word x) (word y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM VAL_CONG] THEN
    MP_TAC (← ISPECL [← q "word x:N word", ← q "word y:N word"] CONG_WORD_ADD) THEN
    MAP_EVERY (MP_TAC o (fun t => ISPEC t VAL_WORD_CONG))
     [← q "x + y:num", ← q "y:num", ← q "x:num"] THEN
    CONV_TAC (fun t => (NUMBER_RULE t).run))

  let ICONG_WORD_ADD ← prove
   r"!x y:(N)word.
        (ival(word_add x y) == ival x + ival y) (mod (&2 pow dimindex(:N)))"
   (REPEAT GEN_TAC THEN MAP_EVERY (MP_TAC o (fun t => SPEC t IVAL_VAL_CONG))
     [← q "x:N word", ← q "y:N word", ← q "word_add x y:N word"] THEN
    MP_TAC (← ISPECL [← q "x:N word", ← q "y:N word"] CONG_WORD_ADD) THEN
    REWRITE_TAC [num_congruent, ← GSYM INT_OF_NUM_POW, ← GSYM INT_OF_NUM_ADD] THEN
    CONV_TAC (fun t => (INTEGER_RULE t).run))

  let IWORD_INT_ADD ← prove
   r"!x y. iword(x + y):N word = word_add (iword x) (iword y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM IVAL_CONG] THEN
    MP_TAC (← ISPECL [← q "iword x:N word", ← q "iword y:N word"] ICONG_WORD_ADD) THEN
    MAP_EVERY (MP_TAC o (fun t => ISPEC t IVAL_IWORD_CONG))
     [← q "x + y:int", ← q "y:int", ← q "x:int"] THEN
    CONV_TAC (fun t => (INTEGER_RULE t).run))

  let WORD_ADD_IMODULAR ← prove
   r"(word_add:N word->N word->N word) = imodular ( + )"
   (REWRITE_TAC [FUN_EQ_THM, ← GSYM IVAL_CONG] THEN
    ASM_MESON_TAC [ICONG_WORD_ADD, CONG_IMODULAR, ← INTEGER_RULE
     (← q r"(a:int == b) (mod n) /\ (c == b) (mod n) ==> (a == c) (mod n)")])

  let ODD_VAL_WORD ← prove
   r"!n. ODD(val(word n:N word)) <=> ODD n"
   (SIMP_TAC [VAL_WORD, ODD_MOD_EVEN, EVEN_EXP, ARITH, DIMINDEX_NONZERO])

  let EVEN_VAL_WORD ← prove
   r"!n. EVEN(val(word n:N word)) <=> EVEN n"
   (REWRITE_TAC [← GSYM NOT_ODD, ODD_VAL_WORD])

  let ODD_VAL_WORD_ADD ← prove
   r"!x y:N word. ODD(val(word_add x y)) <=> ~(ODD(val x) <=> ODD(val y))"
   (SIMP_TAC [VAL_WORD_ADD, ODD_MOD_EVEN, EVEN_EXP, ARITH, DIMINDEX_NONZERO] THEN
    REWRITE_TAC [ODD_ADD])

  let EVEN_VAL_WORD_ADD ← prove
   r"!x y:N word. EVEN(val(word_add x y)) <=> (EVEN(val x) <=> EVEN(val y))"
   (REWRITE_TAC [← GSYM NOT_ODD, ODD_VAL_WORD_ADD] THEN CONV_TAC (fun t => (TAUT t).run))

  let word_sub ← new_definition
   r"(word_sub:(N)word->(N)word->(N)word) =
        modular (\x y. x + (2 EXP dimindex(:N) - y))"

  let VAL_WORD_SUB ← prove
   r"!x y:(N) word.
        val(word_sub x y) =
        (val(x) + (2 EXP dimindex(:N) - val(y))) MOD (2 EXP dimindex(:N))"
   (REWRITE_TAC [word_sub, VAL_MODULAR])

  let VAL_WORD_SUB_CASES ← prove
   r"!x y:(N) word.
        val(word_sub x y) =
        if val y <= val x then val(x) - val(y)
        else val(x) + (2 EXP dimindex(:N) - val(y))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [VAL_WORD_SUB] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [MOD_LT] THENL
     [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC (← q "1"),
      MATCH_MP_TAC MOD_LT] THEN
    MAP_EVERY (MP_TAC o (fun t => ISPEC t VAL_BOUND)) [← q "x:N word", ← q "y:N word"] THEN
    ASM_ARITH_TAC)

  let INT_VAL_WORD_SUB_CASES ← prove
   r"!x y:(N) word.
        &(val(word_sub x y)):int =
        if &(val y):int <= &(val x) then &(val x) - &(val y)
        else &(val x) + (&2 pow dimindex(:N) - &(val y))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [VAL_WORD_SUB_CASES] THEN
    REWRITE_TAC [INT_OF_NUM_ADD, INT_OF_NUM_POW, INT_OF_NUM_LE] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [INT_OF_NUM_ADD, INT_OF_NUM_SUB, VAL_BOUND, LT_IMP_LE])

  let CONG_WORD_SUB ← prove
   r"!x y:(N)word.
        (val(word_sub x y) + val y == val x) (mod (2 EXP dimindex(:N)))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [CONG, VAL_MODULAR, word_sub] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    SIMP_TAC [VAL_BOUND, ← ARITH_RULE (← q r"y:num < n ==> (x + n - y) + y = x + n")] THEN
    REWRITE_TAC [← GSYM CONG] THEN CONV_TAC (fun t => (NUMBER_RULE t).run))

  let INT_CONG_WORD_SUB ← prove
   r"!x y:N word.
    (&(val(word_sub x y)):int == &(val x) - &(val y))
    (mod (&2 pow dimindex(:N)))"
   (REWRITE_TAC [← INTEGER_RULE
     (← q r"(z:int == x - y) (mod n) <=> (z + y == x) (mod n)")] THEN
    REWRITE_TAC [INT_OF_NUM_CLAUSES, CONG_WORD_SUB, ← GSYM num_congruent])

  let INT_VAL_WORD_SUB ← prove
   r"!x y:N word.
        &(val(word_sub x y:N word)):int =
        (&(val x) - &(val y)) rem &2 pow dimindex(:N)"
   (REWRITE_TAC [← GSYM (← REWRITE_RULE [← GSYM INT_REM_EQ] INT_CONG_WORD_SUB)] THEN
    REWRITE_TAC [INT_OF_NUM_CLAUSES, INT_OF_NUM_REM, VAL_MOD_REFL])

  let ICONG_WORD_SUB ← prove
   r"!x y:N word.
        (ival(word_sub x y) == ival x - ival y) (mod (&2 pow dimindex(:N)))"
   (REPEAT GEN_TAC THEN MAP_EVERY (MP_TAC o (fun t => SPEC t IVAL_VAL_CONG))
     [← q "x:N word", ← q "y:N word", ← q "word_sub x y:N word"] THEN
    MP_TAC (← ISPECL [← q "x:N word", ← q "y:N word"] CONG_WORD_SUB) THEN
    REWRITE_TAC [num_congruent, ← GSYM INT_OF_NUM_POW, ← GSYM INT_OF_NUM_ADD] THEN
    CONV_TAC (fun t => (INTEGER_RULE t).run))

  let IWORD_INT_SUB ← prove
   r"!x y. iword(x - y):N word = word_sub (iword x) (iword y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM IVAL_CONG] THEN
    MP_TAC (← ISPECL [← q "iword x:N word", ← q "iword y:N word"] ICONG_WORD_SUB) THEN
    MAP_EVERY (MP_TAC o (fun t => ISPEC t IVAL_IWORD_CONG))
     [← q "x - y:int", ← q "y:int", ← q "x:int"] THEN
    CONV_TAC (fun t => (INTEGER_RULE t).run))

  let WORD_SUB_IMODULAR ← prove
   r"(word_sub:N word->N word->N word) = imodular ( - )"
   (REWRITE_TAC [FUN_EQ_THM, ← GSYM IVAL_CONG] THEN
    ASM_MESON_TAC [ICONG_WORD_SUB, CONG_IMODULAR, ← INTEGER_RULE
     (← q r"(a:int == b) (mod n) /\ (c == b) (mod n) ==> (a == c) (mod n)")])

  let WORD_SUB ← prove
   r"!x y. word(x - y):N word =
         if y <= x then word_sub (word x) (word y) else word 0"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THENL
     [ASM_SIMP_TAC [WORD_IWORD, ← GSYM INT_OF_NUM_SUB, IWORD_INT_SUB],
      ASM_MESON_TAC [SUB_EQ_0, LE_CASES]])

  let word_neg ← new_definition
   r"word_neg (a:N word) = word_sub (word 0) a"

  let ODD_VAL_WORD_SUB ← prove
   r"!x y:N word. ODD(val(word_sub x y)) <=> ~(ODD(val x) <=> ODD(val y))"
   (SIMP_TAC [VAL_WORD_SUB, ODD_MOD_EVEN, EVEN_EXP, ARITH, DIMINDEX_NONZERO] THEN
    REWRITE_TAC [ODD_ADD, ODD_SUB, ODD_EXP, DIMINDEX_NONZERO, ARITH] THEN
    REWRITE_TAC [VAL_BOUND])

  let EVEN_VAL_WORD_SUB ← prove
   r"!x y:N word. EVEN(val(word_sub x y)) <=> (EVEN(val x) <=> EVEN(val y))"
   (REWRITE_TAC [← GSYM NOT_ODD, ODD_VAL_WORD_SUB] THEN CONV_TAC (fun t => (TAUT t).run))

  let VAL_WORD_NEG ← prove
   r"!x:(N) word.
        val(word_neg x) =
        (2 EXP dimindex(:N) - val(x)) MOD (2 EXP dimindex(:N))"
   (REWRITE_TAC [word_neg, VAL_WORD_SUB, VAL_WORD_0, ADD_CLAUSES])

  let VAL_WORD_NEG_CASES ← prove
   r"!x:(N) word.
        val(word_neg x) =
        if val x = 0 then 0 else 2 EXP dimindex(:N) - val(x)"
   (REWRITE_TAC [word_neg, VAL_WORD_SUB_CASES, VAL_WORD_0] THEN
    SIMP_TAC [LE, ADD_CLAUSES, SUB_REFL])

  let INT_VAL_WORD_NEG_CASES ← prove
   r"!x:N word.
        &(val(word_neg x)):int =
        if &(val x):int = &0 then &0 else &2 pow dimindex(:N) - &(val x)"
   (SIMP_TAC [INT_OF_NUM_POW, INT_OF_NUM_SUB, LT_IMP_LE, VAL_BOUND] THEN
    REWRITE_TAC [VAL_WORD_NEG_CASES, INT_OF_NUM_EQ] THEN MESON_TAC [])

  let REAL_VAL_WORD_NEG_CASES ← prove
   r"!x:N word.
        &(val(word_neg x)):real =
        if &(val x):real = &0 then &0 else &2 pow dimindex(:N) - &(val x)"
   (SIMP_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_SUB, LT_IMP_LE, VAL_BOUND] THEN
    REWRITE_TAC [VAL_WORD_NEG_CASES, REAL_OF_NUM_EQ] THEN MESON_TAC [])

  let INT_VAL_WORD_NEG ← prove
   r"!x:N word. &(val(word_neg x)):int =
              &2 pow dimindex(:N) * &(bitval(~(x = word 0))) -
              &(val x)"
   (GEN_TAC THEN REWRITE_TAC [INT_VAL_WORD_NEG_CASES] THEN
    REWRITE_TAC [INT_OF_NUM_EQ, VAL_EQ_0] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [BITVAL_CLAUSES, VAL_WORD_0] THEN
    INT_ARITH_TAC)

  let REAL_VAL_WORD_NEG ← prove
   r"!x:N word. &(val(word_neg x)):real =
              &2 pow dimindex(:N) * &(bitval(~(x = word 0))) -
              &(val x)"
   (GEN_TAC THEN REWRITE_TAC [REAL_VAL_WORD_NEG_CASES] THEN
    REWRITE_TAC [REAL_OF_NUM_EQ, VAL_EQ_0] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [BITVAL_CLAUSES, VAL_WORD_0] THEN
    REAL_ARITH_TAC)

  let CONG_WORD_NEG ← prove
   r"!x:(N)word.
        (val(word_neg x) + val x == 0) (mod (2 EXP dimindex(:N)))"
   (REWRITE_TAC [word_neg] THEN MESON_TAC [CONG_WORD_SUB, VAL_WORD_0])

  let INT_CONG_WORD_NEG ← prove
   r"!x:N word. (&(val(word_neg x)):int == -- &(val x))
              (mod (&2 pow dimindex(:N)))"
   (REWRITE_TAC [← INTEGER_RULE
     (← q r"(z:int == --y) (mod n) <=> (z + y == &0) (mod n)")] THEN
    REWRITE_TAC [INT_OF_NUM_CLAUSES, CONG_WORD_NEG, ← GSYM num_congruent])

  let ICONG_WORD_NEG ← prove
   r"!x:(N)word.
        (ival(word_neg x) == --(ival x)) (mod (&2 pow dimindex(:N)))"
   (REWRITE_TAC [word_neg] THEN
    MESON_TAC [ICONG_WORD_SUB, INT_SUB_LZERO, IVAL_WORD_0])

  let IWORD_INT_NEG ← prove
   r"!x. iword(--x):N word = word_neg (iword x)"
   (REWRITE_TAC [← GSYM INT_SUB_LZERO, word_neg] THEN
    REWRITE_TAC [IWORD_INT_SUB, ← GSYM WORD_IWORD])

  let WORD_NEG_AS_ADD ← prove
   r"!x:N word. word_neg x = word_add (word_not x) (word 1)"
   (GEN_TAC THEN REWRITE_TAC [← GSYM VAL_CONG, CONG, VAL_WORD_NEG] THEN
    REWRITE_TAC [MOD_MOD_REFL, VAL_WORD_ADD, VAL_WORD_1, VAL_WORD_NOT] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    SIMP_TAC [VAL_BOUND, ← ARITH_RULE (← q r"n < e ==> (e - 1 - n) + 1 = e - n")])

  return { word_not, BIT_WORD_NOT, BITS_OF_WORD_NOT, WORD_OF_BITS_DIFF, VAL_WORD_NOT,
           INT_VAL_WORD_NOT, REAL_VAL_WORD_NOT, WORD_POPCOUNT_NOT, word_and, BIT_WORD_AND,
           BIT_WORD_AND_ALT, BITS_OF_WORD_AND, WORD_AND_EQ_0, WORD_OF_BITS_INTER,
           WORD_AND_WORD_OF_BITS_SING, WORD_OF_BITS_SING_AND_WORD, WORD_AND_POW2,
           VAL_WORD_AND_POW2, WORD_AND_POW2_BITVAL, VAL_WORD_AND_POW2_BITVAL,
           VAL_WORD_AND_LE, VAL_WORD_AND_LE_MIN, VAL_WORD_AND_WORD_LE, WORD_POPCOUNT_AND,
           word_or, BIT_WORD_OR, BIT_WORD_OR_ALT, BITS_OF_WORD_OR, WORD_OF_BITS_UNION,
           VAL_WORD_OR_LE, VAL_WORD_OR_LE_MAX, WORD_POPCOUNT_OR, WORD_POPCOUNT_OR_DISJOINT,
           word_xor, BIT_WORD_XOR, BIT_WORD_XOR_ALT, VAL_WORD_ADD_AND_XOR,
           VAL_WORD_ADD_AND_OR, VAL_WORD_OR_DISJOINT, VAL_WORD_OR_AND_XOR,
           REAL_VAL_WORD_XOR, word_add, VAL_WORD_ADD, VAL_WORD_ADD_CASES,
           VAL_WORD_ADC_CASES, INT_VAL_WORD_ADD_CASES, CONG_WORD_ADD, INT_CONG_WORD_ADD,
           WORD_ADD, ICONG_WORD_ADD, IWORD_INT_ADD, WORD_ADD_IMODULAR, ODD_VAL_WORD,
           EVEN_VAL_WORD, ODD_VAL_WORD_ADD, EVEN_VAL_WORD_ADD, word_sub, VAL_WORD_SUB,
           VAL_WORD_SUB_CASES, INT_VAL_WORD_SUB_CASES, CONG_WORD_SUB, INT_CONG_WORD_SUB,
           INT_VAL_WORD_SUB, ICONG_WORD_SUB, IWORD_INT_SUB, WORD_SUB_IMODULAR, WORD_SUB,
           word_neg, ODD_VAL_WORD_SUB, EVEN_VAL_WORD_SUB, VAL_WORD_NEG, VAL_WORD_NEG_CASES,
           INT_VAL_WORD_NEG_CASES, REAL_VAL_WORD_NEG_CASES, INT_VAL_WORD_NEG,
           REAL_VAL_WORD_NEG, CONG_WORD_NEG, INT_CONG_WORD_NEG, ICONG_WORD_NEG,
           IWORD_INT_NEG, WORD_NEG_AS_ADD }

/- (words.ml 2481-2759: more on neg; mul, udiv, umod, max, min, shl.) -/

structure WordOps2 where
  WORD_NOT_AS_SUB : thm
  VAL_WORD_NEG_1 : thm
  IVAL_WORD_NEG_1 : thm
  IVAL_EQ_MINUS1 : thm
  WORD_NEG_1 : thm
  ODD_VAL_WORD_NEG : thm
  EVEN_VAL_WORD_NEG : thm
  word_mul : thm
  VAL_WORD_MUL : thm
  CONG_WORD_MUL : thm
  INT_CONG_WORD_MUL : thm
  WORD_MUL : thm
  ICONG_WORD_MUL : thm
  IWORD_INT_MUL : thm
  WORD_MUL_IMODULAR : thm
  ODD_VAL_WORD_MUL : thm
  EVEN_VAL_WORD_MUL : thm
  word_udiv : thm
  VAL_WORD_UDIV : thm
  word_umod : thm
  VAL_WORD_UMOD : thm
  word_umax : thm
  word_imax : thm
  VAL_WORD_UMAX : thm
  WORD_UMAX : thm
  WORD_UMAX_SYM : thm
  WORD_UMAX_ASSOC : thm
  IVAL_WORD_IMAX : thm
  word_umin : thm
  word_imin : thm
  VAL_WORD_UMIN : thm
  WORD_UMIN : thm
  WORD_UMIN_SYM : thm
  WORD_UMIN_ASSOC : thm
  IVAL_WORD_IMIN : thm
  word_shl : thm
  VAL_WORD_SHL : thm
  CONG_WORD_SHL : thm
  ICONG_WORD_SHL : thm
  BIT_WORD_SHL : thm
  WORD_SHL_WORD_OF_BITS : thm
  WORD_SHL_0 : thm
  WORD_SHL_ZERO : thm
  WORD_SHL_TRIVIAL : thm
  WORD_SHL_COMPOSE : thm
  WORD_SHL_LSB_ALT : thm
  WORD_SHL_LSB : thm
  deriving Inhabited

@[nospecialize]
def setupWordOps2 [HolBase] (D : WordsDeps) (BBitval : Bitval) (BBinary : Binary) (BWordType : WordType) (BBitsOfWord : BitsOfWord) (BVal : Val) (BIval : Ival) (BGeneralOps : GeneralOps) (BWordOps1 : WordOps1) :
    ExceptT String IO WordOps2 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INTEGER_RULE,
        INT_ARITH_TAC, MOD_DOWN_CONV, NUMBER_RULE, NUM_REDUCE_CONV, SET_TAC,
        new_definition, .. } := D
  let { ARITH, ARITH_EQ, CONG, DIMINDEX_NONZERO, DIV_LE, DIV_MOD, DIV_MULT, DIV_MULT2,
        EVEN_EXP, EXP, EXP_ADD, EXP_EQ_0, .. } := D.core1
  let { FUN_EQ_THM, INT_MAX, INT_MIN, INT_OF_NUM_CLAUSES, INT_OF_NUM_MUL,
        INT_OF_NUM_POW, INT_OF_NUM_SUB, .. } := D.core2
  let { LE_1, LE_EXP, MAX, MIN, MOD_LE, MOD_LT, MOD_MOD_REFL, MULT_ASSOC, MULT_CLAUSES,
        MULT_SYM, NOT_ODD, ODD_EXP, ODD_MOD_EVEN, ODD_MULT, ODD_SUB, .. } := D.core3
  let { SUB_REFL, num_congruent, .. } := D.core4
  let { bitval, .. } := BBitval
  let { ODD_MOD_POW2, .. } := BBinary
  let { WORD_EQ_BITS_ALT, bit, .. } := BWordType
  let { WORD_OF_BITS_ALT, .. } := BBitsOfWord
  let { BIT_VAL, BIT_WORD_0, BIT_WORD_POW2, VAL_BOUND, VAL_CONG, VAL_EQ, VAL_WORD,
        VAL_WORD_0, VAL_WORD_1, VAL_WORD_CONG, WORD_EQ, .. } := BVal
  let { IVAL_CONG, IVAL_EQ, IVAL_IWORD_CONG, IVAL_VAL_CONG, IWORD_IVAL, ival, .. } := BIval
  let { CONG_IMODULAR, CONG_MODULAR, VAL_MODULAR, imodular, .. } := BGeneralOps
  let { VAL_WORD_NEG, VAL_WORD_NEG_CASES, VAL_WORD_NOT, VAL_WORD_SUB,
        VAL_WORD_SUB_CASES, word_neg, .. } := BWordOps1
  -- @@SCOPE END

  let WORD_NOT_AS_SUB ← prove
   r"!x:N word. word_not x = word_sub (word_neg x) (word 1)"
   (GEN_TAC THEN
    REWRITE_TAC [← GSYM VAL_CONG, CONG, VAL_WORD_SUB, VAL_WORD_NEG] THEN
    REWRITE_TAC [MOD_MOD_REFL, VAL_WORD_SUB, VAL_WORD_1, VAL_WORD_NOT] THEN
    CONV_TAC MOD_DOWN_CONV THEN SIMP_TAC [VAL_BOUND, ← ARITH_RULE
     (← q r"x < e ==> (e - x) + (e - 1) = e + (e - 1 - x)")] THEN
    REWRITE_TAC [← GSYM CONG] THEN CONV_TAC (fun t => (NUMBER_RULE t).run))

  let VAL_WORD_NEG_1 ← prove
   r"val(word_neg(word 1:N word)) = 2 EXP dimindex(:N) - 1"
   (REWRITE_TAC [VAL_WORD_NEG_CASES, VAL_WORD_1, ARITH_EQ])

  let IVAL_WORD_NEG_1 ← prove
   r"ival(word_neg(word 1:N word)) = -- &1"
   (REWRITE_TAC [ival, VAL_WORD_NEG_1] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"m - 1 < n <=> ~(n = 0) /\ m <= n")] THEN
    SIMP_TAC [LE_EXP, EXP_EQ_0, ARITH_EQ, DIMINDEX_NONZERO,
              ← ARITH_RULE (← q r"n <= n - 1 <=> n = 0"),
              ← GSYM INT_OF_NUM_SUB, ← GSYM INT_OF_NUM_POW, LE_1] THEN
    INT_ARITH_TAC)

  let IVAL_EQ_MINUS1 ← prove
   r"!w:N word. ival w = -- &1 <=> w = word_neg(word 1)"
   (REWRITE_TAC [← GSYM IVAL_EQ, IVAL_WORD_NEG_1])

  let WORD_NEG_1 ← prove
   r"word_neg(word 1:N word) = word_not(word 0)"
   (REWRITE_TAC [WORD_NOT_AS_SUB, word_neg] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_0, VAL_WORD_SUB_CASES] THEN
    CONV_TAC NUM_REDUCE_CONV)

  let ODD_VAL_WORD_NEG ← prove
   r"!x:N word. ODD(val(word_neg x)) <=> ODD(val x)"
   (SIMP_TAC [VAL_WORD_NEG, ODD_MOD_EVEN, EVEN_EXP, ARITH, DIMINDEX_NONZERO] THEN
    REWRITE_TAC [ODD_SUB, VAL_BOUND, ODD_EXP, DIMINDEX_NONZERO, ARITH])

  let EVEN_VAL_WORD_NEG ← prove
   r"!x:N word. EVEN(val(word_neg x)) <=> EVEN(val x)"
   (REWRITE_TAC [← GSYM NOT_ODD, ODD_VAL_WORD_NEG] THEN CONV_TAC (fun t => (TAUT t).run))

  let word_mul ← new_definition
   r"word_mul = modular ( * )"

  let VAL_WORD_MUL ← prove
   r"!x y:(N)word.
        val(word_mul x y) = (val(x) * val(y)) MOD (2 EXP dimindex(:N))"
   (REWRITE_TAC [word_mul, VAL_MODULAR])

  let CONG_WORD_MUL ← prove
   r"!x y:(N)word.
        (val(word_mul x y) == val x * val y) (mod (2 EXP dimindex(:N)))"
   (REWRITE_TAC [word_mul, CONG_MODULAR])

  let INT_CONG_WORD_MUL ← prove
   r"!x y:N word.
    (&(val(word_mul x y)):int == &(val x) * &(val y))
    (mod (&2 pow dimindex(:N)))"
   (REWRITE_TAC [INT_OF_NUM_CLAUSES, ← GSYM num_congruent, CONG_WORD_MUL])

  let WORD_MUL ← prove
   r"!x y. word(x * y):N word = word_mul (word x) (word y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM VAL_CONG] THEN
    MP_TAC (← ISPECL [← q "word x:N word", ← q "word y:N word"] CONG_WORD_MUL) THEN
    MAP_EVERY (MP_TAC o (fun t => ISPEC t VAL_WORD_CONG))
     [← q "x * y:num", ← q "y:num", ← q "x:num"] THEN
    CONV_TAC (fun t => (NUMBER_RULE t).run))

  let ICONG_WORD_MUL ← prove
   r"!x y:(N)word.
        (ival(word_mul x y) == ival x * ival y) (mod (&2 pow dimindex(:N)))"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q "x:N word", ← q "y:N word"] CONG_WORD_MUL) THEN
    MAP_EVERY (MP_TAC o (fun t => SPEC t IVAL_VAL_CONG))
     [← q "x:N word", ← q "y:N word", ← q "word_mul x y:N word"] THEN
    REWRITE_TAC [num_congruent, ← GSYM INT_OF_NUM_POW, ← GSYM INT_OF_NUM_MUL] THEN
    CONV_TAC (fun t => (INTEGER_RULE t).run))

  let IWORD_INT_MUL ← prove
   r"!x y. iword(x * y):N word = word_mul (iword x) (iword y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM IVAL_CONG] THEN
    MP_TAC (← ISPECL [← q "iword x:N word", ← q "iword y:N word"] ICONG_WORD_MUL) THEN
    MAP_EVERY (MP_TAC o (fun t => ISPEC t IVAL_IWORD_CONG))
     [← q "x * y:int", ← q "y:int", ← q "x:int"] THEN
    CONV_TAC (fun t => (INTEGER_RULE t).run))

  let WORD_MUL_IMODULAR ← prove
   r"(word_mul:N word->N word->N word) = imodular ( * )"
   (REWRITE_TAC [FUN_EQ_THM, ← GSYM IVAL_CONG] THEN
    ASM_MESON_TAC [ICONG_WORD_MUL, CONG_IMODULAR, ← INTEGER_RULE
     (← q r"(a:int == b) (mod n) /\ (c == b) (mod n) ==> (a == c) (mod n)")])

  let ODD_VAL_WORD_MUL ← prove
   r"!x y:N word. ODD(val(word_mul x y)) <=> ODD(val x) /\ ODD(val y)"
   (SIMP_TAC [VAL_WORD_MUL, ODD_MOD_EVEN, EVEN_EXP, ARITH, DIMINDEX_NONZERO] THEN
    REWRITE_TAC [ODD_MULT])

  let EVEN_VAL_WORD_MUL ← prove
   r"!x y:N word. EVEN(val(word_mul x y)) <=> EVEN(val x) \/ EVEN(val y)"
   (REWRITE_TAC [← GSYM NOT_ODD, ODD_VAL_WORD_MUL] THEN CONV_TAC (fun t => (TAUT t).run))

  let word_udiv ← new_definition
   r"word_udiv = modular (DIV)"

  let VAL_WORD_UDIV ← prove
   r"!x y:(N)word.
        val(word_udiv x y) = val(x) DIV val(y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_udiv, VAL_MODULAR] THEN
    MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC (← ARITH_RULE
     (← q r"m DIV n <= m /\ m < p ==> m DIV n < p")) THEN
    REWRITE_TAC [VAL_BOUND, DIV_LE])

  let word_umod ← new_definition
   r"word_umod = modular (MOD)"

  let VAL_WORD_UMOD ← prove
   r"!x y:(N)word.
        val(word_umod x y) = val(x) MOD val(y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_umod, VAL_MODULAR] THEN
    MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC (← ARITH_RULE
     (← q r"m MOD n <= m /\ m < p ==> m MOD n < p")) THEN
    REWRITE_TAC [VAL_BOUND, MOD_LE])

  let word_umax ← new_definition
   r"word_umax = modular (MAX)"

  let word_imax ← new_definition
   r"word_imax = imodular (max)"

  let VAL_WORD_UMAX ← prove
   r"!x y:(N)word.
        val(word_umax x y) = MAX (val x) (val y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_umax, VAL_MODULAR] THEN
    MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC [← ARITH_RULE (← q r"MAX x y < n <=> x < n /\ y < n")] THEN
    REWRITE_TAC [VAL_BOUND])

  let WORD_UMAX ← prove
   r"!x y:N word. word_umax x y = if val x <= val y then y else x"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_UMAX, MAX])

  let WORD_UMAX_SYM ← prove
   r"!x y:N word. word_umax x y = word_umax y x"
   (REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_UMAX] THEN ARITH_TAC)

  let WORD_UMAX_ASSOC ← prove
   r"!x y z:N word. word_umax x (word_umax y z) = word_umax (word_umax x y) z"
   (REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_UMAX] THEN ARITH_TAC)

  let IVAL_WORD_IMAX ← prove
   r"!x y:(N)word.
        ival(word_imax x y) = max (ival x) (ival y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_imax, imodular] THEN
    REWRITE_TAC [INT_MAX] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [IWORD_IVAL])

  let word_umin ← new_definition
   r"word_umin = modular (MIN)"

  let word_imin ← new_definition
   r"word_imin = imodular (min)"

  let VAL_WORD_UMIN ← prove
   r"!x y:(N)word.
        val(word_umin x y) = MIN (val x) (val y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_umin, VAL_MODULAR] THEN
    MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC [← ARITH_RULE (← q r"MIN x y < n <=> x < n \/ y < n")] THEN
    REWRITE_TAC [VAL_BOUND])

  let WORD_UMIN ← prove
   r"!x y:N word. word_umin x y = if val x <= val y then x else y"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_UMIN, MIN])

  let WORD_UMIN_SYM ← prove
   r"!x y:N word. word_umin x y = word_umin y x"
   (REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_UMIN] THEN ARITH_TAC)

  let WORD_UMIN_ASSOC ← prove
   r"!x y z:N word. word_umin x (word_umin y z) = word_umin (word_umin x y) z"
   (REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_UMIN] THEN ARITH_TAC)

  let IVAL_WORD_IMIN ← prove
   r"!x y:(N)word.
        ival(word_imin x y) = min (ival x) (ival y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_imin, imodular] THEN
    REWRITE_TAC [INT_MIN] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [IWORD_IVAL])

  let word_shl ← new_definition
   r"word_shl (x:(N)word) n = word((val x) * 2 EXP n):(N)word"

  let VAL_WORD_SHL ← prove
   r"!(x:N word) n.
        val(word_shl x n) = (2 EXP n * val x) MOD (2 EXP dimindex(:N))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_shl, VAL_WORD, MULT_SYM])

  let CONG_WORD_SHL ← prove
   r"!(x:N word) n.
        (val(word_shl x n) == 2 EXP n * val x) (mod (2 EXP dimindex(:N)))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [VAL_WORD_SHL, CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC)

  let ICONG_WORD_SHL ← prove
   r"!(x:N word) n.
        (ival(word_shl x n) == &2 pow n * ival x) (mod (&2 pow dimindex(:N)))"
   (REPEAT GEN_TAC THEN MP_TAC (← ISPECL [← q "x:N word", ← q "n:num"] CONG_WORD_SHL) THEN
    MAP_EVERY (MP_TAC o (fun t => SPEC t IVAL_VAL_CONG))
     [← q "x:N word", ← q "word_shl x n:N word"] THEN
    REWRITE_TAC [num_congruent, ← GSYM INT_OF_NUM_POW, ← GSYM INT_OF_NUM_MUL] THEN
    CONV_TAC (fun t => (INTEGER_RULE t).run))

  let BIT_WORD_SHL ← prove
   r"!(x:N word) n i.
        bit i (word_shl x n) <=>
        n <= i /\ i < dimindex(:N) /\ bit (i - n) x"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "i < dimindex(:N)") THENL
     [ASM_REWRITE_TAC [], ASM_REWRITE_TAC [bit]] THEN
    REWRITE_TAC [word_shl, BIT_VAL, VAL_WORD] THEN
    SUBGOAL_THEN (← q r"dimindex(:N) = i + (dimindex(:N) - i)") SUBST1_TAC THENL
     [ASM_ARITH_TAC, REWRITE_TAC [EXP_ADD, ← GSYM DIV_MOD]] THEN
    ASM_SIMP_TAC [ODD_MOD_POW2, ← ARITH_RULE (← q r"i < n ==> ~(n - i = 0)")] THEN
    ASM_CASES_TAC (← q "n:num <= i") THEN ASM_REWRITE_TAC [] THENL
     [AP_TERM_TAC THEN
      SUBGOAL_THEN (← q "i:num = (i - n) + n")
       (fun th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th])
      THENL [ASM_ARITH_TAC, REWRITE_TAC [EXP_ADD]] THEN
      ONCE_REWRITE_TAC [MULT_SYM] THEN MATCH_MP_TAC DIV_MULT2 THEN
      REWRITE_TAC [EXP_EQ_0, ARITH_EQ],
      SUBGOAL_THEN (← q "n:num = i + (n - i)") SUBST1_TAC THENL
       [ASM_ARITH_TAC, ONCE_REWRITE_TAC [MULT_SYM]] THEN
      REWRITE_TAC [EXP_ADD, ← GSYM MULT_ASSOC] THEN
      SIMP_TAC [DIV_MULT, ARITH_EQ, EXP_EQ_0] THEN
      REWRITE_TAC [ODD_MULT, ODD_EXP] THEN ASM_ARITH_TAC])

  let WORD_SHL_WORD_OF_BITS ← prove
   r"!(x:N word) n.
        word_shl x n =
        word_of_bits {i | n <= i /\ i < dimindex(:N) /\ bit (i - n) x}"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [WORD_OF_BITS_ALT] THEN
    AP_TERM_TAC THEN REWRITE_TAC [BIT_WORD_SHL] THEN SET_TAC [])

  let WORD_SHL_0 ← prove
   r"!n. word_shl (word 0:N word) n = word 0"
   (REWRITE_TAC [word_shl, VAL_WORD_0, MULT_CLAUSES])

  let WORD_SHL_ZERO ← prove
   r"!x:N word. word_shl x 0 = x"
   (REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_SHL, EXP, MULT_CLAUSES] THEN
    SIMP_TAC [MOD_LT, VAL_BOUND])

  let WORD_SHL_TRIVIAL ← prove
   r"!(x:N word) n.
       dimindex(:N) <= n ==> word_shl x n = word 0"
   (SIMP_TAC [WORD_EQ_BITS_ALT, BIT_WORD_SHL, BIT_WORD_0] THEN ARITH_TAC)

  let WORD_SHL_COMPOSE ← prove
   r"!(x:N word) m n. word_shl (word_shl x m) n = word_shl x (m + n)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_shl, VAL_WORD, EXP_ADD] THEN
    REWRITE_TAC [WORD_EQ, CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC [MULT_ASSOC])

  let WORD_SHL_LSB_ALT ← prove
   r"!x:N word.
        word_shl x (dimindex(:N) - 1) =
        if bit 0 x then word(2 EXP (dimindex(:N) - 1)) else word 0"
   (GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_0, BIT_WORD_POW2, BIT_WORD_SHL] THEN
    X_GEN_TAC (← q "i:num") THEN ASM_CASES_TAC (← q "i = dimindex(:N) - 1") THEN
    ASM_REWRITE_TAC [SUB_REFL] THEN ASM_ARITH_TAC)

  let WORD_SHL_LSB ← prove
   r"!x:N word.
        word_shl x (dimindex(:N) - 1) =
        word(2 EXP (dimindex(:N) - 1) * bitval(bit 0 x))"
   (GEN_TAC THEN REWRITE_TAC [WORD_SHL_LSB_ALT, bitval] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [MULT_CLAUSES])

  return { WORD_NOT_AS_SUB, VAL_WORD_NEG_1, IVAL_WORD_NEG_1, IVAL_EQ_MINUS1, WORD_NEG_1,
           ODD_VAL_WORD_NEG, EVEN_VAL_WORD_NEG, word_mul, VAL_WORD_MUL, CONG_WORD_MUL,
           INT_CONG_WORD_MUL, WORD_MUL, ICONG_WORD_MUL, IWORD_INT_MUL, WORD_MUL_IMODULAR,
           ODD_VAL_WORD_MUL, EVEN_VAL_WORD_MUL, word_udiv, VAL_WORD_UDIV, word_umod,
           VAL_WORD_UMOD, word_umax, word_imax, VAL_WORD_UMAX, WORD_UMAX, WORD_UMAX_SYM,
           WORD_UMAX_ASSOC, IVAL_WORD_IMAX, word_umin, word_imin, VAL_WORD_UMIN, WORD_UMIN,
           WORD_UMIN_SYM, WORD_UMIN_ASSOC, IVAL_WORD_IMIN, word_shl, VAL_WORD_SHL,
           CONG_WORD_SHL, ICONG_WORD_SHL, BIT_WORD_SHL, WORD_SHL_WORD_OF_BITS, WORD_SHL_0,
           WORD_SHL_ZERO, WORD_SHL_TRIVIAL, WORD_SHL_COMPOSE, WORD_SHL_LSB_ALT, WORD_SHL_LSB }

/- (words.ml 2761-3256: shl of words, mul expansion, ushr, ishr, rotates,
   relations.) -/

structure WordOps3 where
  WORD_SHL_WORD : thm
  WORD_SHL_AS_IWORD : thm
  WORD_SHL_IWORD : thm
  WORD_MUL_EXPAND : thm
  word_ushr : thm
  VAL_WORD_USHR : thm
  WORD_USHR_EQ_0 : thm
  BIT_WORD_USHR : thm
  WORD_USHR_WORD_OF_BITS : thm
  WORD_USHR_0 : thm
  WORD_USHR_ZERO : thm
  WORD_USHR_COMPOSE : thm
  WORD_USHR_MSB_ALT : thm
  WORD_USHR_MSB : thm
  WORD_USHR_MSB_EQ : thm
  WORD_POPCOUNT_SHL : thm
  WORD_POPCOUNT_USHR : thm
  word_ishr : thm
  IVAL_WORD_ISHR : thm
  WORD_ISHR_EQ_0 : thm
  BIT_WORD_ISHR : thm
  WORD_ISHR_WORD_OF_BITS : thm
  WORD_ISHR_0 : thm
  WORD_ISHR_ZERO : thm
  WORD_ISHR_COMPOSE : thm
  WORD_ISHR_UNIQUE : thm
  IVAL_WORD_ISHR_SHL_UNIQUE : thm
  word_ror : thm
  word_rol : thm
  WORD_ROR_ROL_GEN : thm
  WORD_ROL_ROR_GEN : thm
  WORD_ROR_PERIODIC : thm
  WORD_ROR_MOD : thm
  WORD_ROR_EQ_SELF : thm
  WORD_ROR_ZERO : thm
  WORD_ROL_PERIODIC : thm
  WORD_ROL_MOD : thm
  WORD_ROL_EQ_SELF : thm
  WORD_ROL_ZERO : thm
  WORD_ROR_ROL : thm
  WORD_ROL_ROR : thm
  WORD_ROR_SHIFTS : thm
  WORD_ROL_SHIFTS : thm
  BIT_WORD_ROR : thm
  BIT_WORD_ROL : thm
  WORD_ROR_COMPOSE : thm
  WORD_ROL_COMPOSE : thm
  VAL_WORD_ROR : thm
  VAL_WORD_ROL : thm
  word_ule : thm
  word_uge : thm
  word_ult : thm
  word_ugt : thm
  word_ile : thm
  word_ige : thm
  word_ilt : thm
  word_igt : thm
  WORD_ULT : thm
  WORD_ULE : thm
  WORD_UGT : thm
  WORD_UGE : thm
  WORD_ILT : thm
  WORD_ILE : thm
  WORD_IGT : thm
  WORD_IGE : thm
  deriving Inhabited

@[nospecialize]
def setupWordOps3 [HolBase] (D : WordsDeps) (BWordType : WordType) (BBitsOfWord : BitsOfWord) (BVal : Val) (BIval : Ival) (BPopcount : Popcount) (BGeneralOps : GeneralOps) (BWordOps1 : WordOps1) (BWordOps2 : WordOps2) :
    ExceptT String IO WordOps3 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INTEGER_RULE, INT_ARITH,
        INT_REDUCE_CONV, MESON, MOD_DOWN_CONV, NUMBER_RULE, NUM_REDUCE_CONV, SET_TAC,
        new_definition, .. } := D
  let { ADD_AC, ADD_CLAUSES, ADD_SYM, ARITH_EQ, CARD_IMAGE_LE, CARD_SUBSET, CONG,
        CONG_LMOD, CONG_RMOD, DIMINDEX_NONZERO, DISJ_SYM, DIVISION, DIV_0, DIV_1,
        DIV_DIV, DIV_EQ_0, DIV_LE, DIV_MOD, EVEN_EXISTS, EXP, EXP_ADD, EXP_EQ_0, .. } := D.core1
  let { FINITE_IMAGE, INT_ABS_NUM, INT_ABS_POW, INT_DIVISION, INT_DIV_1, INT_DIV_DIV,
        INT_DIV_EQ_0, INT_DIV_LT_EQ, INT_DIV_MUL, INT_DIV_ZERO, INT_EQ_MUL_LCANCEL,
        INT_LE_DIV_EQ, INT_LE_POW2, INT_LE_RMUL, INT_LT_IMP_LE, INT_LT_POW2,
        INT_MUL_RID, INT_MUL_RNEG, INT_MUL_SYM, INT_NOT_LE, INT_OF_NUM_ADD,
        INT_OF_NUM_CLAUSES, INT_OF_NUM_EQ, INT_OF_NUM_LE, INT_OF_NUM_OF_INT,
        INT_OF_NUM_REM, INT_OF_NUM_SUB, INT_POS, INT_POW, INT_POW_ADD, INT_POW_EQ_0,
        INT_POW_LE, INT_POW_MONO, INT_REM_EQ, INT_REM_MOD_SELF, IN_ELIM_THM, IN_IMAGE, .. } := D.core2
  let { LEFT_IMP_EXISTS_THM, LE_EXP, LE_LT, LE_TRANS, LTE_TRANS, LT_IMP_LE, LT_TRANS,
        MOD_EQ_0, MOD_LT, MOD_LT_EQ, MOD_MULT2, MOD_MULT_ADD, MOD_NSUM_MOD_NUMSEG,
        MOD_REFL, MOD_UNIQ, MULT_AC, MULT_SYM, NOT_LE, NOT_LT, NSUM_RMUL,
        NUMSEG_LT_DIMINDEX, .. } := D.core3
  let { SUBSET, SUB_0, SUB_REFL, divides, int_divides, num_congruent, num_divides, .. } := D.core4
  let { BIT_TRIVIAL, WORD_EQ_BITS, WORD_EQ_BITS_ALT, .. } := BWordType
  let { BIT_WORD_OF_BITS, FINITE_BITS_OF_WORD, WORD_OF_BITS_ALT, WORD_OF_BITS_EQ,
        bits_of_word, .. } := BBitsOfWord
  let { BIT_VAL, BIT_WORD_0, BIT_WORD_1, VAL_BOUND, VAL_EQ, VAL_EQ_0, VAL_WORD,
        VAL_WORD_0, WORD_BITVAL, WORD_NE_10, val_def, .. } := BVal
  let { BIT_IVAL, BIT_IWORD, INT_DIVIDES_IVAL_IWORD, IVAL_BOUND, IVAL_EQ, IVAL_EQ_0,
        IVAL_IWORD, IVAL_IWORD_CONG, IVAL_VAL_CONG, IVAL_WORD_0, IWORD_EQ, MSB_IVAL,
        WORD_IWORD, .. } := BIval
  let { word_popcount, .. } := BPopcount
  let { irelational2, modular, relational2, .. } := BGeneralOps
  let { BIT_WORD_AND, BIT_WORD_OR, VAL_WORD_OR_DISJOINT, .. } := BWordOps1
  let { BIT_WORD_SHL, VAL_WORD_SHL, WORD_SHL_TRIVIAL, word_mul, word_shl, .. } := BWordOps2
  -- @@SCOPE END

  let WORD_SHL_WORD ← prove
   r"!x n. word_shl (word x:N word) n = word(2 EXP n * x)"
   (REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_SHL, VAL_WORD] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC [])

  let WORD_SHL_AS_IWORD ← prove
   r"!(x:N word) n. word_shl x n = iword(ival x * &2 pow n)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_shl, WORD_IWORD] THEN
    REWRITE_TAC [IWORD_EQ, ← GSYM INT_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC (← INTEGER_RULE
     (← q r"(a:int == b) (mod n) ==> (b * x == a * x) (mod n)")) THEN
    REWRITE_TAC [IVAL_VAL_CONG])

  let WORD_SHL_IWORD ← prove
   r"!x n. word_shl (iword x:N word) n = iword(&2 pow n * x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [WORD_SHL_AS_IWORD, IWORD_EQ] THEN
    MATCH_MP_TAC (← INTEGER_RULE
     (← q r"(x:int == y) (mod p) ==> (x * n == n * y) (mod p)")) THEN
    REWRITE_TAC [IVAL_IWORD_CONG])

  let WORD_MUL_EXPAND ← prove
   r"!x y:N word.
        word_mul x y =
        word(nsum {i | i < dimindex(:N)}
                  (\i. bitval(bit i x) * val(word_shl y i)))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_mul, modular] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [val_def] THEN
    REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD, ← GSYM NSUM_RMUL, NUMSEG_LT_DIMINDEX] THEN
    ONCE_REWRITE_TAC [MOD_NSUM_MOD_NUMSEG] THEN
    REWRITE_TAC [VAL_WORD_SHL] THEN CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC [MULT_AC])

  let word_ushr ← new_definition
   r"word_ushr (x:(N)word) n =
        word((val x) DIV (2 EXP n)):(N)word"

  let VAL_WORD_USHR ← prove
   r"!(x:N word) n.
        val(word_ushr x n) = val x DIV (2 EXP n)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_ushr, VAL_WORD] THEN
    MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC (← ARITH_RULE
     (← q r"m DIV n <= m /\ m < p ==> m DIV n < p")) THEN
    REWRITE_TAC [VAL_BOUND, DIV_LE])

  let WORD_USHR_EQ_0 ← prove
   r"!(x:N word) n. word_ushr x n = word 0 <=> val x < 2 EXP n"
   (REWRITE_TAC [← GSYM VAL_EQ_0, VAL_WORD_USHR] THEN
    SIMP_TAC [DIV_EQ_0, EXP_EQ_0, ARITH_EQ])

  let BIT_WORD_USHR ← prove
   r"!(x:N word) n i.
        bit i (word_ushr x n) <=> bit (i + n) x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_ushr, BIT_VAL, VAL_WORD] THEN
    REWRITE_TAC [DIV_MOD, DIV_DIV] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
    AP_TERM_TAC THEN REWRITE_TAC [← GSYM EXP_ADD] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN
    TRANS_TAC LTE_TRANS (← q "2 EXP dimindex(:N)") THEN
    ASM_REWRITE_TAC [VAL_BOUND, LE_EXP, DIMINDEX_NONZERO] THEN
    ARITH_TAC)

  let WORD_USHR_WORD_OF_BITS ← prove
   r"!(x:N word) n.
        word_ushr x n =
        word_of_bits {i | i < dimindex(:N) /\ bit (i + n) x}"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [WORD_OF_BITS_ALT] THEN
    AP_TERM_TAC THEN REWRITE_TAC [BIT_WORD_USHR] THEN SET_TAC [])

  let WORD_USHR_0 ← prove
   r"!n. word_ushr (word 0:N word) n = word 0"
   (REWRITE_TAC [word_ushr, VAL_WORD_0, DIV_0])

  let WORD_USHR_ZERO ← prove
   r"!x:N word. word_ushr x 0 = x"
   (REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_USHR, EXP, DIV_1] THEN
    SIMP_TAC [MOD_LT, VAL_BOUND])

  let WORD_USHR_COMPOSE ← prove
   r"!(x:N word) m n. word_ushr (word_ushr x m) n = word_ushr x (m + n)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [word_ushr] THEN
    REWRITE_TAC [VAL_WORD_USHR] THEN REWRITE_TAC [EXP_ADD, DIV_DIV])

  let WORD_USHR_MSB_ALT ← prove
   r"!x:N word. word_ushr x (dimindex(:N) - 1) =
              if bit (dimindex(:N) - 1) x then word 1 else word 0"
   (GEN_TAC THEN REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_USHR] THEN
    X_GEN_TAC (← q "i:num") THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [BIT_WORD_0, BIT_WORD_1] THEN
    ASM_CASES_TAC (← q "i = 0") THEN ASM_REWRITE_TAC [ADD_CLAUSES] THEN
    MATCH_MP_TAC (← REWRITE_RULE [] BIT_TRIVIAL) THEN ASM_ARITH_TAC)

  let WORD_USHR_MSB ← prove
   r"!x:N word. word_ushr x (dimindex(:N) - 1) =
              word(bitval(bit (dimindex(:N) - 1) x))"
   (REWRITE_TAC [WORD_USHR_MSB_ALT, WORD_BITVAL])

  let WORD_USHR_MSB_EQ ← prove
   r"(!x:N word. word_ushr x (dimindex(:N) - 1) = word 1 <=>
               bit (dimindex(:N) - 1) x) /\
   (!x:N word. word_ushr x (dimindex(:N) - 1) = word 0 <=>
               ~bit (dimindex(:N) - 1) x) /\
   (!P (x:N word).
        (word_ushr x (dimindex(:N) - 1) = if P then word 1 else word 0) <=>
        (bit (dimindex(:N) - 1) x <=> P)) /\
   (!P (x:N word).
        (word_ushr x (dimindex(:N) - 1) = if P then word 0 else word 1) <=>
        (bit (dimindex(:N) - 1) x <=> ~P))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [WORD_USHR_MSB_ALT] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [WORD_NE_10]))

  let WORD_POPCOUNT_SHL ← prove
   r"!(x:N word) n. word_popcount(word_shl x n) <= word_popcount x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_popcount] THEN
    TRANS_TAC LE_TRANS
     (← q r"CARD (IMAGE (\i. n + i) (bits_of_word (x:N word)))") THEN
    SIMP_TAC [CARD_IMAGE_LE, FINITE_BITS_OF_WORD] THEN
    MATCH_MP_TAC CARD_SUBSET THEN
    SIMP_TAC [SUBSET, FINITE_IMAGE, FINITE_BITS_OF_WORD] THEN
    REWRITE_TAC [IN_IMAGE, bits_of_word, IN_ELIM_THM, BIT_WORD_SHL] THEN
    X_GEN_TAC (← q "i:num") THEN STRIP_TAC THEN EXISTS_TAC (← q "i - n:num") THEN
    ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC)

  let WORD_POPCOUNT_USHR ← prove
   r"!(x:N word) n. word_popcount(word_ushr x n) <= word_popcount x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_popcount] THEN
    TRANS_TAC LE_TRANS
     (← q r"CARD (IMAGE (\i. i - n) (bits_of_word (x:N word)))") THEN
    SIMP_TAC [CARD_IMAGE_LE, FINITE_BITS_OF_WORD] THEN
    MATCH_MP_TAC CARD_SUBSET THEN
    SIMP_TAC [SUBSET, FINITE_IMAGE, FINITE_BITS_OF_WORD] THEN
    REWRITE_TAC [IN_IMAGE, bits_of_word, IN_ELIM_THM, BIT_WORD_USHR] THEN
    X_GEN_TAC (← q "i:num") THEN STRIP_TAC THEN EXISTS_TAC (← q "i + n:num") THEN
    ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC)

  let word_ishr ← new_definition
   r"(word_ishr:N word ->num->N word) x n = iword((ival x) div (&2 pow n))"

  let IVAL_WORD_ISHR ← prove
   r"!(x:N word) n. ival(word_ishr x n) = (ival x) div (&2 pow n)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_ishr] THEN
    MATCH_MP_TAC IVAL_IWORD THEN
    SIMP_TAC [INT_LE_DIV_EQ, INT_DIV_LT_EQ, INT_LT_POW2] THEN
    MP_TAC (← ISPEC (← q "x:N word") IVAL_BOUND) THEN
    MATCH_MP_TAC (← INT_ARITH
     (← q r"&1 * a:int <= t * a
    ==> --a <= x /\ x < a ==> t * --a <= x /\ x < t * a")) THEN
    MATCH_MP_TAC INT_LE_RMUL THEN
    SIMP_TAC [INT_LE_POW2, INT_LT_IMP_LE, INT_LT_POW2])

  let WORD_ISHR_EQ_0 ← prove
   r"!(x:N word) n.
        word_ishr x n = word 0 <=> &0 <= ival x /\ ival x < &2 pow n"
   (REWRITE_TAC [← GSYM IVAL_EQ_0, IVAL_WORD_ISHR] THEN
    SIMP_TAC [INT_DIV_EQ_0, INT_POW_EQ_0, INT_OF_NUM_EQ, ARITH_EQ] THEN
    REWRITE_TAC [INT_ABS_POW, INT_ABS_NUM])

  -- Two printing INTEGER_RULEs, in the last THENL branch; the later first.
  let irY ← INTEGER_RULE (← q r"(x:int) divides --y <=> x divides y")
  let irX ← INTEGER_RULE (← q r"(p:int) divides &0")
  let BIT_WORD_ISHR ← prove
   r"!(w:N word) n i.
        bit i (word_ishr w n) <=>
        if i + n < dimindex(:N) then bit (i + n) w
        else i < dimindex(:N) /\ bit (dimindex(:N) - 1) w"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "i < dimindex(:N)") THENL
     [ALL_TAC, ASM_REWRITE_TAC [BIT_IVAL] THEN ASM_ARITH_TAC] THEN
    ASM_REWRITE_TAC [word_ishr, BIT_IWORD] THEN
    SIMP_TAC [INT_DIV_DIV, INT_POW_LE, INT_POS] THEN
    ONCE_REWRITE_TAC [INT_MUL_SYM] THEN REWRITE_TAC [← GSYM INT_POW_ADD] THEN
    COND_CASES_TAC THENL [ASM_SIMP_TAC [BIT_IVAL], ALL_TAC] THEN
    REWRITE_TAC [MSB_IVAL, ← GSYM INT_NOT_LE] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     (← q r"--(&2 pow (i + n)) <= ival(w:N word) /\ ival w < &2 pow (i + n)")
    STRIP_ASSUME_TAC THENL
     [MP_TAC (← ISPEC (← q "w:N word") IVAL_BOUND) THEN MATCH_MP_TAC (← INT_ARITH
       (← q r"a:int <= b ==> --a <= x /\ x < a ==> --b <= x /\ x < b")) THEN
      MATCH_MP_TAC INT_POW_MONO THEN REWRITE_TAC [INT_OF_NUM_LE] THEN
      ASM_ARITH_TAC,
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q "ival(w:N word)", ← q r"(&2:int) pow (i + n)"]
          INT_DIV_EQ_0) THEN
    ASM_REWRITE_TAC [INT_POW_EQ_0, INT_OF_NUM_EQ, ARITH_EQ, INT_ABS_POW,
                     INT_ABS_NUM] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     (← q r"-- &1 <= ival(w:N word) div &2 pow (i + n) /\
    ival(w:N word) div &2 pow (i + n) < &1")
    MP_TAC THENL
     [ASM_SIMP_TAC [INT_DIV_LT_EQ, INT_LE_DIV_EQ, INT_LT_POW2] THEN
      ASM_REWRITE_TAC [INT_MUL_RNEG, INT_MUL_RID],
      REWRITE_TAC [← INT_ARITH
       (← q r"-- &1:int <= x /\ x < &1 <=> x = -- &1 \/ x = &0")] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [irX] THEN
      CONV_TAC INT_REDUCE_CONV THEN
      REWRITE_TAC [irY] THEN
      REWRITE_TAC [← GSYM num_divides, divides, ← GSYM EVEN_EXISTS] THEN
      CONV_TAC NUM_REDUCE_CONV])

  let WORD_ISHR_WORD_OF_BITS ← prove
   r"!(x:N word) n.
        word_ishr x n =
        word_of_bits {i | if i < dimindex(:N) - n then bit (i + n) x
                          else bit (dimindex(:N) - 1) x}"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [WORD_OF_BITS_ALT] THEN
    REWRITE_TAC [WORD_OF_BITS_EQ] THEN X_GEN_TAC (← q "i:num") THEN
    DISCH_TAC THEN ASM_REWRITE_TAC [IN_ELIM_THM, BIT_WORD_ISHR] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"i + n:num < m <=> i < m - n")])

  let WORD_ISHR_0 ← prove
   r"!n. word_ishr (word 0:N word) n = word 0"
   (REWRITE_TAC [word_ishr, IVAL_WORD_0, INT_DIV_ZERO, ← GSYM WORD_IWORD])

  let WORD_ISHR_ZERO ← prove
   r"!x:N word. word_ishr x 0 = x"
   (REWRITE_TAC [← GSYM IVAL_EQ, IVAL_WORD_ISHR, INT_POW, INT_DIV_1])

  let WORD_ISHR_COMPOSE ← prove
   r"!(x:N word) m n. word_ishr (word_ishr x m) n = word_ishr x (m + n)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [word_ishr] THEN
    REWRITE_TAC [IVAL_WORD_ISHR, INT_POW_ADD] THEN
    SIMP_TAC [INT_DIV_DIV, INT_POW_LE, INT_POS])

  let WORD_ISHR_UNIQUE ← prove
   r"!(x:N word) y n. ival x = &2 pow n * y ==> word_ishr x n = iword y"
   (SIMP_TAC [word_ishr, INT_DIV_MUL, INT_POW_EQ_0, INT_OF_NUM_EQ, ARITH_EQ])

  let IVAL_WORD_ISHR_SHL_UNIQUE ← prove
   r"!n (x:N word) y.
        ival(word_ishr (word_shl x n) n) = y <=>
        ival(word_shl x n) = &2 pow n * y"
   (REPEAT GEN_TAC THEN REWRITE_TAC [IVAL_WORD_ISHR] THEN
    SUBGOAL_THEN (← q r"&2 pow n divides ival(word_shl x n:N word)") MP_TAC THENL
     [DISJ_CASES_TAC (← ARITH_RULE (← q r"dimindex(:N) <= n \/ n <= dimindex(:N)")) THEN
      ASM_SIMP_TAC [WORD_SHL_TRIVIAL, WORD_ISHR_0, IVAL_WORD_0,
                    ← INTEGER_RULE (← q r"(d:int) divides &0")] THEN
      ASM_SIMP_TAC [WORD_SHL_AS_IWORD, INT_DIVIDES_IVAL_IWORD] THEN
      CONV_TAC (fun t => (INTEGER_RULE t).run),
      REWRITE_TAC [int_divides] THEN STRIP_TAC THEN
      ASM_SIMP_TAC [INT_DIV_MUL, INT_POW_EQ_0, ARITH_EQ, INT_OF_NUM_EQ,
                    INT_EQ_MUL_LCANCEL]])

  let word_ror ← new_definition
   r"(word_ror:N word->num->N word) w n =
        word_of_bits {i | bit ((i + n) MOD dimindex(:N)) w}"

  let word_rol ← new_definition
   r"(word_rol:N word->num->N word) w n =
        word_of_bits {i | bit (num_of_int((&i - &n) rem &(dimindex(:N)))) w}"

  let WORD_ROR_ROL_GEN ← prove
   r"!(w:N word) n.
        word_ror w n = word_rol w (dimindex(:N) - n MOD dimindex(:N))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [word_ror, word_rol, WORD_OF_BITS_EQ] THEN
    X_GEN_TAC (← q "i:num") THEN DISCH_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [← GSYM INT_OF_NUM_EQ] THEN
    W (MP_TAC o PART_MATCH (lhand o rand) INT_OF_NUM_OF_INT o rand o snd) THEN
    ANTS_TAC THENL
     [SIMP_TAC [INT_DIVISION, DIMINDEX_NONZERO, INT_OF_NUM_EQ],
      DISCH_THEN SUBST1_TAC] THEN
    SIMP_TAC [← GSYM INT_OF_NUM_SUB, LT_IMP_LE, DIVISION, DIMINDEX_NONZERO] THEN
    REWRITE_TAC [← GSYM INT_OF_NUM_REM, ← GSYM INT_OF_NUM_ADD, INT_REM_EQ] THEN
    MATCH_MP_TAC (← INTEGER_RULE
     (← q r"(k:int == n) (mod d)
    ==> (i + n == i - (d - k)) (mod d)")) THEN
    REWRITE_TAC [INT_REM_MOD_SELF])

  let WORD_ROL_ROR_GEN ← prove
   r"!(w:N word) n.
        word_rol w n = word_ror w (dimindex(:N) - n MOD dimindex(:N))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [word_ror, word_rol, WORD_OF_BITS_EQ] THEN
    X_GEN_TAC (← q "i:num") THEN DISCH_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [← GSYM INT_OF_NUM_EQ] THEN
    W (MP_TAC o PART_MATCH (lhand o rand) INT_OF_NUM_OF_INT o lhand o snd) THEN
    ANTS_TAC THENL
     [SIMP_TAC [INT_DIVISION, DIMINDEX_NONZERO, INT_OF_NUM_EQ],
      DISCH_THEN SUBST1_TAC] THEN
    SIMP_TAC [← GSYM INT_OF_NUM_SUB, LT_IMP_LE, DIVISION, DIMINDEX_NONZERO] THEN
    REWRITE_TAC [← GSYM INT_OF_NUM_REM, INT_REM_EQ, ← GSYM INT_OF_NUM_ADD] THEN
    SIMP_TAC [← GSYM INT_OF_NUM_SUB, LT_IMP_LE, DIVISION, DIMINDEX_NONZERO] THEN
    MATCH_MP_TAC (← INTEGER_RULE
     (← q r"(k:int == n) (mod d)
    ==> (i - n == i + (d - k)) (mod d)")) THEN
    REWRITE_TAC [CONG_LMOD, INT_OF_NUM_REM, ← GSYM num_congruent] THEN
    CONV_TAC (fun t => (NUMBER_RULE t).run))

  let WORD_ROR_PERIODIC ← prove
   r"!(w:N word) m n.
        (m == n) (mod dimindex(:N)) ==> word_ror w m = word_ror w n"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [word_ror] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP (← NUMBER_RULE
     (← q r"(m == n) (mod d) ==> !i:num. (i + m == i + n) (mod d)"))) THEN
    SIMP_TAC [CONG])

  let WORD_ROR_MOD ← prove
   r"!(w:N word) n. word_ror w n = word_ror w (n MOD dimindex(:N))"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC WORD_ROR_PERIODIC THEN
    REWRITE_TAC [CONG_RMOD] THEN CONV_TAC (fun t => (NUMBER_RULE t).run))

  let WORD_ROR_EQ_SELF ← prove
   r"!(w:N word) n. dimindex(:N) divides n ==> word_ror w n = w"
   (SIMP_TAC [divides, LEFT_IMP_EXISTS_THM, word_ror] THEN
    ONCE_REWRITE_TAC [← ARITH_RULE (← q r"i + d * n:num = n * d + i")] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [MOD_MULT_ADD] THEN
    REWRITE_TAC [WORD_EQ_BITS, BIT_WORD_OF_BITS] THEN X_GEN_TAC (← q "i:num") THEN
    ASM_CASES_TAC (← q "i < dimindex(:N)") THEN ASM_SIMP_TAC [MOD_LT, IN_ELIM_THM] THEN
    ASM_MESON_TAC [BIT_TRIVIAL, NOT_LE])

  let WORD_ROR_ZERO ← prove
   r"!w:N word. word_ror w 0 = w"
   (GEN_TAC THEN MATCH_MP_TAC WORD_ROR_EQ_SELF THEN CONV_TAC (fun t => (NUMBER_RULE t).run))

  let WORD_ROL_PERIODIC ← prove
   r"!(w:N word) m n.
        (m == n) (mod dimindex(:N)) ==> word_rol w m = word_rol w n"
   (SIMP_TAC [CONG, WORD_ROL_ROR_GEN])

  let WORD_ROL_MOD ← prove
   r"!(w:N word) n. word_rol w n = word_rol w (n MOD dimindex(:N))"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC WORD_ROL_PERIODIC THEN
    REWRITE_TAC [CONG_RMOD] THEN CONV_TAC (fun t => (NUMBER_RULE t).run))

  let WORD_ROL_EQ_SELF ← prove
   r"!(w:N word) n. dimindex(:N) divides n ==> word_rol w n = w"
   (REWRITE_TAC [divides] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN
    SIMP_TAC [← GSYM MOD_EQ_0, WORD_ROL_ROR_GEN, SUB_0] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC WORD_ROR_EQ_SELF THEN
    CONV_TAC (fun t => (NUMBER_RULE t).run))

  let WORD_ROL_ZERO ← prove
   r"!w:N word. word_rol w 0 = w"
   (GEN_TAC THEN MATCH_MP_TAC WORD_ROL_EQ_SELF THEN CONV_TAC (fun t => (NUMBER_RULE t).run))

  let WORD_ROR_ROL ← prove
   r"!(w:N word) n.
        n <= dimindex(:N) ==> word_ror w n = word_rol w (dimindex(:N) - n)"
   (REWRITE_TAC [LE_LT] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [WORD_ROR_ROL_GEN, MOD_LT, MOD_REFL, SUB_0, SUB_REFL] THEN
    MATCH_MP_TAC WORD_ROL_PERIODIC THEN CONV_TAC (fun t => (NUMBER_RULE t).run))

  let WORD_ROL_ROR ← prove
   r"!(w:N word) n.
        n <= dimindex(:N) ==> word_rol w n = word_ror w (dimindex(:N) - n)"
   (REWRITE_TAC [LE_LT] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [WORD_ROL_ROR_GEN, MOD_LT, MOD_REFL, SUB_0, SUB_REFL] THEN
    MATCH_MP_TAC WORD_ROR_PERIODIC THEN CONV_TAC (fun t => (NUMBER_RULE t).run))

  let WORD_ROR_SHIFTS ← prove
   r"!(w:N word) n.
        n <= dimindex(:N)
        ==> word_ror w n =
            word_or (word_ushr w n) (word_shl w (dimindex(:N) - n))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [word_ror] THEN
    SIMP_TAC [WORD_EQ_BITS, BIT_WORD_OF_BITS, BIT_WORD_OR] THEN
    X_GEN_TAC (← q "i:num") THEN ASM_CASES_TAC (← q "i < dimindex(:N)") THEN
    ASM_REWRITE_TAC [IN_ELIM_THM, BIT_WORD_USHR, BIT_WORD_SHL] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"d - n <= i <=> ~(i + n:num < d)")] THEN
    ASM_CASES_TAC (← q "i + n < dimindex(:N)") THEN ASM_SIMP_TAC [MOD_LT] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [NOT_LT]) THEN ASM_SIMP_TAC [BIT_TRIVIAL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN
    EXISTS_TAC (← q "1") THEN ASM_ARITH_TAC)

  let WORD_ROL_SHIFTS ← prove
   r"!(w:N word) n.
        n <= dimindex(:N)
        ==> word_rol w n =
            word_or (word_shl w n) (word_ushr w (dimindex(:N) - n))"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [WORD_ROL_ROR] THEN
    ASM_SIMP_TAC [WORD_ROR_SHIFTS, ← ARITH_RULE (← q r"n - m:num <= n")] THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"m:num <= n ==> n - (n - m) = m")] THEN
    SIMP_TAC [WORD_EQ_BITS, BIT_WORD_OR, DISJ_SYM])

  let BIT_WORD_ROR ← prove
   r"!(w:N word) n i.
        bit i (word_ror w n) =
        if i + n MOD dimindex(:N) < dimindex(:N)
        then bit (i + n MOD dimindex(:N)) w
        else i < dimindex(:N) /\
             bit ((i + n MOD dimindex(:N)) - dimindex(:N)) w"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [WORD_ROR_MOD] THEN
    SIMP_TAC [WORD_ROR_SHIFTS, MOD_LT_EQ, LT_IMP_LE, DIMINDEX_NONZERO] THEN
    REWRITE_TAC [BIT_WORD_OR, BIT_WORD_SHL, BIT_WORD_USHR] THEN
    COND_CASES_TAC THENL
     [ASM_CASES_TAC (← q r"bit (i + n MOD dimindex(:N)) (w:N word)") THEN
      ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
      ASM_CASES_TAC (← q "i < dimindex(:N)") THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC (← TAUT (← q r"~p /\ q /\ (r <=> r') ==> (p \/ q /\ r <=> r')")) THEN
      REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC [BIT_TRIVIAL, ← GSYM NOT_LT],
        ASM_ARITH_TAC,
        AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]])

  let BIT_WORD_ROL ← prove
   r"!(w:N word) n i.
        bit i (word_rol w n) =
        if i < n MOD dimindex(:N)
        then bit (i + (dimindex(:N) - n MOD dimindex(:N))) w
        else i < dimindex(:N) /\ bit (i - n MOD dimindex(:N)) w"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [WORD_ROL_MOD] THEN
    SIMP_TAC [WORD_ROL_SHIFTS, MOD_LT_EQ, LT_IMP_LE, DIMINDEX_NONZERO] THEN
    REWRITE_TAC [BIT_WORD_OR, BIT_WORD_SHL, BIT_WORD_USHR] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [← GSYM NOT_LT] THENL
     [MATCH_MP_TAC (← TAUT (← q r"p ==> (p /\ q <=> q)")) THEN
      TRANS_TAC LT_TRANS (← q "n MOD dimindex(:N)") THEN
      ASM_REWRITE_TAC [MOD_LT_EQ, DIMINDEX_NONZERO],
      ASM_CASES_TAC (← q "i < dimindex(:N)") THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC (← TAUT (← q r"(q <=> F) ==> (p \/ q <=> p)")) THEN
      MATCH_MP_TAC BIT_TRIVIAL THEN ASM_ARITH_TAC])

  let WORD_ROR_COMPOSE ← prove
   r"!(x:N word) m n. word_ror (word_ror x m) n = word_ror x (m + n)"
   (REWRITE_TAC [word_ror, BIT_WORD_OF_BITS, IN_ELIM_THM] THEN
    SIMP_TAC [MOD_LT_EQ, DIMINDEX_NONZERO] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC [ADD_AC])

  let WORD_ROL_COMPOSE ← prove
   r"!(x:N word) m n. word_rol (word_rol x m) n = word_rol x (m + n)"
   (REWRITE_TAC [WORD_ROL_ROR_GEN, WORD_ROR_COMPOSE] THEN
    REPEAT GEN_TAC THEN MATCH_MP_TAC WORD_ROR_PERIODIC THEN
    REWRITE_TAC [num_congruent, ← GSYM INT_OF_NUM_ADD] THEN
    SIMP_TAC [← GSYM INT_OF_NUM_SUB, LT_IMP_LE, MOD_LT_EQ, DIMINDEX_NONZERO] THEN
    REWRITE_TAC [← INTEGER_RULE
     (← q r"((n - a) + (n - b):int == (n - c)) (mod n) <=> (a + b == c) (mod n)")] THEN
    REWRITE_TAC [INT_OF_NUM_ADD, ← GSYM num_congruent, CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC)

  let VAL_WORD_ROR ← prove
   r"!(w:N word) k.
     k <= dimindex(:N)
     ==> val(word_ror w k) =
         2 EXP (dimindex(:N) - k) * val w MOD 2 EXP k + val w DIV 2 EXP k"
   (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [ADD_SYM] THEN
    ASM_SIMP_TAC [WORD_ROR_SHIFTS] THEN
    W (MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_OR_DISJOINT o lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [WORD_EQ_BITS_ALT] THEN
      SIMP_TAC [BIT_WORD_AND, BIT_WORD_USHR, BIT_WORD_SHL, BIT_WORD_0] THEN
      REPEAT STRIP_TAC THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP (← MESON [BIT_TRIVIAL, NOT_LE]
       (← q r"bit i (w:N word) ==> i < dimindex(:N)")))) THEN
      ASM_ARITH_TAC,
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC [VAL_WORD_USHR, VAL_WORD_SHL] THEN AP_TERM_TAC THEN
    REWRITE_TAC [← GSYM MOD_MULT2, ← GSYM EXP_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC)

  let VAL_WORD_ROL ← prove
   r"!(w:N word) k.
        k <= dimindex(:N)
        ==> val(word_rol w k) =
            2 EXP k * val w MOD 2 EXP (dimindex(:N) - k) +
            val w DIV 2 EXP (dimindex(:N) - k)"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [WORD_ROL_ROR] THEN
    SIMP_TAC [VAL_WORD_ROR, ← ARITH_RULE (← q r"n - m:num <= n")] THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"k:num <= n ==> n - (n - k) = k")])

  let word_ule ← new_definition r"word_ule = relational2 (<=)"
  let word_uge ← new_definition r"word_uge = relational2 (>=)"
  let word_ult ← new_definition r"word_ult = relational2 (<)"
  let word_ugt ← new_definition r"word_ugt = relational2 (>)"

  let word_ile ← new_definition r"word_ile = irelational2 (<=)"
  let word_ige ← new_definition r"word_ige = irelational2 (>=)"
  let word_ilt ← new_definition r"word_ilt = irelational2 (<)"
  let word_igt ← new_definition r"word_igt = irelational2 (>)"

  let WORD_ULT ← prove
   r"!x y:N word. word_ult x y <=> val x < val y"
   (REWRITE_TAC [word_ult, relational2])

  let WORD_ULE ← prove
   r"!x y:N word. word_ule x y <=> val x <= val y"
   (REWRITE_TAC [word_ule, relational2])

  let WORD_UGT ← prove
   r"!x y:N word. word_ugt x y <=> val x > val y"
   (REWRITE_TAC [word_ugt, relational2])

  let WORD_UGE ← prove
   r"!x y:N word. word_uge x y <=> val x >= val y"
   (REWRITE_TAC [word_uge, relational2])

  let WORD_ILT ← prove
   r"!x y:N word. word_ilt x y <=> ival x < ival y"
   (REWRITE_TAC [word_ilt, irelational2])

  let WORD_ILE ← prove
   r"!x y:N word. word_ile x y <=> ival x <= ival y"
   (REWRITE_TAC [word_ile, irelational2])

  let WORD_IGT ← prove
   r"!x y:N word. word_igt x y <=> ival x > ival y"
   (REWRITE_TAC [word_igt, irelational2])

  let WORD_IGE ← prove
   r"!x y:N word. word_ige x y <=> ival x >= ival y"
   (REWRITE_TAC [word_ige, irelational2])

  return { WORD_SHL_WORD, WORD_SHL_AS_IWORD, WORD_SHL_IWORD, WORD_MUL_EXPAND, word_ushr,
           VAL_WORD_USHR, WORD_USHR_EQ_0, BIT_WORD_USHR, WORD_USHR_WORD_OF_BITS,
           WORD_USHR_0, WORD_USHR_ZERO, WORD_USHR_COMPOSE, WORD_USHR_MSB_ALT,
           WORD_USHR_MSB, WORD_USHR_MSB_EQ, WORD_POPCOUNT_SHL, WORD_POPCOUNT_USHR,
           word_ishr, IVAL_WORD_ISHR, WORD_ISHR_EQ_0, BIT_WORD_ISHR, WORD_ISHR_WORD_OF_BITS,
           WORD_ISHR_0, WORD_ISHR_ZERO, WORD_ISHR_COMPOSE, WORD_ISHR_UNIQUE,
           IVAL_WORD_ISHR_SHL_UNIQUE, word_ror, word_rol, WORD_ROR_ROL_GEN,
           WORD_ROL_ROR_GEN, WORD_ROR_PERIODIC, WORD_ROR_MOD, WORD_ROR_EQ_SELF,
           WORD_ROR_ZERO, WORD_ROL_PERIODIC, WORD_ROL_MOD, WORD_ROL_EQ_SELF, WORD_ROL_ZERO,
           WORD_ROR_ROL, WORD_ROL_ROR, WORD_ROR_SHIFTS, WORD_ROL_SHIFTS, BIT_WORD_ROR,
           BIT_WORD_ROL, WORD_ROR_COMPOSE, WORD_ROL_COMPOSE, VAL_WORD_ROR, VAL_WORD_ROL,
           word_ule, word_uge, word_ult, word_ugt, word_ile, word_ige, word_ilt, word_igt,
           WORD_ULT, WORD_ULE, WORD_UGT, WORD_UGE, WORD_ILT, WORD_ILE, WORD_IGT, WORD_IGE }

/- ------------------------------------------------------------------------- -/
/- Simple "propagate value modulo" decision procedure.                       -/
/- ------------------------------------------------------------------------- -/

/-- The recursive `conv` of `WORD_VAL_CONG_CONV` (words.ml 3393-3398). -/
partial def wordValCongConv [HolBase] (conv_special conv_unary conv_binary conv_self : ioconv) :
    ioconv := fun tm =>
  let conv := wordValCongConv conv_special conv_unary conv_binary conv_self
  ((conv_special THENC LAND_CONV (RAND_CONV (LAND_CONV conv))) ORELSEC
   (conv_unary THENC LAND_CONV (RAND_CONV conv)) ORELSEC
   (conv_binary THENC LAND_CONV (BINOP_CONV conv)) ORELSEC
   (conv_self THENC conv) ORELSEC
   SUB_CONV conv ORELSEC (fun t => pure (.ok (REFL t)))) tm

structure WordRule where
  /-- `WORD_VAL_CONG_CONV` (words.ml 3261-3403). -/
  WORD_VAL_CONG_CONV : ioconv
  /-- `WORD_RULE` (words.ml 3405-3463). -/
  WORD_RULE : term → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupWordRule [HolBase] (D : WordsDeps) (BBitval : Bitval) (BVal : Val) (BIval : Ival) (BWordOps1 : WordOps1) (BWordOps2 : WordOps2) :
    ExceptT String IO WordRule := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, INTEGER_RULE, INT_POLY_CONV, INT_REM_DOWN_CONV, MOD_DOWN_CONV,
        NUMBER_RULE, REAL_POLY_CONV, .. } := D
  let { CONG, DIMINDEX_NONZERO, .. } := D.core1
  let { INT_OF_NUM_ADD, INT_OF_NUM_CLAUSES, INT_OF_NUM_MUL, INT_OF_NUM_POW,
        INT_OF_NUM_REM, INT_REM_EQ, INT_SUB_0, .. } := D.core2
  let { MOD_MOD_REFL, .. } := D.core3
  let { REAL_OF_INT_CLAUSES, REAL_OF_NUM_CLAUSES, REAL_OF_NUM_SUM_NUMSEG, REAL_SUB_0,
        REAL_SUB_RZERO, SUM_ADD_NUMSEG, SUM_EQ_0_NUMSEG, SUM_LMUL, SUM_NEG, SUM_RMUL,
        SUM_SUB_NUMSEG, .. } := D.core4
  let { BINT_POLY_CONV, BITVAL_CLAUSES, INT_BITVAL_AND, INT_BITVAL_IFF, INT_BITVAL_IMP,
        INT_BITVAL_NOT, INT_BITVAL_OR, .. } := BBitval
  let { BIT_WORD_0, VAL, VAL_EQ, VAL_MOD_REFL, VAL_WORD, VAL_WORD_0, .. } := BVal
  let { IVAL_CONG, IVAL_EQ, IVAL_VAL_CONG, VAL_IWORD_CONG, .. } := BIval
  let { BIT_WORD_AND_ALT, BIT_WORD_NOT, BIT_WORD_OR_ALT, BIT_WORD_XOR_ALT,
        INT_CONG_WORD_ADD, INT_CONG_WORD_NEG, INT_CONG_WORD_SUB, INT_VAL_WORD_NOT, .. } := BWordOps1
  let { INT_CONG_WORD_MUL, VAL_WORD_SHL, .. } := BWordOps2
  -- @@SCOPE END

  let WORD_VAL_CONG_CONV ← do
    -- let ... and ... : evaluated left to right.
    let VAL_WORD_ADD_REM ← prove
     r"!x y:N word.
          &(val(word_add x y)) rem (&2 pow dimindex(:N)) =
          ((&(val x) rem (&2 pow dimindex(:N))) +
           (&(val y) rem (&2 pow dimindex(:N)))) rem (&2 pow dimindex(:N))"
     (REWRITE_TAC [← REWRITE_RULE [← GSYM INT_REM_EQ] INT_CONG_WORD_ADD] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC [])
    let VAL_WORD_SUB_REM ← prove
     r"!x y:N word.
          &(val(word_sub x y)) rem (&2 pow dimindex(:N)) =
          ((&(val x) rem (&2 pow dimindex(:N))) -
           (&(val y) rem (&2 pow dimindex(:N)))) rem (&2 pow dimindex(:N))"
     (REWRITE_TAC [← REWRITE_RULE [← GSYM INT_REM_EQ] INT_CONG_WORD_SUB] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC [])
    let VAL_WORD_NEG_REM ← prove
     r"!x:N word.
          &(val(word_neg x)) rem (&2 pow dimindex(:N)) =
          (--(&(val x) rem (&2 pow dimindex(:N)))) rem (&2 pow dimindex(:N))"
     (REWRITE_TAC [← REWRITE_RULE [← GSYM INT_REM_EQ] INT_CONG_WORD_NEG] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC [])
    let VAL_WORD_NOT_REM ← prove
     r"!x:N word.
          &(val(word_not x)) rem (&2 pow dimindex(:N)) =
          (--(&(val x) rem (&2 pow dimindex(:N)) + &1))
          rem (&2 pow dimindex(:N))"
     (REWRITE_TAC [INT_VAL_WORD_NOT] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN
      REWRITE_TAC [INT_REM_EQ] THEN CONV_TAC (fun t => (INTEGER_RULE t).run))
    let VAL_WORD_MUL_REM ← prove
     r"!x y:N word.
          &(val(word_mul x y)) rem (&2 pow dimindex(:N)) =
          ((&(val x) rem (&2 pow dimindex(:N))) *
           (&(val y) rem (&2 pow dimindex(:N)))) rem (&2 pow dimindex(:N))"
     (REWRITE_TAC [← REWRITE_RULE [← GSYM INT_REM_EQ] INT_CONG_WORD_MUL] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC [])
    let VAL_IWORD_REM ← prove
     r"!x. &(val(iword x:N word)) rem (&2 pow dimindex(:N)) =
         x rem (&2 pow dimindex(:N))"
     (REWRITE_TAC [INT_REM_EQ, VAL_IWORD_CONG])
    let VAL_WORD_REM ← prove
     r"!n. &(val(word n:N word)) rem (&2 pow dimindex(:N)) =
         &n rem (&2 pow dimindex(:N))"
     (REWRITE_TAC [VAL_WORD, INT_OF_NUM_REM, INT_OF_NUM_POW] THEN
      REWRITE_TAC [MOD_MOD_REFL])
    let VAL_WORD_SHL_REM ← prove
     r"!(x:N word) n.
      &(val(word_shl x n)) rem (&2 pow dimindex(:N)) =
      (&2 pow n * &(val x) rem (&2 pow dimindex(:N)))
      rem (&2 pow dimindex(:N))"
     (REWRITE_TAC [INT_OF_NUM_CLAUSES, INT_OF_NUM_REM] THEN
      REWRITE_TAC [VAL_WORD_SHL] THEN CONV_TAC MOD_DOWN_CONV THEN
      REWRITE_TAC [])
    let INT_OF_NUMOP_REM ← prove
     r"&(x + y) rem (&2 pow dimindex(:N)) =
     (&x rem (&2 pow dimindex(:N)) +
      &y rem (&2 pow dimindex(:N))) rem (&2 pow dimindex(:N)) /\
     &(x * y) rem (&2 pow dimindex(:N)) =
     (&x rem (&2 pow dimindex(:N)) *
      &y rem (&2 pow dimindex(:N))) rem (&2 pow dimindex(:N))"
     (REWRITE_TAC [← GSYM INT_OF_NUM_ADD, ← GSYM INT_OF_NUM_MUL] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC [])
    let INT_OF_INTOP_REM ← prove
     r"(x + y) rem (&2 pow dimindex(:N)) =
     (x rem (&2 pow dimindex(:N)) +
      y rem (&2 pow dimindex(:N))) rem (&2 pow dimindex(:N)) /\
     (x - y) rem (&2 pow dimindex(:N)) =
     (x rem (&2 pow dimindex(:N)) -
      y rem (&2 pow dimindex(:N))) rem (&2 pow dimindex(:N)) /\
     (x * y) rem (&2 pow dimindex(:N)) =
     (x rem (&2 pow dimindex(:N)) *
      y rem (&2 pow dimindex(:N))) rem (&2 pow dimindex(:N))"
     (CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC [])
    let INT_OF_NEG_REM ← prove
     r"(--x) rem (&2 pow dimindex(:N)) =
     (--(x rem (&2 pow dimindex(:N)))) rem (&2 pow dimindex(:N))"
     (CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC [])
    let INT_REM_REM_REFL ← prove
     r"(x rem (&2 pow dimindex(:N))) rem (&2 pow dimindex(:N)) =
     x rem (&2 pow dimindex(:N))"
     (CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC [])
    let IVAL_VAL_REM ← prove
     r"!x:N word. ival x rem (&2 pow dimindex(:N)) =
                &(val x) rem (&2 pow dimindex(:N))"
     (REWRITE_TAC [INT_REM_EQ, IVAL_VAL_CONG])
    let topth ← prove
     r"(!v w:N word.
          v = w <=>
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N))) /\
     (!(v:N word) (w:N word).
          val v = val w <=>
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N))) /\
     (!(v:N word) (w:N word).
          val v MOD 2 EXP dimindex(:N) = val w MOD 2 EXP dimindex(:N) <=>
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N))) /\
     (!(v:N word) (w:N word).
          (val v == val w) (mod (2 EXP dimindex(:N))) <=>
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N))) /\
     (!(v:N word) (w:N word).
          &(val v):int = &(val w) <=>
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N))) /\
     (!(v:N word) (w:N word).
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N)) <=>
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N))) /\
     (!(v:N word) (w:N word).
          (&(val v):int == &(val w)) (mod (&2 pow dimindex(:N))) <=>
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N))) /\
     (!(v:N word) (w:N word).
          ival v = ival w <=>
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N))) /\
     (!(v:N word) (w:N word).
          ival v rem (&2 pow dimindex(:N)) =
          ival w rem (&2 pow dimindex(:N)) <=>
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N))) /\
     (!(v:N word) (w:N word).
          (ival v == ival w) (mod (&2 pow dimindex(:N))) <=>
          &(val v) rem (&2 pow dimindex(:N)) =
          &(val w) rem (&2 pow dimindex(:N)))"
     (REWRITE_TAC [IVAL_EQ, IVAL_CONG,
                   ← REWRITE_RULE [← GSYM INT_REM_EQ] IVAL_CONG] THEN
      REWRITE_TAC [CONG, ← GSYM INT_REM_EQ, ← GSYM VAL_EQ] THEN
      ONCE_REWRITE_TAC [← GSYM VAL_MOD_REFL] THEN
      REWRITE_TAC [← GSYM INT_OF_NUM_CLAUSES, ← GSYM INT_OF_NUM_REM] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC [])
    let conv_special ← GEN_REWRITE_CONV_NET id [VAL_WORD_NOT_REM]
    let conv_unary ← GEN_REWRITE_CONV_NET id
     [VAL_WORD_NEG_REM, INT_OF_NEG_REM, VAL_WORD_SHL_REM]
    let conv_binary ← GEN_REWRITE_CONV_NET id
     [VAL_WORD_ADD_REM, VAL_WORD_SUB_REM, VAL_WORD_MUL_REM,
      INT_OF_NUMOP_REM, INT_OF_INTOP_REM]
    let conv_self ← GEN_REWRITE_CONV_NET id
     [VAL_IWORD_REM, VAL_WORD_REM, IVAL_VAL_REM, INT_REM_REM_REFL]
    let conv := wordValCongConv conv_special conv_unary conv_binary conv_self
    pure ((← GEN_REWRITE_CONV_NET id [topth]) THENC
          conv THENC
          INT_REM_DOWN_CONV THENC
          (← GEN_REWRITE_CONV_NET id [INT_REM_EQ]))

  let WORD_RULE ← do
    let plus_tm ← q "(+):int->int->int"
    let soppify := striplist (dest_binop plus_tm)
    let pth ← prove
     r"!k. (x == &0) (mod (&2 pow dimindex(:N))) <=>
         (--k * &(val(word_not(word 0:N word))) + (x - k):int == &0)
         (mod (&2 pow dimindex(:N)))"
     (REWRITE_TAC [INT_VAL_WORD_NOT, VAL_WORD_0] THEN
      CONV_TAC (fun t => (INTEGER_RULE t).run))
    -- WORD_UNBLAST_TAC.  OCaml builds the THEN chain right to left, so the
    -- ARITH_RULE near its end is evaluated before the INTEGER_RULE.
    let arB ← ARITH_RULE (← q r"i <= n - 1 ==> ~(n = 0) ==> i < n")
    let irA ← INTEGER_RULE (← q r"(x:int == y) (mod n) <=> (x - y == &0) (mod n)")
    let WORD_UNBLAST_TAC : tactic ← do pure (
      REPEAT STRIP_TAC THEN
      REWRITE_TAC [REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC [← GSYM INT_OF_NUM_CLAUSES] THEN
      TRY (GEN_REWRITE_TAC id [irA] THEN
           CONV_TAC (RATOR_CONV (LAND_CONV INT_POLY_CONV)) THEN
           (fun gl => ExceptT.run do
             match (soppify (← liftExcept (do lhand (← rator gl.2)))).filter
                     HolMath.Int.is_intconst with
             | [c] => ExceptT.mk ((GEN_REWRITE_TAC id [← SPEC c pth] THEN
                                   CONV_TAC (RATOR_CONV (LAND_CONV INT_POLY_CONV))) gl)
             | _ => ExceptT.mk (ALL_TAC gl)) THEN
           GEN_REWRITE_TAC id [← GSYM INT_REM_EQ] THEN
           AP_THM_TAC THEN AP_TERM_TAC) THEN
      REWRITE_TAC [← GSYM REAL_OF_INT_CLAUSES] THEN
      ONCE_REWRITE_TAC [← GSYM REAL_SUB_0] THEN
      CONV_TAC (LAND_CONV REAL_POLY_CONV) THEN
      REWRITE_TAC [VAL, REAL_OF_NUM_SUM_NUMSEG] THEN
      REWRITE_TAC [← GSYM SUM_ADD_NUMSEG, ← GSYM SUM_SUB_NUMSEG,
                  ← GSYM SUM_LMUL, ← GSYM SUM_RMUL, ← GSYM SUM_NEG] THEN
      REWRITE_TAC [← GSYM REAL_OF_NUM_CLAUSES, REAL_SUB_RZERO] THEN
      MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC [REAL_OF_INT_CLAUSES] THEN
      FIRST_X_ASSUM (MP_TAC o MATCH_MP arB) THEN
      REWRITE_TAC [DIMINDEX_NONZERO] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC [BIT_WORD_AND_ALT, BIT_WORD_XOR_ALT, BIT_WORD_OR_ALT,
                       BIT_WORD_NOT, BIT_WORD_0] THEN
      REWRITE_TAC [INT_BITVAL_AND, INT_BITVAL_OR, INT_BITVAL_NOT,
                   INT_BITVAL_IMP, INT_BITVAL_IFF, BITVAL_CLAUSES] THEN
      GEN_REWRITE_TAC id [← GSYM INT_SUB_0] THEN
      CONV_TAC (LAND_CONV BINT_POLY_CONV) THEN REWRITE_TAC [] THEN
      HolCore.Tactics.NO_TAC)
    let wordprover (tm : term) : ExceptT String IO thm :=
      tryWith (NUMBER_RULE tm)
        (ExceptT.mk (HolCore.Tactics.prove HolBase.B tm WORD_UNBLAST_TAC))
    pure fun (tm : term) =>
      tryCatch (do
          let (avs, bod) := strip_forall tm
          let th ← ExceptT.mk (ONCE_DEPTH_CONV WORD_VAL_CONG_CONV bod)
          GENL avs (← EQT_ELIM (← TRANS th
            (← EQT_INTRO (← wordprover (← liftExcept (rand (concl th))))))))
        (fun m => do
          let s ← HolCore.Printer.string_of_term tm
          throw ("WORD_RULE `" ++ s ++ "`: " ++ m))

  return { WORD_VAL_CONG_CONV, WORD_RULE }

/- ------------------------------------------------------------------------- -/
/- A somewhat complementary purely bitwise decision procedure.               -/
/- ------------------------------------------------------------------------- -/

structure WordBitwise where
  /-- `WORD_BITWISE_RULE` (words.ml 3493-3497). -/
  WORD_BITWISE_RULE : term → ExceptT String IO thm
  /-- `WORD_BITWISE_TAC` (words.ml 3499), the second binding. -/
  WORD_BITWISE_TAC : tactic
  deriving Inhabited

@[nospecialize]
def setupWordBitwise [HolBase] (D : WordsDeps) (BWordType : WordType) (BBitsOfWord : BitsOfWord) (BVal : Val) (BWordOps1 : WordOps1) :
    ExceptT String IO WordBitwise := do
  -- @@SCOPE BEGIN
  let { MESON, .. } := D
  let { IN_INSERT, IN_UNIV, .. } := D.core2
  let { NOT_IN_EMPTY, .. } := D.core3
  let { WORD_EQ_BITS_ALT, .. } := BWordType
  let { BIT_WORD_OF_BITS, .. } := BBitsOfWord
  let { BIT_WORD_0, .. } := BVal
  let { BIT_WORD_AND, BIT_WORD_NOT, BIT_WORD_OR, BIT_WORD_XOR, .. } := BWordOps1
  -- @@SCOPE END

  -- The first WORD_BITWISE_TAC (words.ml 3468-3491).
  let WORD_BITWISE_TAC0 ← do
    let WORD_BITWISE_CONV :=
      (← GEN_REWRITE_CONV_NET id [WORD_EQ_BITS_ALT]) THENC
      (← GEN_REWRITE_CONV_NET (BINDER_CONV o RAND_CONV o BINOP_CONV o TOP_DEPTH_CONV)
       [BIT_WORD_NOT, BIT_WORD_AND, BIT_WORD_OR,
        BIT_WORD_XOR, BIT_WORD_OF_BITS, BIT_WORD_0,
        IN_INSERT, NOT_IN_EMPTY, IN_UNIV])
    -- The three MESONs, in OCaml's order: the THEN chain right to left, and
    -- within `X ORELSE Y`, Y first.
    let m3 ← MESON [] (← q r"(!i. i < dimindex(:N) ==> (P i <=> Q i))
        ==> ((!i. i < dimindex(:N) ==> P i) <=>
             (!i. i < dimindex(:N) ==> Q i))")
    let m2 ← MESON [] (← q r"(!i. i < dimindex(:N) ==> P i ==> Q i)
        ==> (!i. i < dimindex(:N) ==> P i)
             ==> (!i. i < dimindex(:N) ==> Q i)")
    let m1 ← MESON [] (← q r"(!i. i < dimindex(:N) ==> P i) /\
             (!i. i < dimindex(:N) ==> Q i) <=>
             (!i. i < dimindex(:N) ==> P i /\ Q i)")
    pure (REPEAT GEN_TAC THEN
      CONV_TAC (ONCE_DEPTH_CONV WORD_BITWISE_CONV) THEN
      GEN_REWRITE_TAC DEPTH_CONV [m1] THEN
      TRY (MATCH_MP_TAC m2 ORELSE MATCH_MP_TAC m3) THEN
      TRY (GEN_TAC THEN DISCH_TAC) THEN ASM_REWRITE_TAC [] THEN
      CONV_TAC (fun t => (TAUT t).run))

  let WORD_BITWISE_RULE (tm : term) : ExceptT String IO thm :=
    tryCatch (ExceptT.mk (HolCore.Tactics.prove HolBase.B tm WORD_BITWISE_TAC0))
      (fun m => do
        let s ← HolCore.Printer.string_of_term tm
        throw ("WORD_BITWISE_RULE `" ++ s ++ "`: " ++ m))

  let WORD_BITWISE_TAC := CONV_TAC (fun t => (WORD_BITWISE_RULE t).run)

  return { WORD_BITWISE_RULE, WORD_BITWISE_TAC }

/- ------------------------------------------------------------------------- -/
/- Slightly ad hoc but useful reduction to linear arithmetic.                -/
/- ------------------------------------------------------------------------- -/

structure WordArith where
  /-- `WORD_ARITH` (words.ml 3530-3534). -/
  WORD_ARITH : term → ExceptT String IO thm
  /-- `WORD_ARITH_TAC` (words.ml 3536), the second binding. -/
  WORD_ARITH_TAC : tactic
  deriving Inhabited

@[nospecialize]
def setupWordArith [HolBase] (D : WordsDeps) (BVal : Val) (BIval : Ival) (BLimits : Limits) (BGeneralOps : GeneralOps) (BWordOps1 : WordOps1) (BWordOps2 : WordOps2) (BWordOps3 : WordOps3) (BWordRule : WordRule) :
    ExceptT String IO WordArith := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, DIMINDEX_CONV, INT_ARITH_TAC, INT_RED_CONV, NUM_RED_CONV, .. } := D
  let { DIMINDEX_GE_1, .. } := D.core1
  let { GE, GT, INT_GE, INT_GT, INT_OF_NUM_CLAUSES, INT_OF_NUM_REM, .. } := D.core2
  let { BIT_WORD_0, BIT_WORD_1, INT_VAL_BOUND, MSB_INT_VAL, TWICE_MSB, VAL_EQ,
        VAL_WORD, VAL_WORD_0, VAL_WORD_1, WORD_VAL, .. } := BVal
  let { INT_IVAL, .. } := BIval
  let { BIT_WORD_INT_MIN, INT_VAL_WORD_INT_MIN, .. } := BLimits
  let { irelational2, relational2, .. } := BGeneralOps
  let { BIT_WORD_AND, BIT_WORD_NOT, BIT_WORD_OR, BIT_WORD_XOR, INT_VAL_WORD_ADD_CASES,
        INT_VAL_WORD_NEG_CASES, INT_VAL_WORD_SUB_CASES, WORD_ADD, .. } := BWordOps1
  let { WORD_MUL, WORD_NOT_AS_SUB, .. } := BWordOps2
  let { WORD_IGE, WORD_IGT, WORD_ILE, WORD_ILT, WORD_UGE, WORD_UGT, WORD_ULE, WORD_ULT,
        WORD_USHR_MSB_EQ, .. } := BWordOps3
  let { WORD_RULE, .. } := BWordRule
  -- @@SCOPE END

  -- The first WORD_ARITH_TAC (words.ml 3505-3528).
  let WORD_ARITH_TAC0 ← do
    let msb_pth ← prove
     r"dimindex (:N) - 1 < dimindex(:N)"
     (REWRITE_TAC [DIMINDEX_GE_1, ← ARITH_RULE (← q r"n - 1 < n <=> 1 <= n")])
    let wordy (tm : term) : Bool :=
      match tm with | .Var _ (.Tyapp "word" [_]) => true | _ => false
    let wr ← WORD_RULE (← q r"word_shl (x:N word) 1 = word_add x x")
    pure (REPEAT (CONJ_TAC ORELSE GEN_TAC) THEN REWRITE_TAC [WORD_USHR_MSB_EQ] THEN
      REWRITE_TAC [BIT_WORD_OR, BIT_WORD_AND, BIT_WORD_NOT, BIT_WORD_XOR,
                   BIT_WORD_INT_MIN, BIT_WORD_1, BIT_WORD_0, msb_pth] THEN
      REWRITE_TAC [MSB_INT_VAL, WORD_NOT_AS_SUB, wr] THEN
      REWRITE_TAC [WORD_ULT, WORD_ULE, WORD_UGT, WORD_UGE,
                   WORD_ILT, WORD_ILE, WORD_IGT, WORD_IGE] THEN
      REWRITE_TAC [irelational2, relational2, ← GSYM VAL_EQ, INT_IVAL, WORD_VAL,
                   ← GSYM WORD_MUL, ← GSYM WORD_ADD, VAL_WORD] THEN
      REWRITE_TAC [INT_GT, INT_GE, GT, GE] THEN
      REWRITE_TAC [← GSYM INT_OF_NUM_CLAUSES, ← GSYM INT_OF_NUM_REM] THEN
      REWRITE_TAC [INT_VAL_WORD_NEG_CASES, INT_VAL_WORD_ADD_CASES,
                   INT_VAL_WORD_INT_MIN,
                   INT_VAL_WORD_SUB_CASES, INT_IVAL, VAL_WORD_0, VAL_WORD_1] THEN
      REWRITE_TAC [VAL_WORD, ← GSYM INT_OF_NUM_REM, ← GSYM INT_OF_NUM_CLAUSES] THEN
      (fun gl => MAP_EVERY (MP_TAC o (fun t => ISPEC t INT_VAL_BOUND))
                   (find_terms wordy gl.2) gl) THEN
      REWRITE_TAC [← CONJUNCT2 TWICE_MSB] THEN CONV_TAC (DEPTH_CONV
       (NUM_RED_CONV ORELSEC DIMINDEX_CONV ORELSEC INT_RED_CONV)) THEN
      INT_ARITH_TAC)

  let WORD_ARITH (tm : term) : ExceptT String IO thm :=
    tryCatch (ExceptT.mk (HolCore.Tactics.prove HolBase.B tm WORD_ARITH_TAC0))
      (fun m => do
        let s ← HolCore.Printer.string_of_term tm
        throw ("WORD_ARITH `" ++ s ++ "`: " ++ m))

  let WORD_ARITH_TAC := CONV_TAC (fun t => (WORD_ARITH t).run)

  return { WORD_ARITH, WORD_ARITH_TAC }

/- ------------------------------------------------------------------------- -/
/- Expand a constant into 2 EXP n where possible (e.g. |- 8 = 2 EXP 3), and  -/
/- expand "val x" or "val x DIV 2 EXP k" or "val x MOD 2 EXP k" into a sum   -/
/- over individual bits.                                                     -/
/- ------------------------------------------------------------------------- -/

/-- `blog` of `EMPOWER_CONV` (words.ml 3543-3546).  `//` is exact rational
    division in OCaml's Num. -/
partial def empowerBlog (k : Int) (n : Rat) : Except String Int :=
  if n == 1 then .ok k
  else if n < 1 then .error "Not a power of 2"
  else empowerBlog (k + 1) (n / 2)

structure ValExpand where
  /-- `EMPOWER_CONV` (words.ml 3542-3553). -/
  EMPOWER_CONV : ioconv
  /-- `VAL_EXPAND_CONV` (words.ml 3560-3599). -/
  VAL_EXPAND_CONV : ioconv
  deriving Inhabited

@[nospecialize]
def setupValExpand [HolBase] (D : WordsDeps) (BVal : Val) :
    ExceptT String IO ValExpand := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, EXPAND_NSUM_CONV, NUM_EQ_CONV, NUM_REDUCE_CONV, NUM_SUB_CONV,
        mk_small_numeral, .. } := D
  let { COND_CLAUSES, DIMINDEX_NONZERO, EXTENSION, .. } := D.core1
  let { IN_ELIM_THM, IN_NUMSEG, .. } := D.core2
  let { NSUM_CLAUSES, NUMSEG_LT, .. } := D.core3
  let { VAL, VAL_DIV, VAL_MOD, .. } := BVal
  -- @@SCOPE END

  let EMPOWER_CONV ← do
    let exp2 ← q "(EXP) 2"
    pure fun (tm : term) => ExceptT.run do
      match tm with
      | .Comb l r =>
        if l == exp2 && HolMath.Nums.is_numeral r then return REFL tm
      | _ => pure ()
      let th ← ExceptT.mk (NUM_REDUCE_CONV tm)
      let k ← liftExcept (do empowerBlog 0 (← dest_numeral (← rand (concl th))))
      let tm' ← liftExcept (do mk_comb exp2 (← mk_small_numeral k))
      TRANS th (← SYM (← ExceptT.mk (NUM_REDUCE_CONV tm')))

  let VAL_EXPAND_CONV ← do
    let pth_mod ← prove
     r"!(x:N word) k.
           val x MOD 2 EXP k =
           if k = 0 then 0
           else nsum (0..k-1) (\i. 2 EXP i * bitval(bit i x))"
     (REPEAT GEN_TAC THEN REWRITE_TAC [VAL_MOD, NUMSEG_LT] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [NSUM_CLAUSES])
    let pth_div ← prove
     r"!(x:N word) k.
           val x DIV 2 EXP k =
           nsum (k..dimindex(:N)-1) (\i. 2 EXP (i - k) * bitval(bit i x))"
     (REPEAT GEN_TAC THEN REWRITE_TAC [VAL_DIV] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_NUMSEG] THEN
      SIMP_TAC [DIMINDEX_NONZERO, ← ARITH_RULE
       (← q r"~(d = 0) ==> (x <= d - 1 <=> x < d)")])
    -- `!word_SIZE_CONV` is read here, when the rules are built.
    let sizeConv ← D.word_SIZE_CONV.get
    let pm (th : thm) : ioconv := fun t => (PART_MATCH lhand th t).run
    let base_rule :=
      pm VAL THENC
      LAND_CONV (RAND_CONV (LAND_CONV sizeConv THENC NUM_SUB_CONV))
    let div_rule :=
      RAND_CONV EMPOWER_CONV THENC
      pm pth_div THENC
      LAND_CONV (RAND_CONV (LAND_CONV sizeConv THENC NUM_SUB_CONV))
    let mod_rule :=
      RAND_CONV EMPOWER_CONV THENC
      pm pth_mod THENC
      RATOR_CONV (LAND_CONV NUM_EQ_CONV) THENC
      (← GEN_REWRITE_CONV_NET id [COND_CLAUSES]) THENC
      TRY_CONV (LAND_CONV (RAND_CONV NUM_SUB_CONV))
    let coreconv : ioconv := fun tm =>
      match tm with
      | .Comb (.Const "val" _) _ => base_rule tm
      | .Comb (.Comb (.Const "DIV" _) (.Comb (.Const "val" _) _)) _ => div_rule tm
      | .Comb (.Comb (.Const "MOD" _) (.Comb (.Const "val" _) _)) _ => mod_rule tm
      | _ => pure (.error "VAL_EXPAND_CONV: not of expected form")
    pure (coreconv THENC
          EXPAND_NSUM_CONV THENC ONCE_DEPTH_CONV NUM_SUB_CONV)

  return { EMPOWER_CONV, VAL_EXPAND_CONV }

/- ------------------------------------------------------------------------- -/
/- Zero extension and sign extension (also works for shortening modulo);     -/
/- sign-extension from a specific bit position; conditional AND and OR.      -/
/- ------------------------------------------------------------------------- -/

structure ZxSx where
  word_zx : thm
  VAL_WORD_ZX_GEN : thm
  VAL_WORD_ZX : thm
  WORD_ZX_ZX : thm
  WORD_ZX_0 : thm
  WORD_ZX_TRIVIAL : thm
  WORD_ZX_WORD : thm
  WORD_ZX_WORD_SIMPLE : thm
  WORD_ZX_1 : thm
  WORD_ZX_BITVAL : thm
  BIT_WORD_ZX : thm
  WORD_ZX_AND : thm
  WORD_ZX_OR : thm
  WORD_ZX_XOR : thm
  WORD_ZX_NOT : thm
  WORD_ZX_ADD : thm
  WORD_ZX_MUL : thm
  WORD_ZX_NEG : thm
  WORD_ZX_SUB : thm
  WORD_ZX_SHL : thm
  word_sx : thm
  IVAL_WORD_SX : thm
  WORD_SX_SX : thm
  WORD_SX_0 : thm
  WORD_SX_TRIVIAL : thm
  WORD_SX_ZX : thm
  word_sxfrom : thm
  BIT_WORD_SXFROM : thm
  IVAL_WORD_SXFROM_UNIQUE : thm
  word_cand : thm
  word_cor : thm
  WORD_CAND : thm
  WORD_COR : thm
  WORD_CAND_NE_0 : thm
  WORD_COR_NE_0 : thm
  WORD_CAND_EQ_0 : thm
  WORD_COR_EQ_0 : thm
  VAL_WORD_CAND : thm
  VAL_WORD_COR : thm
  BIT_WORD_CAND : thm
  BIT_WORD_COR : thm
  deriving Inhabited

@[nospecialize]
def setupZxSx [HolBase] (D : WordsDeps) (BBitval : Bitval) (BBinary : Binary) (BWordType : WordType) (BVal : Val) (BIval : Ival) (BWordOps1 : WordOps1) (BWordOps2 : WordOps2) (BWordOps3 : WordOps3) (BWordRule : WordRule) :
    ExceptT String IO ZxSx := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INTEGER_RULE, INT_ARITH,
        INT_REDUCE_CONV, MESON_TAC, MOD_DOWN_CONV, NUM_REDUCE_CONV, define,
        new_definition, .. } := D
  let { DIMINDEX_GE_1, DIMINDEX_NONZERO, DIV_MOD, EQ_IMP, EXP_ADD, .. } := D.core1
  let { FORALL_BOOL_THM, INT_LE_LMUL_EQ, INT_LT_IMP_NE, INT_LT_LMUL_EQ, INT_LT_POW2,
        INT_MUL_RNEG, INT_MUL_SYM, INT_POW_ADD, INT_POW_MONO, .. } := D.core2
  let { LE_EXISTS, LE_EXP, LE_REFL, LTE_TRANS, LT_EXISTS, MOD_0, MOD_EQ_SELF, MOD_LT,
        MOD_MOD_EXP_MIN, NOT_LE, NOT_SUC, .. } := D.core3
  let { BITVAL_CLAUSES, .. } := BBitval
  let { ODD_MOD_POW2, .. } := BBinary
  let { BIT_GUARD, BIT_TRIVIAL, WORD_EQ_BITS_ALT, .. } := BWordType
  let { BIT_VAL, BIT_WORD_0, BIT_WORD_1, VAL_BOUND, VAL_EQ, VAL_EQ_0, VAL_MOD_REFL,
        VAL_WORD, VAL_WORD_0, VAL_WORD_1, WORD_NE_10, .. } := BVal
  let { IVAL_BOUND, IVAL_EQ, IVAL_IWORD, IVAL_IWORD_GALOIS, IVAL_VAL, IVAL_WORD_0,
        IWORD_EQ, IWORD_IVAL, WORD_IWORD, .. } := BIval
  let { BIT_WORD_AND, BIT_WORD_NOT, BIT_WORD_OR, BIT_WORD_XOR, VAL_WORD_ADD,
        WORD_NEG_AS_ADD, .. } := BWordOps1
  let { BIT_WORD_SHL, VAL_WORD_MUL, VAL_WORD_SHL, .. } := BWordOps2
  let { BIT_WORD_ISHR, IVAL_WORD_ISHR_SHL_UNIQUE, WORD_SHL_AS_IWORD, .. } := BWordOps3
  let { WORD_RULE, .. } := BWordRule
  -- @@SCOPE END

  let word_zx ← new_definition
   r"(word_zx:(M)word->(N)word) w = word(val w)"

  let VAL_WORD_ZX_GEN ← prove
   r"!x. val((word_zx:(M)word->(N)word) x) = val x MOD 2 EXP dimindex(:N)"
   (GEN_TAC THEN REWRITE_TAC [word_zx, VAL_WORD])

  let VAL_WORD_ZX ← prove
   r"!x. dimindex(:M) <= dimindex(:N)
       ==> val((word_zx:(M)word->(N)word) x) = val x"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [VAL_WORD_ZX_GEN] THEN
    MATCH_MP_TAC MOD_LT THEN
    TRANS_TAC LTE_TRANS (← q "2 EXP dimindex(:M)") THEN
    ASM_REWRITE_TAC [LE_EXP, VAL_BOUND] THEN
    CONV_TAC NUM_REDUCE_CONV)

  let WORD_ZX_ZX ← prove
   r"!x. dimindex(:M) <= dimindex(:N)
       ==> (word_zx:N word->M word) ((word_zx:M word->N word) x) = x"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_ZX_GEN, MOD_MOD_EXP_MIN] THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"m <= n ==> MIN n m = m")] THEN
    REWRITE_TAC [VAL_MOD_REFL])

  let WORD_ZX_0 ← prove
   r"(word_zx:M word->N word) (word 0) = word 0"
   (REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_ZX_GEN, VAL_WORD_0, MOD_0])

  let WORD_ZX_TRIVIAL ← prove
   r"!x:N word. word_zx x = x"
   (SIMP_TAC [← GSYM VAL_EQ, VAL_WORD_ZX, LE_REFL])

  let WORD_ZX_WORD ← prove
   r"!n. (word_zx:M word->N word) (word n) = word (n MOD 2 EXP dimindex(:M))"
   (REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD, VAL_WORD_ZX_GEN])

  let WORD_ZX_WORD_SIMPLE ← prove
   r"!n. dimindex(:N) <= dimindex(:M)
       ==> word_zx(word n:M word):N word = word n"
   (SIMP_TAC [← GSYM VAL_EQ, VAL_WORD, VAL_WORD_ZX_GEN] THEN
    SIMP_TAC [MOD_MOD_EXP_MIN, ← ARITH_RULE (← q r"n <= m ==> MIN m n = n")])

  let WORD_ZX_1 ← prove
   r"(word_zx:M word->N word) (word 1) = word 1"
   (REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_ZX_GEN, VAL_WORD_1, MOD_EQ_SELF] THEN
    DISJ2_TAC THEN REWRITE_TAC [← ARITH_RULE (← q r"1 < n <=> 2 EXP 1 <= n")] THEN
    REWRITE_TAC [LE_EXP, DIMINDEX_GE_1, DIMINDEX_NONZERO] THEN ARITH_TAC)

  let WORD_ZX_BITVAL ← prove
   r"!b. (word_zx:M word->N word) (word(bitval b)) = word(bitval b)"
   (REWRITE_TAC [FORALL_BOOL_THM, BITVAL_CLAUSES, WORD_ZX_0, WORD_ZX_1])

  let BIT_WORD_ZX ← prove
   r"!x i. bit i ((word_zx:M word->N word) x) <=>
         i < dimindex(:N) /\ bit i x"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q "i < dimindex(:N)") THENL
     [ASM_REWRITE_TAC [BIT_VAL, VAL_WORD_ZX_GEN],
      ASM_MESON_TAC [BIT_TRIVIAL, NOT_LE]] THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q "d:num") SUBST1_TAC o REWRITE_RULE [LT_EXISTS]) THEN
    REWRITE_TAC [EXP_ADD, ← GSYM DIV_MOD, ODD_MOD_POW2, NOT_SUC])

  let WORD_ZX_AND ← prove
   r"!(x:M word) (y:M word).
        word_zx(word_and x y):N word =
        word_and (word_zx x) (word_zx y)"
   (REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_ZX, BIT_WORD_AND] THEN
    ONCE_REWRITE_TAC [BIT_GUARD] THEN CONV_TAC (fun t => (TAUT t).run))

  let WORD_ZX_OR ← prove
   r"!(x:M word) (y:M word).
        word_zx(word_or x y):N word =
        word_or (word_zx x) (word_zx y)"
   (REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_ZX, BIT_WORD_OR] THEN
    ONCE_REWRITE_TAC [BIT_GUARD] THEN CONV_TAC (fun t => (TAUT t).run))

  let WORD_ZX_XOR ← prove
   r"!(x:M word) (y:M word).
        word_zx(word_xor x y):N word =
        word_xor (word_zx x) (word_zx y)"
   (REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_ZX, BIT_WORD_XOR] THEN
    ONCE_REWRITE_TAC [BIT_GUARD] THEN CONV_TAC (fun t => (TAUT t).run))

  let WORD_ZX_NOT ← prove
   r"!x:M word.
        dimindex(:N) <= dimindex(:M)
        ==> word_zx(word_not x):N word = word_not(word_zx x)"
   (REPEAT STRIP_TAC THEN
    SIMP_TAC [WORD_EQ_BITS_ALT, BIT_WORD_ZX, BIT_WORD_NOT] THEN
    X_GEN_TAC (← q "i:num") THEN ASM_CASES_TAC (← q "bit i (x:M word)") THEN
    ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC)

  let WORD_ZX_ADD ← prove
   r"!(x:M word) (y:M word).
        dimindex(:N) <= dimindex(:M)
        ==> word_zx(word_add x y):N word =
            word_add (word_zx x) (word_zx y)"
   (REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_ZX_GEN, VAL_WORD_ADD, MOD_MOD_EXP_MIN] THEN
    SIMP_TAC [← ARITH_RULE (← q r"n <= m ==> MIN m n = n")] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC [])

  let WORD_ZX_MUL ← prove
   r"!(x:M word) (y:M word).
        dimindex(:N) <= dimindex(:M)
        ==> word_zx(word_mul x y):N word =
            word_mul (word_zx x) (word_zx y)"
   (REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_ZX_GEN, VAL_WORD_MUL, MOD_MOD_EXP_MIN] THEN
    SIMP_TAC [← ARITH_RULE (← q r"n <= m ==> MIN m n = n")] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC [])

  let WORD_ZX_NEG ← prove
   r"!x:M word.
        dimindex(:N) <= dimindex(:M)
        ==> word_zx(word_neg x):N word = word_neg(word_zx x)"
   (SIMP_TAC [WORD_NEG_AS_ADD, WORD_ZX_ADD, WORD_ZX_NOT, WORD_ZX_1])

  let WORD_ZX_SUB ← prove
   r"!(x:M word) (y:M word).
        dimindex(:N) <= dimindex(:M)
        ==> word_zx(word_sub x y):N word =
            word_sub (word_zx x) (word_zx y)"
   (REWRITE_TAC [← WORD_RULE (← q r"word_sub x y = word_add x (word_neg y)")] THEN
    SIMP_TAC [WORD_ZX_NEG, WORD_ZX_ADD])

  let WORD_ZX_SHL ← prove
   r"!(x:M word) n.
        dimindex(:N) <= dimindex(:M)
        ==> word_zx(word_shl x n):N word =
            word_shl (word_zx x) n"
   (REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_ZX_GEN, VAL_WORD_SHL, MOD_MOD_EXP_MIN] THEN
    SIMP_TAC [← ARITH_RULE (← q r"n <= m ==> MIN m n = n")] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC [])

  let word_sx ← new_definition
   r"(word_sx:(M)word->(N)word) w = iword(ival w)"

  let IVAL_WORD_SX ← prove
   r"!x. dimindex(:M) <= dimindex(:N)
       ==> ival((word_sx:(M)word->(N)word) x) = ival x"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [IVAL_IWORD, word_sx] THEN
    MATCH_MP_TAC IVAL_IWORD THEN
    MP_TAC (← ISPEC (← q "x:M word") IVAL_BOUND) THEN
    MATCH_MP_TAC (← INT_ARITH
     (← q r"m:int <= n ==> --m <= x /\ x < m ==> --n <= x /\ x < n")) THEN
    MATCH_MP_TAC INT_POW_MONO THEN CONV_TAC INT_REDUCE_CONV THEN
    ASM_ARITH_TAC)

  let WORD_SX_SX ← prove
   r"!x. dimindex(:M) <= dimindex(:N)
       ==> (word_sx:N word->M word) ((word_sx:M word->N word) x) = x"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM IVAL_EQ] THEN
    ONCE_REWRITE_TAC [word_sx] THEN ASM_SIMP_TAC [IVAL_WORD_SX, IWORD_IVAL])

  let WORD_SX_0 ← prove
   r"(word_sx:M word->N word) (word 0) = word 0"
   (REWRITE_TAC [← GSYM IVAL_EQ, word_sx, IVAL_WORD_0, ← GSYM WORD_IWORD])

  let WORD_SX_TRIVIAL ← prove
   r"!x:N word. word_sx x = x"
   (SIMP_TAC [← GSYM IVAL_EQ, IVAL_WORD_SX, LE_REFL])

  let WORD_SX_ZX ← prove
   r"!x. dimindex(:N) <= dimindex(:M)
       ==> (word_sx:M word->N word) x = word_zx x"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [word_sx, word_zx, WORD_IWORD, IWORD_EQ, IVAL_VAL] THEN
    MATCH_MP_TAC (← INTEGER_RULE
     (← q r"(p:int) divides q ==> (x - q * b == x) (mod p)")) THEN
    FIRST_X_ASSUM (CHOOSE_THEN SUBST1_TAC o REWRITE_RULE [LE_EXISTS]) THEN
    REWRITE_TAC [INT_POW_ADD] THEN CONV_TAC (fun t => (INTEGER_RULE t).run))

  let word_sxfrom ← define
   r"word_sxfrom n (x:N word) =
  word_ishr (word_shl x (dimindex(:N) - 1 - n)) (dimindex(:N) - 1 - n)"

  let BIT_WORD_SXFROM ← prove
   r"!n i (x:N word).
        bit i (word_sxfrom n x) <=> i < dimindex(:N) /\ bit (MIN n i) x"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [word_sxfrom, BIT_WORD_SHL, BIT_WORD_ISHR] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    EQ_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
    POP_ASSUM MP_TAC THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC)

  let IVAL_WORD_SXFROM_UNIQUE ← prove
   r"!(w:N word) k x.
        k < dimindex(:N)
        ==> (ival(word_sxfrom k w) = x <=>
             --(&2 pow k) <= x /\ x < &2 pow k /\
             (ival w == x) (mod (&2 pow (k + 1))))"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [word_sxfrom, IVAL_WORD_ISHR_SHL_UNIQUE] THEN
    REWRITE_TAC [IVAL_IWORD_GALOIS] THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [INT_MUL_SYM] WORD_SHL_AS_IWORD] THEN
    REWRITE_TAC [IWORD_EQ] THEN
    SUBGOAL_THEN
     (← q r"(&2:int) pow (dimindex(:N) - 1) =
    &2 pow (dimindex(:N) - 1 - k) * &2 pow k /\
   (&2:int) pow dimindex(:N) =
    &2 pow (dimindex(:N) - 1 - k) * &2 pow (k + 1)")
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC [← GSYM INT_POW_ADD] THEN CONJ_TAC THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC,
      SIMP_TAC [← GSYM INT_MUL_RNEG, INT_LE_LMUL_EQ, INT_LT_LMUL_EQ, INT_LT_POW2,
                INT_LT_IMP_NE, ← INTEGER_RULE
                 (← q r"(a * x:int == a * y) (mod (a * b)) <=>
               a = &0 \/ (x == y) (mod b)")]])

  let word_cand ← new_definition
   r"(word_cand:N word->N word->N word) x y =
        if ~(x = word 0) /\ ~(y = word 0) then word 1 else word 0"

  let word_cor ← new_definition
   r"(word_cor:N word->N word->N word) x y =
        if ~(x = word 0) \/ ~(y = word 0) then word 1 else word 0"

  let WORD_CAND ← prove
   r"!x y:N word.
        word_cand x y = if x = word 0 \/ y = word 0 then word 0 else word 1"
   (REWRITE_TAC [word_cand] THEN MESON_TAC [])

  let WORD_COR ← prove
   r"!x y:N word.
        word_cor x y = if x = word 0 /\ y = word 0 then word 0 else word 1"
   (REWRITE_TAC [word_cor] THEN MESON_TAC [])

  let WORD_CAND_NE_0 ← prove
   r"!x y:N word.
        ~(word_cand x y = word 0) <=> ~(x = word 0) /\ ~(y = word 0)"
   (REWRITE_TAC [word_cand] THEN MESON_TAC [WORD_NE_10])

  let WORD_COR_NE_0 ← prove
   r"!x y:N word.
        ~(word_cor x y = word 0) <=> ~(x = word 0) \/ ~(y = word 0)"
   (REWRITE_TAC [word_cor] THEN MESON_TAC [WORD_NE_10])

  let WORD_CAND_EQ_0 ← prove
   r"!x y:N word.
        word_cand x y = word 0 <=> x = word 0 \/ y = word 0"
   (REWRITE_TAC [word_cand] THEN MESON_TAC [WORD_NE_10])

  let WORD_COR_EQ_0 ← prove
   r"!x y:N word.
        word_cor x y = word 0 <=> x = word 0 /\ y = word 0"
   (REWRITE_TAC [word_cor] THEN MESON_TAC [WORD_NE_10])

  let VAL_WORD_CAND ← prove
   r"!x y:N word.
        val(word_cand x y) =
        if ~(val x = 0) /\ ~(val y = 0) then 1 else 0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_cand, VAL_EQ_0] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [VAL_WORD_0, VAL_WORD_1])

  let VAL_WORD_COR ← prove
   r"!x y:N word.
        val(word_cor x y) =
        if ~(val x = 0) \/ ~(val y = 0) then 1 else 0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_cor, VAL_EQ_0] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [VAL_WORD_0, VAL_WORD_1])

  let BIT_WORD_CAND ← prove
   r"!i x y:N word.
        bit i (word_cand x y) <=> i = 0 /\ ~(x = word 0) /\ ~(y = word 0)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_cand] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [BIT_WORD_0, BIT_WORD_1])

  let BIT_WORD_COR ← prove
   r"!i x y:N word.
        bit i (word_cor x y) <=> i = 0 /\ (~(x = word 0) \/ ~(y = word 0))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_cor] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [BIT_WORD_0, BIT_WORD_1])

  return { word_zx, VAL_WORD_ZX_GEN, VAL_WORD_ZX, WORD_ZX_ZX, WORD_ZX_0, WORD_ZX_TRIVIAL,
           WORD_ZX_WORD, WORD_ZX_WORD_SIMPLE, WORD_ZX_1, WORD_ZX_BITVAL, BIT_WORD_ZX,
           WORD_ZX_AND, WORD_ZX_OR, WORD_ZX_XOR, WORD_ZX_NOT, WORD_ZX_ADD, WORD_ZX_MUL,
           WORD_ZX_NEG, WORD_ZX_SUB, WORD_ZX_SHL, word_sx, IVAL_WORD_SX, WORD_SX_SX,
           WORD_SX_0, WORD_SX_TRIVIAL, WORD_SX_ZX, word_sxfrom, BIT_WORD_SXFROM,
           IVAL_WORD_SXFROM_UNIQUE, word_cand, word_cor, WORD_CAND, WORD_COR,
           WORD_CAND_NE_0, WORD_COR_NE_0, WORD_CAND_EQ_0, WORD_COR_EQ_0, VAL_WORD_CAND,
           VAL_WORD_COR, BIT_WORD_CAND, BIT_WORD_COR }

/- ------------------------------------------------------------------------- -/
/- Joining, in a somewhat (over?) general sense; v is the high part, w low;  -/
/- and subwords, where the (pos,len) argument is (lsb_position,length).      -/
/- ------------------------------------------------------------------------- -/

structure JoinSubword where
  word_join : thm
  VAL_WORD_JOIN : thm
  BIT_WORD_JOIN_GEN : thm
  BIT_WORD_JOIN : thm
  VAL_WORD_JOIN_SIMPLE : thm
  WORD_JOIN_NOT : thm
  word_subword : thm
  VAL_WORD_SUBWORD : thm
  VAL_WORD_SUBWORD_DIMINDEX : thm
  VAL_WORD_SUBWORD_SIMPLE : thm
  WORD_SUBWORD_WORD : thm
  BIT_WORD_SUBWORD : thm
  WORD_SUBWORD_0 : thm
  WORD_SUBWORD_JOIN_SELF : thm
  VAL_WORD_SUBWORD_JOIN : thm
  WORD_SUBWORD_JOIN_LOWER : thm
  WORD_SUBWORD_JOIN_UPPER : thm
  WORD_SUBWORD_SUBWORD : thm
  WORD_SUBWORD_TRIVIAL : thm
  WORD_SUBWORD_DIMINDEX : thm
  WORD_ZX_SUBWORD : thm
  VAL_WORD_SUBWORD_JOIN_FULL : thm
  WORD_SUBWORD_JOIN_AS_USHR : thm
  WORD_SUBWORD_JOIN_AS_SHL : thm
  WORD_SUBWORD_AS_USHR : thm
  WORD_USHR_AS_SUBWORD : thm
  WORD_SHL_SUBWORD : thm
  WORD_SUBWORD_AND : thm
  WORD_SUBWORD_OR : thm
  WORD_SUBWORD_XOR : thm
  WORD_SUBWORD_NOT : thm
  WORD_SUBWORD_ADD : thm
  WORD_SUBWORD_AS_IWORD : thm
  /-- The second binding of `WORD_SUBWORD_IWORD` (words.ml 4249). -/
  WORD_SUBWORD_IWORD : thm
  WORD_SUBWORD_AS_USHR_SHL : thm
  WORD_SXFROM_SUBWORD_AS_ISHR_SHL : thm
  VAL_EXPAND_SUBWORDS : thm
  VAL_SUBWORDS_EQ : thm
  WORD_SUBWORDS_EQ : thm
  deriving Inhabited

@[nospecialize]
def setupJoinSubword [HolBase] (D : WordsDeps) (BDigitsum : Digitsum) (BBinary : Binary) (BWordType : WordType) (BVal : Val) (BIval : Ival) (BWordOps1 : WordOps1) (BWordOps2 : WordOps2) (BWordOps3 : WordOps3) (BZxSx : ZxSx) :
    ExceptT String IO JoinSubword := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC,
        MOD_DOWN_CONV, new_definition, .. } := D
  let { ADD_ASSOC, ADD_CLAUSES, ADD_SUB2, ADD_SYM, ARITH, ARITH_EQ, COND_SWAP,
        CONJ_ASSOC, DE_MORGAN_THM, DIMINDEX_TYBIT0, DIVISION_SIMP, DIV_0, DIV_1,
        DIV_ADD_EQ, DIV_DIV, DIV_EQ_0, DIV_LE, DIV_LT, DIV_MOD, DIV_MULT, DIV_MULT_ADD,
        EXP, EXP_ADD, EXP_EQ_0, EXP_MULT, .. } := D.core1
  let { FINITE_NUMSEG_LT, FORALL_IN_GSPEC, IMP_CONJ_ALT, INT_DIV_REM,
        INT_OF_NUM_CLAUSES, INT_OF_NUM_DIV, INT_POS, INT_POW_ADD, INT_POW_LE,
        IN_ELIM_PAIR_THM, IN_ELIM_THM, .. } := D.core2
  let { LEFT_ADD_DISTRIB, LEFT_IMP_EXISTS_THM, LEFT_SUB_DISTRIB, LET_ADD2, LET_TRANS,
        LE_EXISTS, LE_EXP, LE_MULT_LCANCEL, LE_REFL, LT, LTE_TRANS, LT_ADD_LCANCEL,
        LT_EXISTS, MOD_0, MOD_LT, MOD_LT_EQ, MOD_MOD_EXP_MIN, MOD_MULT2, MOD_MULT_ADD,
        MOD_REFL, MOD_UNIQ, MULT_2, MULT_ASSOC, MULT_CLAUSES, MULT_SYM, NOT_LT,
        NOT_SUC, NSUM_EQ_GENERAL_INVERSES, NSUM_LMUL, NSUM_NSUM_PRODUCT, ODD, ODD_ADD,
        ODD_MULT, PAIR_EQ, .. } := D.core3
  let { RDIV_LT_EQ, .. } := D.core4
  let { DIGITSUM_BOUND, DIGITSUM_UNIQUE, .. } := BDigitsum
  let { ODD_MOD_POW2, .. } := BBinary
  let { BIT_GUARD, BIT_TRIVIAL, WORD_EQ_BITS_ALT, .. } := BWordType
  let { BIT_VAL, BIT_WORD, VAL_BOUND, VAL_EQ, VAL_WORD, VAL_WORD_0, WORD_MOD_SIZE,
        val_def, .. } := BVal
  let { INT_REM_IVAL, INT_REM_IVAL_IWORD, WORD_IWORD, .. } := BIval
  let { BIT_WORD_AND, BIT_WORD_NOT, BIT_WORD_OR, BIT_WORD_XOR, VAL_WORD_ADD, .. } := BWordOps1
  let { BIT_WORD_SHL, VAL_WORD_SHL, word_shl, .. } := BWordOps2
  let { BIT_WORD_ISHR, BIT_WORD_ROR, BIT_WORD_USHR, VAL_WORD_USHR, WORD_USHR_ZERO,
        word_ushr, .. } := BWordOps3
  let { BIT_WORD_SXFROM, word_zx, .. } := BZxSx
  -- @@SCOPE END

  let word_join ← new_definition
   r"(word_join:(M)word->(N)word->(P)word) v w =
        word(2 EXP dimindex(:N) * val v + val w)"

  let VAL_WORD_JOIN ← prove
   r"!v w. val((word_join:(M)word->(N)word->(P)word) v w) =
         (2 EXP dimindex(:N) * val v + val w) MOD 2 EXP dimindex(:P)"
   (REWRITE_TAC [word_join, VAL_WORD])

  let BIT_WORD_JOIN_GEN ← prove
   r"!e h l i.
        l < 2 EXP e
        ==> (ODD ((2 EXP e * h + l) DIV 2 EXP i) <=>
             if i < e then ODD(l DIV 2 EXP i) else ODD(h DIV 2 EXP (i - e)))"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [LT_EXISTS]) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d:num") SUBST1_TAC) THEN
      REWRITE_TAC [EXP_ADD, EXP, ← GSYM MULT_ASSOC] THEN
      SIMP_TAC [DIV_MULT_ADD, EXP_EQ_0, ARITH_EQ] THEN
      REWRITE_TAC [ODD_MULT, ODD_ADD, ARITH],
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [NOT_LT]) THEN
      DISCH_THEN (MP_TAC o GEN_REWRITE_RULE id [LE_EXISTS]) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d:num") SUBST1_TAC) THEN
      SIMP_TAC [DIV_MULT_ADD, EXP_EQ_0, ARITH_EQ, EXP_ADD, ← GSYM DIV_DIV] THEN
      ASM_SIMP_TAC [DIV_LT, ADD_CLAUSES, ADD_SUB2]])

  let BIT_WORD_JOIN ← prove
   r"!v w i.
        bit i ((word_join:(M)word->(N)word->(P)word) v w) <=>
        i < dimindex(:P) /\
        (if i < dimindex(:N) then bit i w else bit (i - dimindex(:N)) v)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "i < dimindex(:P)") THEN
    ASM_SIMP_TAC [BIT_TRIVIAL, ← GSYM NOT_LT] THEN
    REWRITE_TAC [word_join, BIT_WORD] THEN ASM_REWRITE_TAC [BIT_VAL] THEN
    SIMP_TAC [BIT_WORD_JOIN_GEN, VAL_BOUND])

  let VAL_WORD_JOIN_SIMPLE ← prove
   r"!v w.
        dimindex(:M) + dimindex(:N) = dimindex(:P)
        ==> val((word_join:(M)word->(N)word->(P)word) v w) =
            2 EXP dimindex(:N) * val v + val w"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [VAL_WORD_JOIN] THEN
    MATCH_MP_TAC MOD_LT THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    TRANS_TAC LTE_TRANS
     (← q r"2 EXP dimindex(:N) * (2 EXP dimindex(:M) - 1) + 2 EXP dimindex(:N)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LET_ADD2 THEN REWRITE_TAC [VAL_BOUND, LE_MULT_LCANCEL] THEN
      DISJ2_TAC THEN MATCH_MP_TAC (← ARITH_RULE (← q r"a < b ==> a <= b - 1")) THEN
      REWRITE_TAC [VAL_BOUND],
      REWRITE_TAC [LEFT_SUB_DISTRIB, EXP_ADD] THEN MATCH_MP_TAC (← ARITH_RULE
       (← q r"n * 1 <= n * m ==> n * m - n * 1 + n <= m * n")) THEN
      REWRITE_TAC [LE_MULT_LCANCEL, ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")] THEN
      REWRITE_TAC [EXP_EQ_0, ARITH_EQ]])

  let WORD_JOIN_NOT ← prove
   r"!v w. dimindex(:P) <= dimindex(:M) + dimindex(:N)
         ==> (word_join:(M)word->(N)word->(P)word) (word_not v) (word_not w) =
             word_not(word_join v w)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [WORD_EQ_BITS_ALT] THEN
    SIMP_TAC [BIT_WORD_JOIN, BIT_WORD_NOT, COND_SWAP] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [BIT_GUARD] THEN EQ_TAC THEN SIMP_TAC [] THEN
    ASM_ARITH_TAC)

  let word_subword ← new_definition
   r"word_subword (w:M word) (pos,len):N word =
        word((val w DIV (2 EXP pos)) MOD (2 EXP len))"

  let VAL_WORD_SUBWORD ← prove
   r"!pos len w:M word.
        val(word_subword w (pos,len):N word) =
        (val w DIV (2 EXP pos)) MOD (2 EXP (MIN len (dimindex(:N))))"
   (REWRITE_TAC [word_subword, VAL_WORD, MOD_MOD_EXP_MIN])

  let VAL_WORD_SUBWORD_DIMINDEX ← prove
   r"!pos w:M word.
        val(word_subword w (pos,dimindex(:N)):N word) =
        (val w DIV (2 EXP pos)) MOD (2 EXP dimindex(:N))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [VAL_WORD_SUBWORD] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"MIN n n = n")])

  let VAL_WORD_SUBWORD_SIMPLE ← prove
   r"!w:M word.
        val(word_subword w (0,dimindex(:N)):N word) =
        val w MOD (2 EXP dimindex(:N))"
   (REWRITE_TAC [VAL_WORD_SUBWORD_DIMINDEX, EXP, DIV_1])

  let WORD_SUBWORD_WORD ← prove
   r"!n pos len.
        pos + len <= dimindex(:N)
        ==> word_subword (word n:N word) (pos,len) =
            word((n DIV 2 EXP pos) MOD 2 EXP len)"
   (REPEAT STRIP_TAC THEN SIMP_TAC [word_subword, DIV_MOD, ← GSYM EXP_ADD] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [VAL_WORD, MOD_MOD_EXP_MIN] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC)

  let BIT_WORD_SUBWORD ← prove
   r"!pos len (w:M word) i.
        bit i (word_subword w (pos,len):N word) <=>
        i < MIN len (dimindex(:N)) /\ bit (pos + i) w"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [← ARITH_RULE (← q r"m < MIN p q <=> m < p /\ m < q")] THEN
    ASM_CASES_TAC (← q "i < dimindex(:N)") THEN
    ASM_SIMP_TAC [← GSYM NOT_LT, BIT_TRIVIAL] THEN
    ASM_REWRITE_TAC [word_subword, BIT_WORD] THEN
    REWRITE_TAC [DIV_MOD, ← GSYM EXP_ADD, BIT_VAL, DIV_DIV] THEN
    ASM_CASES_TAC (← q "i:num < len") THEN ASM_REWRITE_TAC [] THENL
     [UNDISCH_TAC (← q "i:num < len") THEN
      SIMP_TAC [LT_EXISTS, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q "d:num") THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [ADD_ASSOC] THEN
      SPEC_TAC (← q "pos + i:num", ← q "j:num") THEN REWRITE_TAC [EXP_ADD] THEN
      REWRITE_TAC [← GSYM DIV_MOD, ODD_MOD_POW2, NOT_SUC],
      MATCH_MP_TAC (← MESON [ODD] (← q r"n = 0 ==> ~ODD n")) THEN
      SIMP_TAC [DIV_EQ_0, EXP_EQ_0, ARITH_EQ] THEN
      TRANS_TAC LTE_TRANS (← q "2 EXP (pos + len)") THEN
      SIMP_TAC [MOD_LT_EQ, EXP_EQ_0, ARITH_EQ, LE_EXP] THEN
      ASM_ARITH_TAC])

  let WORD_SUBWORD_0 ← prove
   r"!pos len. word_subword (word 0) (pos,len) = word 0"
   (REWRITE_TAC [word_subword, VAL_WORD_0, DIV_0, MOD_0])

  let WORD_SUBWORD_JOIN_SELF ← prove
   r"!(w:N word) k.
        k <= dimindex(:N)
        ==> word_subword (word_join w w:(N tybit0)word) (k,dimindex(:N)) =
            word_ror w k"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_SUBWORD, BIT_WORD_JOIN, BIT_WORD_ROR,
                 DIMINDEX_TYBIT0, ← ARITH_RULE (← q r"MIN n n = n")] THEN
    X_GEN_TAC (← q "i:num") THEN DISCH_TAC THEN
    FIRST_ASSUM (DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC o MATCH_MP (← ARITH_RULE
     (← q r"k:num <= n ==> k = n \/ k < n"))) THEN
    ASM_SIMP_TAC [MOD_REFL, MOD_LT, ADD_CLAUSES,
                  ← ARITH_RULE (← q r"(n + i) - n:num = i"),
                  ← ARITH_RULE (← q r"~(n + i:num < n)"),
                  ← ARITH_RULE (← q r"i < n ==> n + i < 2 * n")] THEN
    REWRITE_TAC [ADD_SYM, ← TAUT (← q r"(p /\ q <=> q) <=> q ==> p")] THEN
    DISCH_THEN (fun _ => ALL_TAC) THEN ASM_ARITH_TAC)

  let VAL_WORD_SUBWORD_JOIN ← prove
   r"!(h:N word) (l:N word) n m.
        m <= dimindex(:N)
        ==> val(word_subword (word_join h l:(N tybit0)word) (n,m) :N word) =
            ((2 EXP dimindex(:N) * val h + val l) DIV 2 EXP n) MOD 2 EXP m"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [VAL_WORD_JOIN, VAL_WORD_SUBWORD] THEN
    REWRITE_TAC [DIV_MOD, ← GSYM EXP_ADD, MOD_MOD_EXP_MIN, DIMINDEX_TYBIT0] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC (← MESON [MOD_LT]
     (← q r"!e. x < e /\ x MOD e MOD m = x MOD e MOD n ==> x MOD m = x MOD n")) THEN
    EXISTS_TAC (← q "2 EXP (2 * dimindex(:N))") THEN CONJ_TAC THENL
     [REWRITE_TAC [MULT_2, EXP_ADD] THEN MATCH_MP_TAC (← ARITH_RULE
       (← q r"e * h + e * 1 <= e * e /\ l < e ==> e * h + l < e * e")) THEN
      REWRITE_TAC [← GSYM LEFT_ADD_DISTRIB, LE_MULT_LCANCEL, VAL_BOUND,
                   EXP_EQ_0, ARITH_EQ, ← ARITH_RULE (← q r"h + 1 <= e <=> h < e")],
      REWRITE_TAC [MOD_MOD_EXP_MIN] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC])

  let WORD_SUBWORD_JOIN_LOWER ← prove
   r"!(h:M word) (l:N word) pos len.
        pos + len <= dimindex(:N) /\ dimindex(:N) <= dimindex(:P)
        ==> word_subword (word_join (h:M word) (l:N word):P word)
                         (pos,len):Q word =
            word_subword l (pos,len)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_SUBWORD, BIT_WORD_JOIN] THEN
    REPEAT STRIP_TAC THEN REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    TRY ASM_ARITH_TAC THEN REWRITE_TAC [CONJ_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC)

  let WORD_SUBWORD_JOIN_UPPER ← prove
   r"!(h:M word) (l:N word) pos len.
        dimindex(:N) <= pos /\ pos + len <= dimindex(:P)
        ==> word_subword (word_join (h:M word) (l:N word):P word)
                         (pos,len):Q word =
            word_subword h (pos - dimindex(:N),len)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_SUBWORD, BIT_WORD_JOIN] THEN
    REPEAT STRIP_TAC THEN REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    TRY ASM_ARITH_TAC THEN REWRITE_TAC [CONJ_ASSOC] THEN
    BINOP_TAC THEN TRY (AP_THM_TAC THEN AP_TERM_TAC) THEN ASM_ARITH_TAC)

  let WORD_SUBWORD_SUBWORD ← prove
   r"!(x:M word) pos1 len1 pos2 len2.
        len1 <= dimindex(:N) /\ dimindex(:N) <= dimindex(:M)
        ==> word_subword (word_subword x (pos1,len1):N word)
                         (pos2,len2):P word =
            word_subword x (pos1+pos2,MIN len2 (len1-pos2))"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_SUBWORD] THEN
    REWRITE_TAC [← GSYM ADD_ASSOC] THEN
    REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [BIT_GUARD]) THEN
    ASM_ARITH_TAC)

  let WORD_SUBWORD_TRIVIAL ← prove
   r"!(x:N word) n. dimindex(:N) <= n ==> word_subword x (0,n) = x"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_SUBWORD, ADD_CLAUSES] THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"N:num <= n ==> MIN n N = N")])

  let WORD_SUBWORD_DIMINDEX ← prove
   r"!(x:N word) k.
        word_subword x (k,dimindex(:M)):M word = word_zx(word_ushr x k)"
   (REWRITE_TAC [word_subword, word_zx, VAL_WORD_USHR, WORD_MOD_SIZE])

  let WORD_ZX_SUBWORD ← prove
   r"!(x:N word). word_zx x:M word = word_subword x (0,dimindex(:M))"
   (REWRITE_TAC [WORD_SUBWORD_DIMINDEX, WORD_USHR_ZERO])

  let VAL_WORD_SUBWORD_JOIN_FULL ← prove
   r"!(h:N word) (l:N word) k.
       k <= dimindex(:N)
       ==> val(word_subword (word_join h l:(N tybit0)word)
                            (k,dimindex(:N)) :N word) =
           2 EXP (dimindex(:N) - k) * val h MOD 2 EXP k + val l DIV (2 EXP k)"
   (REPEAT STRIP_TAC THEN SIMP_TAC [VAL_WORD_SUBWORD_JOIN, LE_REFL] THEN
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC (← q "val(h:N word) DIV 2 EXP k") THEN
    SUBGOAL_THEN (← q r"2 EXP dimindex(:N) = 2 EXP k * 2 EXP (dimindex(:N) - k)")
    SUBST1_TAC THENL
     [REWRITE_TAC [← GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC,
      SIMP_TAC [← GSYM MULT_ASSOC, DIV_MULT_ADD, EXP_EQ_0, ARITH_EQ]] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [DIVISION_SIMP, ← ARITH_RULE
       (← q r"d * k * e + e * m + l:num = e * (d * k + m) + l")],
      MATCH_MP_TAC (← ARITH_RULE
       (← q r"d < e /\ e * (m + 1) <= e * k ==> e * m + d < k * e")) THEN
      REWRITE_TAC [LE_MULT_LCANCEL, ← ARITH_RULE (← q r"a + 1 <= b <=> a < b")] THEN
      SIMP_TAC [MOD_LT_EQ, EXP_EQ_0, ARITH_EQ, RDIV_LT_EQ] THEN
      ASM_SIMP_TAC [← GSYM EXP_ADD, ← ARITH_RULE (← q r"k:num <= d ==> k + d - k = d")] THEN
      REWRITE_TAC [VAL_BOUND]])

  let WORD_SUBWORD_JOIN_AS_USHR ← prove
   r"!(x:N word) k.
      word_subword (word_join (word 0:N word) x:((N)tybit0)word)
                   (k,dimindex(:N)) =
      word_ushr x k"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM VAL_EQ] THEN
    SIMP_TAC [VAL_WORD_USHR, VAL_WORD_SUBWORD_JOIN, LE_REFL] THEN
    REWRITE_TAC [VAL_WORD_0, MULT_CLAUSES, ADD_CLAUSES] THEN
    MATCH_MP_TAC MOD_LT THEN MESON_TAC [DIV_LE, VAL_BOUND, LET_TRANS])

  let WORD_SUBWORD_JOIN_AS_SHL ← prove
   r"!(x:N word) k.
        k <= dimindex(:N)
        ==> word_subword (word_join x (word 0:N word):((N)tybit0)word)
                         (k,dimindex(:N)) =
            word_shl x (dimindex(:N) - k)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM VAL_EQ] THEN
    SIMP_TAC [VAL_WORD_SHL, VAL_WORD_SUBWORD_JOIN, LE_REFL] THEN
    REWRITE_TAC [VAL_WORD_0, ADD_CLAUSES] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN (← q r"2 EXP dimindex(:N) = 2 EXP k * 2 EXP (dimindex(:N) - k)")
    SUBST1_TAC THENL
     [REWRITE_TAC [← GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC,
      SIMP_TAC [← GSYM MULT_ASSOC, DIV_MULT, EXP_EQ_0, ARITH_EQ]])

  let WORD_SUBWORD_AS_USHR ← prove
   r"!(x:N word) k l.
        dimindex(:N) <= k + l ==> word_subword x (k,l) = word_ushr x k"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [word_subword, word_ushr] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN
    SIMP_TAC [RDIV_LT_EQ, EXP_EQ_0, ARITH_EQ, ← GSYM EXP_ADD] THEN
    W (MP_TAC o PART_MATCH lhand VAL_BOUND o lhand o snd) THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] LTE_TRANS) THEN
    ASM_REWRITE_TAC [LE_EXP] THEN ARITH_TAC)

  let WORD_USHR_AS_SUBWORD ← prove
   r"!(x:N word) k. word_ushr x k = word_subword x (k,dimindex (:N) - k)"
   (REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC WORD_SUBWORD_AS_USHR THEN ARITH_TAC)

  let WORD_SHL_SUBWORD ← prove
   r"!(x:N word) d l.
        dimindex(:N) <= l + d
        ==> word_shl (word_subword x (0,l)) d = word_shl x d"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [word_shl, word_subword] THEN
    REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD, EXP, DIV_1] THEN
    CONV_TAC MOD_DOWN_CONV THEN ONCE_REWRITE_TAC [MULT_SYM] THEN
    REWRITE_TAC [← GSYM MOD_MULT2, ← GSYM EXP_ADD, MOD_MOD_EXP_MIN] THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"n <= l + d ==> MIN (d + l) n = n")])

  let WORD_SUBWORD_AND ← prove
   r"!(x:M word) y pos len.
        word_subword (word_and x y) (pos,len) :N word =
        word_and (word_subword x (pos,len)) (word_subword y (pos,len))"
   (REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_SUBWORD, BIT_WORD_AND] THEN
    ONCE_REWRITE_TAC [BIT_GUARD] THEN CONV_TAC (fun t => (TAUT t).run))

  let WORD_SUBWORD_OR ← prove
   r"!(x:M word) y pos len.
        word_subword (word_or x y) (pos,len) :N word =
        word_or (word_subword x (pos,len)) (word_subword y (pos,len))"
   (REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_SUBWORD, BIT_WORD_OR] THEN
    ONCE_REWRITE_TAC [BIT_GUARD] THEN CONV_TAC (fun t => (TAUT t).run))

  let WORD_SUBWORD_XOR ← prove
   r"!(x:M word) y pos len.
        word_subword (word_xor x y) (pos,len) :N word =
        word_xor (word_subword x (pos,len))
                 (word_subword y (pos,len))"
   (REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_SUBWORD, BIT_WORD_XOR] THEN
    ONCE_REWRITE_TAC [BIT_GUARD] THEN CONV_TAC (fun t => (TAUT t).run))

  let WORD_SUBWORD_NOT ← prove
   r"!(x:M word) pos len.
        dimindex(:N) <= len /\ pos + len <= dimindex(:M)
        ==> word_subword (word_not x) (pos,len):N word =
            word_not (word_subword x (pos,len))"
   (REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_SUBWORD, BIT_WORD_NOT] THEN
    SIMP_TAC [← ARITH_RULE (← q r"i < MIN m n <=> i < m /\ i < n")] THEN
    REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC [DE_MORGAN_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC)

  let WORD_SUBWORD_ADD ← prove
   r"!x y:N word.
        dimindex(:M) = len /\ pos + len <= dimindex(:N) /\
        val x MOD 2 EXP pos + val y MOD 2 EXP pos < 2 EXP pos
        ==> word_subword (word_add x y) (pos,len):M word =
            word_add (word_subword x (pos,len))
                     (word_subword y (pos,len))"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_ADD, VAL_WORD_SUBWORD] THEN
    FIRST_ASSUM SUBST1_TAC THEN REWRITE_TAC [← ARITH_RULE (← q r"MIN n n = n")] THEN
    CONV_TAC MOD_DOWN_CONV THEN ASM_SIMP_TAC [← GSYM DIV_ADD_EQ] THEN
    REWRITE_TAC [DIV_MOD, ← GSYM EXP_ADD, MOD_MOD_EXP_MIN] THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"m <= n ==> MIN n m = m")])

  let WORD_SUBWORD_AS_IWORD ← prove
   r"!(w:N word) pos len.
        pos + len <= dimindex(:N)
        ==> word_subword w (pos,len):M word =
            iword((ival w div &2 pow pos) rem &2 pow len)"
   (REPEAT STRIP_TAC THEN SIMP_TAC [INT_DIV_REM, INT_POW_LE, INT_POS] THEN
    ASM_SIMP_TAC [← GSYM INT_POW_ADD, INT_REM_IVAL] THEN
    REWRITE_TAC [word_subword, INT_OF_NUM_DIV, INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC [WORD_IWORD, EXP_ADD, ← GSYM DIV_MOD])

  -- words.ml binds WORD_SUBWORD_IWORD twice (4240, 4249); the second wins.
  let _ ← prove
   r"!x pos len.
        pos + len <= dimindex(:N)
        ==> word_subword (iword x:N word) (pos,len):M word =
            iword((x div &2 pow pos) rem &2 pow len)"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [WORD_SUBWORD_AS_IWORD] THEN
    SIMP_TAC [INT_DIV_REM, INT_POW_LE, INT_POS, ← GSYM INT_POW_ADD] THEN
    ASM_SIMP_TAC [INT_REM_IVAL_IWORD])

  let WORD_SUBWORD_IWORD ← prove
   r"!x pos len.
        pos + len <= dimindex(:N)
        ==> word_subword (iword x:N word) (pos,len):N word =
            iword((x div &2 pow pos) rem &2 pow len)"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [WORD_SUBWORD_AS_IWORD] THEN
    SIMP_TAC [INT_DIV_REM, INT_POW_LE, INT_POS, ← GSYM INT_POW_ADD] THEN
    ASM_SIMP_TAC [INT_REM_IVAL_IWORD])

  let WORD_SUBWORD_AS_USHR_SHL ← prove
   r"!(x:N word) pos len.
        pos + len <= dimindex(:N)
        ==> word_subword x (pos,len):N word =
            word_ushr (word_shl x (dimindex(:N) - (pos + len)))
                      (dimindex(:N) - len)"
   (REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_SUBWORD,
                 BIT_WORD_USHR, BIT_WORD_SHL] THEN
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [BIT_GUARD] THEN
    REWRITE_TAC [CONJ_ASSOC] THEN MATCH_MP_TAC (← TAUT
     (← q r"(p <=> p') /\ (p /\ p' ==> (q <=> q')) ==> (p /\ q <=> p' /\ q')")) THEN
    CONJ_TAC THENL [ALL_TAC, STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC] THEN
    ASM_ARITH_TAC)

  let WORD_SXFROM_SUBWORD_AS_ISHR_SHL ← prove
   r"!(x:N word) pos len.
        pos + len <= dimindex(:N) /\ 0 < len
        ==> word_sxfrom (len-1) (word_subword x (pos,len)):N word =
            word_ishr (word_shl x (dimindex(:N) - (pos + len)))
                      (dimindex(:N) - len)"
   (REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_SUBWORD, BIT_WORD_SXFROM,
                 BIT_WORD_ISHR, BIT_WORD_SHL] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ONCE_REWRITE_TAC [BIT_GUARD] THEN
    REWRITE_TAC [CONJ_ASSOC] THEN MATCH_MP_TAC (← TAUT
     (← q r"(p <=> p') /\ (p /\ p' ==> (q <=> q')) ==> (p /\ q <=> p' /\ q')")) THEN
    (CONJ_TAC THENL [ALL_TAC, STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC]) THEN
    ASM_ARITH_TAC)

  let VAL_EXPAND_SUBWORDS ← prove
   r"!k m (x:N word).
        dimindex(:M) = k /\ dimindex(:N) = k * m
        ==> nsum {i | i < m}
                 (\i.  2 EXP (k * i) *
                       val(word_subword x (k * i,k):M word)) =
            val x"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [val_def, ← GSYM NSUM_LMUL, BIT_WORD_SUBWORD] THEN
    POP_ASSUM_LIST (CONV_TAC o SUBS_CONV) THEN
    REWRITE_TAC [MULT_ASSOC, ← GSYM EXP_ADD, ← ARITH_RULE (← q r"MIN n n = n")] THEN
    SIMP_TAC [NSUM_NSUM_PRODUCT, FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC NSUM_EQ_GENERAL_INVERSES THEN
    MAP_EVERY EXISTS_TAC [← q r"\(i,j). (k:num) * i + j", ← q r"\n. n DIV k,n MOD k"] THEN
    REWRITE_TAC [FORALL_IN_GSPEC] THEN
    REWRITE_TAC [IN_ELIM_PAIR_THM, PAIR_EQ] THEN SIMP_TAC [IN_ELIM_THM] THEN
    ASM_CASES_TAC (← q "k = 0") THEN ASM_REWRITE_TAC [LT, MULT_CLAUSES] THEN
    ASM_SIMP_TAC [DIV_MULT_ADD, DIVISION_SIMP, MOD_MULT_ADD, DIV_LT, MOD_LT] THEN
    ASM_SIMP_TAC [MOD_LT_EQ, RDIV_LT_EQ, ADD_CLAUSES] THEN
    REPEAT STRIP_TAC THEN TRANS_TAC LTE_TRANS (← q "k * i + k:num") THEN
    ASM_REWRITE_TAC [LT_ADD_LCANCEL] THEN
    ASM_REWRITE_TAC [← ARITH_RULE (← q r"k * i + k = k * (i + 1)")] THEN
    REWRITE_TAC [LE_MULT_LCANCEL] THEN ASM_ARITH_TAC)

  let VAL_SUBWORDS_EQ ← prove
   r"!k m f (x:N word).
        dimindex(:M) = k /\ dimindex(:N) = k * m
        ==> ((!i. i < m ==> val(word_subword x (k * i,k):M word) = f i) <=>
             (!i. i < m ==> f i < 2 EXP k) /\
             val x = nsum {i | i < m} (\i.  2 EXP (k * i) * f i))"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"!i. i < m ==> val(word_subword (x:N word) (k * i,k):M word) < 2 EXP k")
    ASSUME_TAC THENL
     [REPEAT (FIRST_X_ASSUM (SUBST1_TAC o SYM)) THEN REWRITE_TAC [VAL_BOUND],
      ALL_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"(p ==> q) /\ (q ==> (p <=> r)) ==> (p <=> q /\ r)")) THEN
    CONJ_TAC THENL [ASM_MESON_TAC [], DISCH_TAC] THEN
    MP_TAC (← SPECL [← q "k:num", ← q "m:num", ← q "x:N word"] VAL_EXPAND_SUBWORDS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN
    ASM_SIMP_TAC [DIGITSUM_UNIQUE, EXP_MULT, IN_ELIM_THM, FINITE_NUMSEG_LT] THEN
    MESON_TAC [])

  let WORD_SUBWORDS_EQ ← prove
   r"!k m f (x:N word).
        dimindex(:M) = k /\ dimindex(:N) = k * m
        ==> ((!i. i < m ==> val(word_subword x (k * i,k):M word) = f i) <=>
             (!i. i < m ==> f i < 2 EXP k) /\
             word(nsum {i | i < m} (\i.  2 EXP (k * i) * f i)) = x)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP VAL_SUBWORDS_EQ th])) THEN
    MATCH_MP_TAC (← TAUT (← q r"(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)")) THEN
    DISCH_TAC THEN REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD] THEN
    CONV_TAC (RAND_CONV SYM_CONV) THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    FIRST_X_ASSUM (SUBST1_TAC o CONJUNCT2) THEN
    ASM_SIMP_TAC [EXP_MULT, DIGITSUM_BOUND, IN_ELIM_THM, FINITE_NUMSEG_LT])

  return { word_join, VAL_WORD_JOIN, BIT_WORD_JOIN_GEN, BIT_WORD_JOIN, VAL_WORD_JOIN_SIMPLE,
           WORD_JOIN_NOT, word_subword, VAL_WORD_SUBWORD, VAL_WORD_SUBWORD_DIMINDEX,
           VAL_WORD_SUBWORD_SIMPLE, WORD_SUBWORD_WORD, BIT_WORD_SUBWORD, WORD_SUBWORD_0,
           WORD_SUBWORD_JOIN_SELF, VAL_WORD_SUBWORD_JOIN, WORD_SUBWORD_JOIN_LOWER,
           WORD_SUBWORD_JOIN_UPPER, WORD_SUBWORD_SUBWORD, WORD_SUBWORD_TRIVIAL,
           WORD_SUBWORD_DIMINDEX, WORD_ZX_SUBWORD, VAL_WORD_SUBWORD_JOIN_FULL,
           WORD_SUBWORD_JOIN_AS_USHR, WORD_SUBWORD_JOIN_AS_SHL, WORD_SUBWORD_AS_USHR,
           WORD_USHR_AS_SUBWORD, WORD_SHL_SUBWORD, WORD_SUBWORD_AND, WORD_SUBWORD_OR,
           WORD_SUBWORD_XOR, WORD_SUBWORD_NOT, WORD_SUBWORD_ADD, WORD_SUBWORD_AS_IWORD,
           WORD_SUBWORD_IWORD, WORD_SUBWORD_AS_USHR_SHL, WORD_SXFROM_SUBWORD_AS_ISHR_SHL,
           VAL_EXPAND_SUBWORDS, VAL_SUBWORDS_EQ, WORD_SUBWORDS_EQ }

/- ------------------------------------------------------------------------- -/
/- Extract bottom len bits of x' and insert into x at position pos;          -/
/- repetition of a shorter word in a longer one; reduce some "simple"        -/
/- subword expressions.                                                      -/
/- ------------------------------------------------------------------------- -/

/-- OCaml's `tryfind`, on rules that can fail. -/
def tryfindE {α β : Type} (f : α → ExceptT String IO β) : List α → ExceptT String IO β
  | [] => throw "tryfind"
  | x :: xs => tryWith (f x) (tryfindE f xs)

structure InsertDup where
  word_insert : thm
  BIT_WORD_INSERT : thm
  WORD_SUBWORD_INSERT_OUTER : thm
  WORD_SUBWORD_INSERT_INNER : thm
  word_duplicate : thm
  BIT_WORD_DUPLICATE : thm
  WORD_DUPLICATE_REFL : thm
  WORD_DUPLICATE_DOUBLE : thm
  WORD_SUBWORD_DUPLICATE : thm
  WORD_SUBWORD_DUPLICATE_DUPLICATE : thm
  VAL_WORD_DUPLICATE : thm
  WORD_DUPLICATE : thm
  WORD_SUBWORD_ZX : thm
  WORD_SUBWORD_ZX_TRIVIAL : thm
  /-- `WORD_SIMPLE_SUBWORD_CONV` (words.ml 4541-4582). -/
  WORD_SIMPLE_SUBWORD_CONV : ioconv
  deriving Inhabited

@[nospecialize]
def setupInsertDup [HolBase] (D : WordsDeps) (BBinary : Binary) (BWordType : WordType) (BBitsOfWord : BitsOfWord) (BVal : Val) (BZxSx : ZxSx) (BJoinSubword : JoinSubword) :
    ExceptT String IO InsertDup := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, INT_ARITH, MESON, MESON_TAC,
        NUM_RED_CONV, new_definition, .. } := D
  let { ADD_CLAUSES, ARITH_EQ, CONG, CONG_DIV2, CONJ_ASSOC, DIMINDEX_NONZERO,
        DIMINDEX_TYBIT0, DIVISION_SIMP, DIV_DIV, DIV_LT, DIV_MULT_ADD, DIV_UNIQ,
        EQ_IMP, EQ_TRANS, EXP, EXP_ADD, EXP_EQ_0, .. } := D.core1
  let { FINITE_NUMSEG_LT, FORALL_IN_GSPEC, FORALL_IN_IMAGE, IMP_CONJ, INT_OF_NUM_ADD,
        INT_OF_NUM_EQ, INT_OF_NUM_MUL, INT_OF_NUM_POW, INT_OF_NUM_SUB, INT_POW_ADD,
        IN_ELIM_THM, .. } := D.core2
  let { LE_1, LE_EXP, LE_MULT_RCANCEL, LTE_TRANS, MOD_ADD_MOD, MOD_CASES, MOD_LT,
        MOD_LT_EQ, MOD_MOD, MOD_MOD_EXP_MIN, MOD_MOD_REFL, MOD_MULT_ADD, MOD_UNIQ,
        MULT_AC, MULT_ASSOC, MULT_CLAUSES, MULT_EQ_0, MULT_SYM, NOT_LT,
        NSUM_CLAUSES_NUMSEG_LT, NSUM_EQ, NSUM_EQ_GENERAL_INVERSES, NSUM_GROUP,
        NSUM_LMUL, NSUM_RMUL, ODD_MOD, .. } := D.core3
  let { RDIV_LT_EQ, RIGHT_ADD_DISTRIB, SUBSET, SUB_REFL, num_INDUCTION, .. } := D.core4
  let { BINARY_DIGITSUM_MOD, .. } := BBinary
  let { BIT_GUARD, WORD_EQ_BITS_ALT, .. } := BWordType
  let { BIT_WORD_OF_BITS, .. } := BBitsOfWord
  let { BIT_VAL, BIT_WORD, BIT_WORD_0, VAL_MOD_REFL, VAL_WORD, VAL_WORD_GALOIS,
        WORD_MOD_SIZE, val_def, .. } := BVal
  let { BIT_WORD_ZX, .. } := BZxSx
  let { BIT_WORD_JOIN, BIT_WORD_JOIN_GEN, BIT_WORD_SUBWORD, WORD_SUBWORD_JOIN_LOWER,
        WORD_SUBWORD_JOIN_UPPER, WORD_SUBWORD_SUBWORD, WORD_SUBWORD_TRIVIAL, .. } := BJoinSubword
  -- @@SCOPE END

  let word_insert ← new_definition
   r"(word_insert:N word->num#num->M word->P word) x (pos,len) x' =
        word(2 EXP (pos + len) * val x DIV 2 EXP (pos + len) +
             2 EXP pos * val x' MOD 2 EXP len +
             val x MOD 2 EXP pos)"

  let BIT_WORD_INSERT ← prove
   r"!(x:N word) (x':M word) pos len i.
        bit i (word_insert x (pos,len) x':P word) <=>
        i < dimindex(:P) /\
        (if pos <= i /\ i < pos + len then bit (i - pos) x' else bit i x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_insert, BIT_WORD] THEN
    ASM_CASES_TAC (← q "i < dimindex(:P)") THEN ASM_REWRITE_TAC [BIT_VAL] THEN
    REWRITE_TAC [EXP_ADD, ← ARITH_RULE
     (← q r"(p * q) * h + p * m + l:num = p * (q * h + m) + l")] THEN
    SIMP_TAC [BIT_WORD_JOIN_GEN, MOD_LT_EQ, EXP_EQ_0, ARITH_EQ] THEN
    ASM_CASES_TAC (← q "i:num < pos") THEN ASM_REWRITE_TAC [← GSYM NOT_LT] THEN
    ASM_SIMP_TAC [← ARITH_RULE
     (← q r"~(i:num < pos) ==> (i - pos < len <=> i < pos + len)")] THEN
    TRY (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    ASM_SIMP_TAC [DIV_DIV, ← GSYM EXP_ADD, ← ARITH_RULE
     (← q r"~(i:num < pos + len) ==> (pos + len) + i - pos - len = i")] THEN
    REWRITE_TAC [ODD_MOD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [← GSYM CONG] THEN MATCH_MP_TAC CONG_DIV2 THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [MULT_SYM] (← GSYM (← CONJUNCT2 EXP))] THEN
    REWRITE_TAC [CONG, MOD_MOD_EXP_MIN] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC)

  let WORD_SUBWORD_INSERT_OUTER ← prove
   r"!(x:M word) (y:N word) pos1 len1 pos2 len2.
        pos2 + len2 <= dimindex(:P) /\
        (pos2 + len2 <= pos1 \/ pos1 + len1 <= pos2)
        ==> word_subword (word_insert x (pos1,len1) y:P word)
                         (pos2,len2):Q word =
            word_subword x (pos2,len2)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_SUBWORD, BIT_WORD_INSERT] THEN
    REPEAT STRIP_TAC THEN REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    TRY ASM_ARITH_TAC THEN REWRITE_TAC [CONJ_ASSOC] THEN
    REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [BIT_GUARD]) THEN
    ASM_ARITH_TAC)

  let WORD_SUBWORD_INSERT_INNER ← prove
   r"!(x:M word) (y:N word) pos1 len1 pos2 len2.
        pos2 + len2 <= dimindex(:P) /\
        pos1 <= pos2 /\ pos2 + len2 <= pos1 + len1
        ==> word_subword (word_insert x (pos1,len1) y:P word)
                         (pos2,len2):Q word =
            word_subword y (pos2-pos1,len2)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_SUBWORD, BIT_WORD_INSERT] THEN
    REPEAT STRIP_TAC THEN REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    TRY ASM_ARITH_TAC THEN REWRITE_TAC [CONJ_ASSOC] THEN
    REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [BIT_GUARD]) THEN
    TRY ASM_ARITH_TAC THEN REWRITE_TAC [IMP_CONJ] THEN DISCH_TAC THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC)

  let word_duplicate ← new_definition
   r"(word_duplicate:M word->N word) x =
  word_of_bits {i | bit (i MOD dimindex(:M)) x}"

  let BIT_WORD_DUPLICATE ← prove
   r"!(x:M word) i.
        bit i (word_duplicate x:N word) <=>
        i < dimindex(:N) /\ bit (i MOD dimindex(:M)) x"
   (REWRITE_TAC [word_duplicate, BIT_WORD_OF_BITS, IN_ELIM_THM])

  let WORD_DUPLICATE_REFL ← prove
   r"!x:N word. word_duplicate x = x"
   (SIMP_TAC [WORD_EQ_BITS_ALT, BIT_WORD_DUPLICATE, MOD_LT])

  let WORD_DUPLICATE_DOUBLE ← prove
   r"!x:M word. (word_duplicate:((M)tybit0)word->N word) (word_join x x) =
              word_duplicate x"
   (GEN_TAC THEN REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_DUPLICATE] THEN
    X_GEN_TAC (← q "i:num") THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [BIT_WORD_JOIN, DIMINDEX_TYBIT0] THEN
    MP_TAC (← SPECL [← q "i MOD (2 * dimindex(:M))", ← q "dimindex(:M)"] MOD_CASES) THEN
    REWRITE_TAC [MOD_LT_EQ, MULT_EQ_0, DIMINDEX_NONZERO, ARITH_EQ] THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [MULT_SYM] MOD_MOD] THEN MESON_TAC [])

  let WORD_SUBWORD_DUPLICATE ← prove
   r"!x pos len.
        pos MOD dimindex(:M) + len <= dimindex(:M) /\
        pos + len <= dimindex(:N)
        ==> word_subword ((word_duplicate:M word->N word) x) (pos,len):P word =
            word_subword x (pos MOD dimindex(:M),len)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_SUBWORD, BIT_WORD_DUPLICATE] THEN
    X_GEN_TAC (← q "i:num") THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [← ARITH_RULE (← q r"i < MIN m n <=> i < m /\ i < n")] THEN
    ASM_CASES_TAC (← q "i:num < len") THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← TAUT (← q r"p /\ (q <=> r) ==> (p /\ q <=> r)")) THEN
    CONJ_TAC THENL [ASM_ARITH_TAC, AP_THM_TAC THEN AP_TERM_TAC] THEN
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC (← q "pos DIV dimindex(:M)") THEN
    ASM_ARITH_TAC)

  let WORD_SUBWORD_DUPLICATE_DUPLICATE ← prove
   r"!x pos len.
        pos MOD dimindex(:M) = 0 /\ dimindex(:P) <= len /\
        pos + len <= dimindex(:N)
        ==> word_subword ((word_duplicate:M word->N word) x) (pos,len):P word =
            word_duplicate x"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_SUBWORD, BIT_WORD_DUPLICATE] THEN
    X_GEN_TAC (← q "i:num") THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [← ARITH_RULE (← q r"i < MIN m n <=> i < m /\ i < n")] THEN
    REWRITE_TAC [CONJ_ASSOC] THEN
    MATCH_MP_TAC (← TAUT (← q r"p /\ (q <=> r) ==> (p /\ q <=> r)")) THEN
    CONJ_TAC THENL [ASM_ARITH_TAC, AP_THM_TAC THEN AP_TERM_TAC] THEN
    ONCE_REWRITE_TAC [← GSYM MOD_ADD_MOD] THEN
    ASM_REWRITE_TAC [ADD_CLAUSES, MOD_MOD_REFL])

  let VAL_WORD_DUPLICATE ← prove
   r"!x k. dimindex(:N) <= k * dimindex(:M)
         ==> val((word_duplicate:M word->N word) x) =
             ((2 EXP (k * dimindex(:M)) - 1) DIV (2 EXP dimindex(:M) - 1) *
              val x) MOD 2 EXP dimindex(:N)"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM VAL_MOD_REFL] THEN
    MP_TAC (← ISPECL
     [← q r"\i. i DIV dimindex(:M)",
      ← q r"\i. 2 EXP i * bitval (bit (i MOD dimindex(:M)) (x:M word))",
      ← q r"{i | i < k * dimindex(:M)}", ← q r"{i:num | i < k}"]
     NSUM_GROUP) THEN
    REWRITE_TAC [FINITE_NUMSEG_LT, SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
    ANTS_TAC THENL
     [SIMP_TAC [RDIV_LT_EQ, DIMINDEX_NONZERO, MULT_AC], ALL_TAC] THEN
    MATCH_MP_TAC (← MESON [MOD_MOD_REFL]
     (← q r"y MOD n = y' /\ x = x' ==> x = y ==> y' MOD n = x' MOD n")) THEN
    CONJ_TAC THENL
     [SIMP_TAC [val_def, BINARY_DIGITSUM_MOD, FINITE_NUMSEG_LT] THEN
      SIMP_TAC [BIT_WORD_DUPLICATE, IN_ELIM_THM] THEN
      ASM_SIMP_TAC [← ARITH_RULE (← q r"a:num <= b ==> (i < b /\ i < a <=> i < a)")],
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     (← q r"nsum {i | i < k} (\i. 2 EXP (dimindex(:M) * i) * val(x:M word))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC [FORALL_IN_GSPEC] THEN
      X_GEN_TAC (← q "i:num") THEN DISCH_TAC THEN
      REWRITE_TAC [val_def, ← GSYM NSUM_LMUL] THEN
      MATCH_MP_TAC NSUM_EQ_GENERAL_INVERSES THEN
      EXISTS_TAC (← q r"\j. j MOD dimindex(:M)") THEN
      EXISTS_TAC (← q r"\j:num. dimindex(:M) * i + j") THEN
      REWRITE_TAC [IN_ELIM_THM] THEN
      SIMP_TAC [MOD_MULT_ADD, DIV_MULT_ADD, DIMINDEX_NONZERO, MOD_LT, DIV_LT,
                MOD_LT_EQ, ADD_CLAUSES] THEN
      CONJ_TAC THEN X_GEN_TAC (← q "j:num") THEN STRIP_TAC THENL
       [TRANS_TAC LTE_TRANS (← q "(i + 1) * dimindex(:M)") THEN
        ASM_REWRITE_TAC [LE_MULT_RCANCEL, DIMINDEX_NONZERO] THEN ASM_ARITH_TAC,
        REWRITE_TAC [MULT_ASSOC, ← GSYM EXP_ADD] THEN ASM_MESON_TAC [DIVISION_SIMP]],
      REWRITE_TAC [NSUM_RMUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC (← q "0") THEN
      REWRITE_TAC [ADD_CLAUSES, ← ARITH_RULE (← q r"0 < e - 1 <=> 2 EXP 1 <= e")] THEN
      SIMP_TAC [LE_EXP, LE_1, DIMINDEX_NONZERO, ARITH_EQ] THEN
      CONV_TAC SYM_CONV THEN SPEC_TAC (← q "k:num", ← q "k:num") THEN
      MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC [NSUM_CLAUSES_NUMSEG_LT] THEN
      SIMP_TAC [MULT_CLAUSES, EXP, SUB_REFL] THEN X_GEN_TAC (← q "i:num") THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN
      SIMP_TAC [← GSYM INT_OF_NUM_EQ, ← GSYM INT_OF_NUM_ADD, ← GSYM INT_OF_NUM_MUL] THEN
      SIMP_TAC [← GSYM INT_OF_NUM_SUB, LE_1, EXP_EQ_0, ARITH_EQ] THEN
      REWRITE_TAC [← GSYM INT_OF_NUM_POW, EXP_ADD] THEN
      REWRITE_TAC [← ARITH_RULE (← q r"i * dimindex(:M) = dimindex(:M) * i")] THEN
      REWRITE_TAC [INT_POW_ADD] THEN CONV_TAC (fun t => (INT_ARITH t).run)])

  let WORD_DUPLICATE ← prove
   r"!m k. dimindex(:N) <= k * dimindex(:M)
         ==> (word_duplicate:M word->N word)(word m) =
             word((2 EXP (k * dimindex(:M)) - 1) DIV
                  (2 EXP dimindex(:M) - 1) * m MOD 2 EXP dimindex(:M))"
   (SIMP_TAC [← REWRITE_RULE [VAL_WORD_GALOIS] VAL_WORD_DUPLICATE] THEN
    REWRITE_TAC [VAL_WORD, WORD_MOD_SIZE])

  let WORD_SUBWORD_ZX ← prove
   r"!x pos len.
        MIN (pos + dimindex(:P)) (dimindex(:M)) <= dimindex(:N)
        ==> word_subword ((word_zx:M word->N word) x) (pos,len):P word =
               word_subword x (pos,len)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_SUBWORD, BIT_WORD_ZX] THEN
    X_GEN_TAC (← q "i:num") THEN STRIP_TAC THEN
    ASM_CASES_TAC (← q "i:num < len") THEN
    ASM_REWRITE_TAC [← ARITH_RULE (← q r"i < MIN a b <=> i < a /\ i < b")] THEN
    ONCE_REWRITE_TAC [BIT_GUARD] THEN
    REWRITE_TAC [← TAUT (← q r"(p /\ q <=> q) <=> q ==> p")] THEN STRIP_TAC THEN
    ASM_ARITH_TAC)

  let WORD_SUBWORD_ZX_TRIVIAL ← prove
   r"!x pos len.
        MIN (dimindex(:M)) (dimindex(:N)) <= pos
        ==> word_subword ((word_zx:M word->N word) x) (pos,len):P word =
            word 0"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_SUBWORD, BIT_WORD_ZX, BIT_WORD_0] THEN
    X_GEN_TAC (← q "i:num") THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC [BIT_GUARD] THEN ASM_ARITH_TAC)

  let WORD_SIMPLE_SUBWORD_CONV ← do
    let dimarith_conv := DEPTH_CONV ((← D.word_SIZE_CONV.get) ORELSEC NUM_RED_CONV)
    let dimarith_rule (th : thm) : ExceptT String IO thm := do
      MP th (← EQT_ELIM (← ExceptT.mk (dimarith_conv (← liftExcept (lhand (concl th))))))
    let post_rule := CONV_RULE (RAND_CONV (RAND_CONV (BINOP_CONV dimarith_conv)))
    let triv_rule ← do
      let c ← GEN_REWRITE_CONV_NET (RAND_CONV o TRY_CONV) [WORD_DUPLICATE_REFL]
      pure (CONV_RULE c)
    let pm (th : thm) : term → ExceptT String IO thm := PART_MATCH (lhand o rand) th
    let rules_join := [pm WORD_SUBWORD_JOIN_LOWER, pm WORD_SUBWORD_JOIN_UPPER]
    let rules_insert := [pm WORD_SUBWORD_INSERT_OUTER, pm WORD_SUBWORD_INSERT_INNER]
    let rules_zx := [pm WORD_SUBWORD_ZX_TRIVIAL, pm WORD_SUBWORD_ZX]
    let rules_subword := [pm WORD_SUBWORD_SUBWORD]
    let rules_duplicate := [pm WORD_SUBWORD_DUPLICATE]
    let rule_duplicate := pm WORD_SUBWORD_DUPLICATE_DUPLICATE
    let rule_trivial := pm WORD_SUBWORD_TRIVIAL
    let viaList (rs : List (term → ExceptT String IO thm)) (tm : term) :=
      tryfindE (fun f => do dimarith_rule (← f tm)) rs
    pure fun (tm : term) => ExceptT.run do
      match tm with
      | .Comb (.Comb (.Const "word_subword" _) itm)
              (.Comb (.Comb (.Const "," _) (.Comb (.Const "NUMERAL" _) _))
                     (.Comb (.Const "NUMERAL" _) _)) =>
        tryWith (do dimarith_rule (← rule_trivial tm)) (do
          match itm with
          | .Comb (.Comb (.Const "word_join" _) _) _ => post_rule (← viaList rules_join tm)
          | .Comb (.Comb (.Comb (.Const "word_insert" _) _) _) _ =>
            post_rule (← viaList rules_insert tm)
          | .Comb (.Comb (.Const "word_subword" _) _) _ =>
            post_rule (← viaList rules_subword tm)
          | .Comb (.Const "word_zx" _) _ => viaList rules_zx tm
          | .Comb (.Const "word_duplicate" _) _ =>
            tryWith (do triv_rule (← dimarith_rule (← rule_duplicate tm)))
              (do post_rule (← viaList rules_duplicate tm))
          | _ => throw "WORD_SIMPLE_SUBWORD_CONV")
      | _ => throw "WORD_SIMPLE_SUBWORD_CONV"

  return { word_insert, BIT_WORD_INSERT, WORD_SUBWORD_INSERT_OUTER, WORD_SUBWORD_INSERT_INNER,
           word_duplicate, BIT_WORD_DUPLICATE, WORD_DUPLICATE_REFL, WORD_DUPLICATE_DOUBLE,
           WORD_SUBWORD_DUPLICATE, WORD_SUBWORD_DUPLICATE_DUPLICATE, VAL_WORD_DUPLICATE,
           WORD_DUPLICATE, WORD_SUBWORD_ZX, WORD_SUBWORD_ZX_TRIVIAL, WORD_SIMPLE_SUBWORD_CONV }

/- ------------------------------------------------------------------------- -/
/- Bit recursion equations for "linear" operations.                          -/
/- ------------------------------------------------------------------------- -/

structure BitRec where
  BIT_WORD_ADD : thm
  BIT_WORD_SUB : thm
  BIT_WORD_NEG : thm
  BIT_WORD_ADD_CLAUSES : thm
  BIT_WORD_SUB_CLAUSES : thm
  BIT_WORD_NEG_CLAUSES : thm
  LE_VAL_MOD_STEP : thm
  LT_VAL_MOD_STEP : thm
  deriving Inhabited

@[nospecialize]
def setupBitRec [HolBase] (D : WordsDeps) (BBitval : Bitval) (BWordType : WordType) (BVal : Val) (BWordOps1 : WordOps1) (BWordRule : WordRule) :
    ExceptT String IO BitRec := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, NUM_REDUCE_CONV, .. } := D
  let { ADD1, ADD_CLAUSES, ADD_EQ_0, ADD_SUB, ARITH_EQ, COND_SWAP, DIMINDEX_GE_1,
        DIVISION, DIV_MULT_ADD, EVEN_ADD, EXP, EXP_1, EXP_ADD, EXP_EQ_0, .. } := D.core1
  let { LE, LE_1, LE_ADD, LE_ADD_LCANCEL, LT_ADD_LCANCEL, LT_IMP_LE, MOD_1,
        MOD_2_CASES, MOD_ADD_CASES, MOD_ADD_MOD, MOD_LT, MOD_MOD_EXP_MIN, MOD_MULT_ADD,
        MOD_MULT_MOD, MULT_CLAUSES, NOT_IMP, NOT_LE, NOT_LT, .. } := D.core3
  let { SUB_ADD, .. } := D.core4
  let { BITVAL_CLAUSES, .. } := BBitval
  let { BIT_TRIVIAL, .. } := BWordType
  let { BIT_VAL_MOD, BIT_WORD_0, VAL_MOD_STEP, .. } := BVal
  let { BIT_WORD_NOT, VAL_WORD_ADD, .. } := BWordOps1
  let { WORD_RULE, .. } := BWordRule
  -- @@SCOPE END

  -- prove(`..`, let lemma = prove(..) in tac): the tactic, and so `lemma`,
  -- is evaluated before the goal is parsed.
  let BIT_WORD_ADD ← prove
   r"!x (y:N word) i.
        bit i (word_add x y) <=>
        i < dimindex(:N) /\
        ((bit i x <=> bit i y) <=>
         ~(i = 0) /\
         (bit (i - 1) x /\ bit (i - 1) y \/
          (bit (i - 1) x \/ bit (i - 1) y) /\
          ~(bit (i - 1) (word_add x y))))"
   (← do
    let lemma ← prove
     r"2 EXP i <= (2 EXP i * b + x) MOD 2 EXP (i + 1) <=>
     (EVEN b <=> 2 EXP i <= x MOD (2 EXP (i + 1)))"
     (SIMP_TAC [EXP_ADD, EXP_1, MOD_MULT_MOD, EXP_EQ_0, ARITH_EQ,
                DIV_MULT_ADD, MOD_MULT_ADD] THEN
      REWRITE_TAC [MOD_2_CASES, EVEN_ADD] THEN
      MAP_EVERY ASM_CASES_TAC [← q "EVEN b", ← q "EVEN(x DIV 2 EXP i)"] THEN
      ASM_REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES, LE_ADD, NOT_LE] THEN
      SIMP_TAC [DIVISION, EXP_EQ_0, ARITH_EQ])
    pure (REPEAT GEN_TAC THEN
      ASM_CASES_TAC (← q "i < dimindex(:N)") THENL
       [ASM_REWRITE_TAC [], ASM_MESON_TAC [NOT_LT, BIT_TRIVIAL]] THEN
      GEN_REWRITE_TAC LAND_CONV [BIT_VAL_MOD] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [BIT_VAL_MOD] THEN
      ASM_REWRITE_TAC [VAL_WORD_ADD, MOD_MOD_EXP_MIN] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
        [← TAUT (← q r"~p /\ q <=> ~(~p ==> ~q)")] THEN
      ASM_SIMP_TAC [SUB_ADD, LE_1, ← ARITH_RULE
        (← q r"~(k = 0) /\ k < n ==> MIN n (k - 1 + 1) = k")] THEN
      ASM_SIMP_TAC [NOT_IMP, ← ARITH_RULE (← q r"k < n ==> MIN n (k + 1) = k + 1")] THEN
      ONCE_REWRITE_TAC [← GSYM MOD_ADD_MOD] THEN
      REWRITE_TAC [VAL_MOD_STEP, lemma, ← ARITH_RULE
       (← q r"(k * b + x) + (k * c + y):num = k * (b + c) + x + y")] THEN
      BINOP_TAC THENL
       [MAP_EVERY ASM_CASES_TAC [← q "bit i (x:N word)", ← q "bit i (y:N word)"] THEN
        ASM_REWRITE_TAC [BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV,
        SIMP_TAC [EXP_ADD, EXP_1, MOD_LT, DIVISION, EXP_EQ_0, ARITH_EQ,
                  ← ARITH_RULE (← q r"x < n /\ y < n ==> x + y < n * 2")]] THEN
      ASM_CASES_TAC (← q "i = 0") THEN
      ASM_SIMP_TAC [EXP, MOD_1, ADD_CLAUSES, ← CONJUNCT1 LE,
                    EXP_EQ_0, ARITH_EQ] THEN
      SIMP_TAC [MOD_ADD_CASES, DIVISION, EXP_EQ_0, ARITH_EQ] THEN
      REWRITE_TAC [← GSYM NOT_LE] THEN
      MAP_EVERY ABBREV_TAC
       [← q r"m = val(x:N word) MOD 2 EXP i", ← q r"n = val(y:N word) MOD 2 EXP i"] THEN
      SUBGOAL_THEN (← q r"m < 2 EXP i /\ n < 2 EXP i") MP_TAC THENL
       [ASM_MESON_TAC [DIVISION, EXP_EQ_0, ← ARITH_RULE (← q r"~(2 = 0)")], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"2 EXP i = 2 * 2 EXP(i - 1)") SUBST1_TAC THENL
       [ASM_SIMP_TAC [← GSYM (← CONJUNCT2 EXP), ADD1, SUB_ADD, LE_1],
        ABBREV_TAC (← q "j = i - 1") THEN
        REWRITE_TAC [COND_SWAP, NOT_LE] THEN ASM_ARITH_TAC]))

  let BIT_WORD_SUB ← prove
   r"!x (y:N word) i.
        bit i (word_sub x y) <=>
        i < dimindex(:N) /\
        ((bit i x <=> bit i y) <=>
         ~(i = 0) /\
         (~bit (i - 1) x /\ bit (i - 1) y \/
          (~bit (i - 1) x \/ bit (i - 1) y) /\
          bit (i - 1) (word_sub x y)))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← WORD_RULE
     (← q r"word_sub x y:N word = word_not(word_add (word_not x) y)")] THEN
    REWRITE_TAC [BIT_WORD_NOT] THEN
    ASM_CASES_TAC (← q "i < dimindex(:N)") THEN ASM_REWRITE_TAC [] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [BIT_WORD_ADD] THEN
    ASM_SIMP_TAC [BIT_WORD_NOT, ← ARITH_RULE (← q r"i < n ==> i - 1 < n")] THEN
    REWRITE_TAC [← TAUT (← q r"~((~p <=> q) <=> r) <=> ((p <=> q) <=> r)")])

  let BIT_WORD_NEG ← prove
   r"!(x:N word) i.
        bit i (word_neg x) <=>
        i < dimindex(:N) /\
        (bit i x <=> i = 0 \/ ~bit (i - 1) x /\ ~bit (i - 1) (word_neg x))"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [← WORD_RULE (← q r"word_neg x:N word = word_sub (word 0) x")] THEN
    GEN_REWRITE_TAC LAND_CONV [BIT_WORD_SUB] THEN
    REWRITE_TAC [BIT_WORD_0] THEN CONV_TAC (fun t => (TAUT t).run))

  let BIT_WORD_ADD_CLAUSES ← prove
   r"(!x (y:N word).
        bit 0 (word_add x y) <=> ~(bit 0 x <=> bit 0 y)) /\
   (!x (y:N word) i.
        bit (i + 1) (word_add x y) <=>
        i + 1 < dimindex(:N) /\
        ((bit (i + 1) x <=> bit (i + 1) y) <=>
         (bit i x /\ bit i y \/
          (bit i x \/ bit i y) /\ ~(bit i (word_add x y)))))"
   (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [BIT_WORD_ADD] THEN
    SIMP_TAC [DIMINDEX_GE_1, LE_1, ADD_SUB, ADD_EQ_0, ARITH_EQ])

  let BIT_WORD_SUB_CLAUSES ← prove
   r"(!x (y:N word).
        bit 0 (word_sub x y) <=> ~(bit 0 x <=> bit 0 y)) /\
   (!x (y:N word) i.
        bit (i + 1) (word_sub x y) <=>
        i + 1 < dimindex(:N) /\
        ((bit (i + 1) x <=> bit (i + 1) y) <=>
         (~bit i x /\ bit i y \/
          (~bit i x \/ bit i y) /\ bit i (word_sub x y))))"
   (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [BIT_WORD_SUB] THEN
    SIMP_TAC [DIMINDEX_GE_1, LE_1, ADD_SUB, ADD_EQ_0, ARITH_EQ])

  let BIT_WORD_NEG_CLAUSES ← prove
   r"(!(x:N word).
        bit 0 (word_neg x) = bit 0 x) /\
   (!(x:N word) i.
        bit (i + 1) (word_neg x) <=>
        i + 1 < dimindex(:N) /\
        (bit (i + 1) x <=> ~bit i x /\ ~bit i (word_neg x)))"
   (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [BIT_WORD_NEG] THEN
    SIMP_TAC [DIMINDEX_GE_1, LE_1, ADD_SUB, ADD_EQ_0, ARITH_EQ])

  let LE_VAL_MOD_STEP ← prove
   r"!(x:N word) (y:N word) i.
        (val x MOD 2 EXP (i + 1)) <= (val y MOD 2 EXP (i + 1)) <=>
        ~bit i x /\ bit i y \/
        (bit i x <=> bit i y) /\ val x MOD 2 EXP i <= val y MOD 2 EXP i"
   (REPEAT GEN_TAC THEN REWRITE_TAC [VAL_MOD_STEP] THEN
    MAP_EVERY BOOL_CASES_TAC [← q "bit i (x:N word)", ← q "bit i (y:N word)"] THEN
    ASM_REWRITE_TAC [BITVAL_CLAUSES, ADD_CLAUSES, MULT_CLAUSES] THEN
    REWRITE_TAC [LE_ADD_LCANCEL, NOT_LE] THEN TRY (MATCH_MP_TAC LT_IMP_LE) THEN
    MATCH_MP_TAC (← ARITH_RULE (← q r"x:num < y ==> x < y + z")) THEN
    SIMP_TAC [DIVISION, EXP_EQ_0, ARITH_EQ])

  let LT_VAL_MOD_STEP ← prove
   r"!(x:N word) (y:N word) i.
        (val x MOD 2 EXP (i + 1)) < (val y MOD 2 EXP (i + 1)) <=>
        ~bit i x /\ bit i y \/
        (bit i x <=> bit i y) /\ val x MOD 2 EXP i < val y MOD 2 EXP i"
   (REPEAT GEN_TAC THEN REWRITE_TAC [VAL_MOD_STEP] THEN
    MAP_EVERY BOOL_CASES_TAC [← q "bit i (x:N word)", ← q "bit i (y:N word)"] THEN
    ASM_REWRITE_TAC [BITVAL_CLAUSES, ADD_CLAUSES, MULT_CLAUSES] THEN
    REWRITE_TAC [LT_ADD_LCANCEL, NOT_LT] THEN TRY (MATCH_MP_TAC LT_IMP_LE) THEN
    MATCH_MP_TAC (← ARITH_RULE (← q r"x:num < y ==> x < y + z")) THEN
    SIMP_TAC [DIVISION, EXP_EQ_0, ARITH_EQ])

  return { BIT_WORD_ADD, BIT_WORD_SUB, BIT_WORD_NEG, BIT_WORD_ADD_CLAUSES,
           BIT_WORD_SUB_CLAUSES, BIT_WORD_NEG_CLAUSES, LE_VAL_MOD_STEP, LT_VAL_MOD_STEP }

/- ------------------------------------------------------------------------- -/
/- Miscellaneous lemmas we don't want to keep regenerating. Many of them in  -/
/- any case need a little bit of manual effort.                              -/
/- ------------------------------------------------------------------------- -/

structure Misc1 where
  -- @@FIELDS
  WORD_ADD_0 : thm
  WORD_ADD_SYM : thm
  WORD_ADD_ASSOC : thm
  WORD_ADD_AC : thm
  WORD_MUL_0 : thm
  WORD_MUL_SYM : thm
  WORD_MUL_ASSOC : thm
  WORD_MUL_AC : thm
  WORD_SUB_0 : thm
  WORD_SUB_LZERO : thm
  WORD_SUB_EQ_0 : thm
  WORD_SUB_REFL : thm
  WORD_NEG_NEG : thm
  WORD_NEG_0 : thm
  WORD_NEG_SUB : thm
  WORD_NEG_EQ_0 : thm
  WORD_NOT_NOT : thm
  WORD_AND_REFL : thm
  WORD_AND_0 : thm
  WORD_AND_NOT0 : thm
  WORD_AND_SYM : thm
  WORD_AND_ASSOC : thm
  WORD_OR_REFL : thm
  WORD_OR_0 : thm
  WORD_OR_NOT0 : thm
  WORD_OR_SYM : thm
  WORD_OR_ASSOC : thm
  WORD_OR_EQ_0 : thm
  WORD_NOT_AND : thm
  WORD_NOT_OR : thm
  WORD_XOR_EQ_0 : thm
  WORD_XOR_0 : thm
  WORD_XOR_NOT : thm
  WORD_XOR_NOT0 : thm
  WORD_XOR_REFL : thm
  WORD_XOR_SYM : thm
  WORD_XOR_ASSOC : thm
  WORD_AND_1 : thm
  WORD_AND_1_BITVAL : thm
  WORD_NOT_NEG : thm
  WORD_NOT_SUB : thm
  WORD_NOT_ADD : thm
  VAL_WORD_SUB_EQ_0 : thm
  VAL_EQ_MAX_ALT : thm
  VAL_EQ_MAX : thm
  VAL_EQ_MAX_MASK : thm
  VAL_WORD_OR_EQ_0 : thm
  VAL_WORD_AND_EQ_MAX : thm
  WORD_SHL_AND : thm
  WORD_USHR_AND : thm
  WORD_SHL_OR : thm
  WORD_USHR_OR : thm
  WORD_SHL_XOR : thm
  WORD_USHR_XOR : thm
  WORD_ADD_XOR_GEN : thm
  WORD_ADD_OR_GEN : thm
  WORD_OR_XOR_GEN : thm
  WORD_ADD_OR_EQ : thm
  WORD_OR_XOR_EQ : thm
  WORD_ADD_OR : thm
  WORD_OR_XOR : thm
  WORD_ADD_XOR : thm
  WORD_POPCOUNT_ADD_DISJOINT : thm
  WORD_POPCOUNT_XOR_AND : thm
  WORD_POPCOUNT_OR_AND : thm
  WORD_POPCOUNT_XOR_AND2 : thm
  WORD_POPCOUNT_XOR : thm
  WORD_SUB_XOR : thm
  WORD_XOR_SUB : thm
  WORD_SUB_MASK_WORD : thm
  WORD_XOR_MASK_WORD : thm
  WORD_XOR_INT_MIN : thm
  WORD_BITVAL_NOT : thm
  IVAL_WORD_NOT : thm
  BIT_WORD_NEG_CASES : thm
  BIT_WORD_ADD_1_CASES : thm
  BIT_WORD_SUB_1_CASES : thm
  BIT_WORD_AND_NEG : thm
  BIT_WORD_OR_NEG : thm
  BIT_WORD_XOR_NEG : thm
  BIT_WORD_AND_ADD_1 : thm
  BIT_WORD_AND_SUB_1 : thm
  BIT_WORD_OR_ADD_1 : thm
  BIT_WORD_OR_SUB_1 : thm
  BIT_WORD_XOR_ADD_1 : thm
  BIT_WORD_XOR_SUB_1 : thm
  BIT_WORD_AND_NOT_SUB_1 : thm
  BIT_WORD_AND_NOT_ADD_1 : thm
  WORD_OR_SHL_USHR : thm
  WORD_OR_USHR_SHL : thm
  WORD_ADD_SHL_USHR : thm
  WORD_ADD_USHR_SHL : thm
  deriving Inhabited

@[nospecialize]
def setupMisc1 [HolBase] (D : WordsDeps) (BBitval : Bitval) (BWordType : WordType) (BBitsOfWord : BitsOfWord) (BVal : Val) (BIval : Ival) (BLimits : Limits) (BPopcount : Popcount) (BWordOps1 : WordOps1) (BWordOps2 : WordOps2) (BWordOps3 : WordOps3) (BWordRule : WordRule) (BWordBitwise : WordBitwise) (BZxSx : ZxSx) (BJoinSubword : JoinSubword) (BBitRec : BitRec) :
    ExceptT String IO Misc1 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, INT_ARITH, MESON, MESON_TAC,
        MOD_DOWN_CONV, .. } := D
  let { ADD1, ADD_EQ_0, ADD_SYM, ARITH_EQ, CARD_SUBSET, CARD_UNION_GEN, CONG,
        DIMINDEX_GE_1, DIMINDEX_TYBIT0, EXISTS_OR_THM, EXP_1, .. } := D.core1
  let { INTER_SUBSET, .. } := D.core2
  let { LE_1, LE_ADD, LE_LT, LT, NOT_LE, NOT_LT, .. } := D.core3
  let { RIGHT_OR_DISTRIB, SUB_0, UNWIND_THM2, num_INDUCTION, .. } := D.core4
  let { BITVAL_CLAUSES, bitval, .. } := BBitval
  let { BIT_TRIVIAL, WORD_EQ_BITS, WORD_EQ_BITS_ALT, .. } := BWordType
  let { FINITE_BITS_OF_WORD, .. } := BBitsOfWord
  let { BIT_MASK_WORD, BIT_WORD_0, BIT_WORD_1, BLOCK_BITS_ZERO, VAL_CONG, VAL_EQ,
        VAL_EQ_0, VAL_MOD_REFL, VAL_WORD_0, .. } := BVal
  let { IVAL_BOUND, IVAL_IWORD_GALOIS, IWORD_IVAL, WORD_IWORD, .. } := BIval
  let { BIT_WORD_INT_MIN, .. } := BLimits
  let { word_popcount, .. } := BPopcount
  let { BITS_OF_WORD_AND, BITS_OF_WORD_OR, BIT_WORD_AND, BIT_WORD_NOT, BIT_WORD_OR,
        BIT_WORD_XOR, IWORD_INT_ADD, IWORD_INT_NEG, VAL_WORD_ADD, VAL_WORD_ADD_AND_OR,
        VAL_WORD_ADD_AND_XOR, VAL_WORD_NOT, VAL_WORD_OR_AND_XOR,
        WORD_POPCOUNT_OR_DISJOINT, .. } := BWordOps1
  let { BIT_WORD_SHL, VAL_WORD_SHL, WORD_NEG_1, WORD_NOT_AS_SUB, .. } := BWordOps2
  let { BIT_WORD_USHR, .. } := BWordOps3
  let { WORD_RULE, .. } := BWordRule
  let { WORD_BITWISE_RULE, .. } := BWordBitwise
  let { BIT_WORD_ZX, .. } := BZxSx
  let { BIT_WORD_JOIN, .. } := BJoinSubword
  let { BIT_WORD_ADD_CLAUSES, BIT_WORD_NEG_CLAUSES, BIT_WORD_SUB_CLAUSES, .. } := BBitRec
  -- @@SCOPE END
  let WR : tactic := CONV_TAC (fun t => (WORD_RULE t).run)
  let WBR : tactic := CONV_TAC (fun t => (WORD_BITWISE_RULE t).run)

  let WORD_ADD_0 ← prove
   r"(!x:N word. word_add x (word 0) = x) /\
   (!x:N word. word_add (word 0) x = x)"
   WR

  let WORD_ADD_SYM ← prove
   r"!x y:N word. word_add x y = word_add y x"
   WR

  let WORD_ADD_ASSOC ← prove
   r"!x y z:N word. word_add x (word_add y z) =
                  word_add (word_add x y) z"
   WR

  let WORD_ADD_AC ← prove
   r"word_add x y = word_add y x /\
   word_add (word_add x y) z = word_add x (word_add y z) /\
   word_add x (word_add y z) = word_add y (word_add x z)"
   WR

  let WORD_MUL_0 ← prove
   r"(!x:N word. word_mul x (word 0) = word 0) /\
   (!x:N word. word_mul (word 0) x = word 0)"
   WR

  let WORD_MUL_SYM ← prove
   r"!x y:N word. word_mul x y = word_mul y x"
   WR

  let WORD_MUL_ASSOC ← prove
   r"!x y z:N word. word_mul x (word_mul y z) =
                  word_mul (word_mul x y) z"
   WR

  let WORD_MUL_AC ← prove
   r"word_mul x y = word_mul y x /\
   word_mul (word_mul x y) z = word_mul x (word_mul y z) /\
   word_mul x (word_mul y z) = word_mul y (word_mul x z)"
   WR

  let WORD_SUB_0 ← prove
   r"!x:N word. word_sub x (word 0) = x"
   WR

  let WORD_SUB_LZERO ← prove
   r"!x:N word. word_sub (word 0) x = word_neg x"
   WR

  let WORD_SUB_EQ_0 ← prove
   r"!x y:N word. word_sub x y = word 0 <=> x = y"
   WR

  let WORD_SUB_REFL ← prove
   r"!x:N word. word_sub x x = word 0"
   WR

  let WORD_NEG_NEG ← prove
   r"!x:N word. word_neg(word_neg x) = x"
   WR

  let WORD_NEG_0 ← prove
   r"word_neg (word 0) = word 0"
   WR

  let WORD_NEG_SUB ← prove
   r"!x y:N word. word_neg(word_sub x y) = word_sub y x"
   WR

  let WORD_NEG_EQ_0 ← prove
   r"!x:N word. word_neg x = word 0 <=> x = word 0"
   WR

  let WORD_NOT_NOT ← prove
   r"!x:N word. word_not(word_not x) = x"
   WBR

  let WORD_AND_REFL ← prove
   r"!x:N word. word_and x x = x"
   WBR

  let WORD_AND_0 ← prove
   r"(!x:N word. word_and x (word 0) = word 0) /\
   (!x:N word. word_and (word 0) x = word 0)"
   WBR

  let WORD_AND_NOT0 ← prove
   r"(!x:N word. word_and x (word_not(word 0)) = x) /\
   (!x:N word. word_and (word_not(word 0)) x = x)"
   WBR

  let WORD_AND_SYM ← prove
   r"!x y:N word. word_and x y = word_and y x"
   WBR

  let WORD_AND_ASSOC ← prove
   r"!x y z:N word. word_and x (word_and y z) = word_and (word_and x y) z"
   WBR

  let WORD_OR_REFL ← prove
   r"!x:N word. word_or x x = x"
   WBR

  let WORD_OR_0 ← prove
   r"(!x:N word. word_or x (word 0) = x) /\
   (!x:N word. word_or (word 0) x = x)"
   WBR

  let WORD_OR_NOT0 ← prove
   r"(!x:N word. word_or x (word_not(word 0)) = word_not(word 0)) /\
   (!x:N word. word_or (word_not(word 0)) x = word_not(word 0))"
   WBR

  let WORD_OR_SYM ← prove
   r"!x y:N word. word_or x y = word_or y x"
   WBR

  let WORD_OR_ASSOC ← prove
   r"!x y z:N word. word_or x (word_or y z) = word_or (word_or x y) z"
   WBR

  let WORD_OR_EQ_0 ← prove
   r"!x y:N word. word_or x y = word 0 <=> x = word 0 /\ y = word 0"
   WBR

  let WORD_NOT_AND ← prove
   r"!x y:N word. word_not(word_and x y) = word_or (word_not x) (word_not y)"
   WBR

  let WORD_NOT_OR ← prove
   r"!x y:N word. word_not(word_or x y) = word_and (word_not x) (word_not y)"
   WBR

  let WORD_XOR_EQ_0 ← prove
   r"!x y:N word. word_xor x y = word 0 <=> x = y"
   WBR

  let WORD_XOR_0 ← prove
   r"(!x:N word. word_xor x (word 0) = x) /\
   (!x:N word. word_xor (word 0) x = x)"
   WBR

  let WORD_XOR_NOT ← prove
   r"(!x y:N word. word_xor (word_not x) y = word_not(word_xor x y)) /\
   (!x y:N word. word_xor x (word_not y) = word_not(word_xor x y))"
   WBR

  let WORD_XOR_NOT0 ← prove
   r"(!x:N word. word_xor x (word_not(word 0)) = word_not x) /\
   (!x:N word. word_xor (word_not(word 0)) x = word_not x)"
   (REWRITE_TAC [WORD_XOR_NOT, WORD_XOR_0])

  let WORD_XOR_REFL ← prove
   r"!x:N word. word_xor x x = word 0"
   (REWRITE_TAC [WORD_XOR_EQ_0])

  let WORD_XOR_SYM ← prove
   r"!x y:N word. word_xor x y = word_xor y x"
   WBR

  let WORD_XOR_ASSOC ← prove
   r"!x y z:N word. word_xor x (word_xor y z) = word_xor (word_xor x y) z"
   WBR

  let WORD_AND_1 ← prove
   r"(!x:N word. word_and x (word 1) = if bit 0 x then word 1 else word 0) /\
   (!x:N word. word_and (word 1) x = if bit 0 x then word 1 else word 0)"
   (REWRITE_TAC [← WORD_BITWISE_RULE
     (← q r"word_and (word 1:N word) x = word_and x (word 1)")] THEN
    GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC [WORD_EQ_BITS, BIT_WORD_AND, BIT_WORD_1, BIT_WORD_0] THEN
    X_GEN_TAC (← q "i:num") THEN ASM_CASES_TAC (← q "i = 0") THEN
    ASM_REWRITE_TAC [BIT_WORD_0] THEN SIMP_TAC [DIMINDEX_GE_1, LE_1])

  let WORD_AND_1_BITVAL ← prove
   r"(!x:N word. word_and (word 1) x = word(bitval(bit 0 x))) /\
   (!x:N word. word_and x (word 1) = word(bitval(bit 0 x)))"
   (REWRITE_TAC [bitval, WORD_AND_1] THEN MESON_TAC [])

  let WORD_NOT_NEG ← prove
   r"!x:N word. word_not(word_neg x) = word_sub x (word 1)"
   (GEN_TAC THEN REWRITE_TAC [WORD_NOT_AS_SUB] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN WR)

  let WORD_NOT_SUB ← prove
   r"!x y:N word.
        word_not(word_sub x y) = word_add (word_not x) y"
   (REWRITE_TAC [WORD_NOT_AS_SUB] THEN WR)

  let WORD_NOT_ADD ← prove
   r"!x y:N word.
        word_not(word_add x y) = word_add (word_not x) (word_neg y)"
   (REWRITE_TAC [WORD_NOT_AS_SUB] THEN WR)

  let VAL_WORD_SUB_EQ_0 ← prove
   r"!x y:N word. val(word_sub x y) = 0 <=> val x = val y"
   (REWRITE_TAC [VAL_EQ_0, WORD_SUB_EQ_0] THEN REWRITE_TAC [VAL_EQ])

  let VAL_EQ_MAX_ALT ← prove
   r"!x:N word. val x = 2 EXP dimindex(:N) - 1 <=> x = word_not(word 0)"
   (GEN_TAC THEN REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_NOT, VAL_WORD_0, SUB_0])

  let VAL_EQ_MAX ← prove
   r"!x:N word. val x = 2 EXP dimindex(:N) - 1 <=> word_not x = word 0"
   (REWRITE_TAC [VAL_EQ_MAX_ALT] THEN WBR)

  let VAL_EQ_MAX_MASK ← prove
   r"!x:N word. val x = 2 EXP dimindex(:N) - 1 <=> x = word_neg(word 1)"
   (REWRITE_TAC [WORD_NEG_1, VAL_EQ_MAX_ALT])

  let VAL_WORD_OR_EQ_0 ← prove
   r"!x y:N word. val(word_or x y) = 0 <=> val x = 0 /\ val y = 0"
   (REWRITE_TAC [VAL_EQ_0, WORD_OR_EQ_0])

  let VAL_WORD_AND_EQ_MAX ← prove
   r"!x y:N word.
        val(word_and x y) = 2 EXP dimindex(:N) - 1 <=>
        val x = 2 EXP dimindex(:N) - 1 /\
        val y = 2 EXP dimindex(:N) - 1"
   (REWRITE_TAC [VAL_EQ_MAX] THEN WBR)

  let shlTac (bitop : thm) : ExceptT String IO tactic := do pure (
    REPEAT GEN_TAC THEN
    REWRITE_TAC [WORD_EQ_BITS, BIT_WORD_SHL, bitop] THEN
    X_GEN_TAC (← q "i:num") THEN
    ASM_CASES_TAC (← q "bit (i - n) (v:N word)") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q "bit (i - n) (w:N word)") THEN ASM_REWRITE_TAC [] THEN
    ARITH_TAC)
  let ushrTac (bitop : thm) : ExceptT String IO tactic := do pure (
    REPEAT GEN_TAC THEN
    REWRITE_TAC [WORD_EQ_BITS, BIT_WORD_USHR, bitop] THEN
    X_GEN_TAC (← q "i:num") THEN ASM_CASES_TAC (← q "i + n < dimindex(:N)") THEN
    RULE_ASSUM_TAC (REWRITE_RULE [NOT_LT]) THEN ASM_SIMP_TAC [BIT_TRIVIAL] THEN
    ASM_CASES_TAC (← q "i < dimindex(:N)") THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC)

  let WORD_SHL_AND ← prove
   r"!(v:N word) w n.
        word_shl (word_and v w) n =
        word_and (word_shl v n) (word_shl w n)"
   (← shlTac BIT_WORD_AND)

  let WORD_USHR_AND ← prove
   r"!(v:N word) w n.
        word_ushr (word_and v w) n =
        word_and (word_ushr v n) (word_ushr w n)"
   (← ushrTac BIT_WORD_AND)

  let WORD_SHL_OR ← prove
   r"!(v:N word) w n.
        word_shl (word_or v w) n =
        word_or (word_shl v n) (word_shl w n)"
   (← shlTac BIT_WORD_OR)

  let WORD_USHR_OR ← prove
   r"!(v:N word) w n.
        word_ushr (word_or v w) n =
        word_or (word_ushr v n) (word_ushr w n)"
   (← ushrTac BIT_WORD_OR)

  let WORD_SHL_XOR ← prove
   r"!(v:N word) w n.
        word_shl (word_xor v w) n =
        word_xor (word_shl v n) (word_shl w n)"
   (← shlTac BIT_WORD_XOR)

  let WORD_USHR_XOR ← prove
   r"!(v:N word) w n.
        word_ushr (word_xor v w) n =
        word_xor (word_ushr v n) (word_ushr w n)"
   (← ushrTac BIT_WORD_XOR)

  let WORD_ADD_XOR_GEN ← prove
   r"!x y:N word.
        word_add x y = word_add (word_shl (word_and x y) 1) (word_xor x y)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [← GSYM VAL_CONG, CONG, VAL_WORD_ADD, VAL_WORD_SHL] THEN
    CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXP_1, VAL_WORD_ADD_AND_XOR])

  let WORD_ADD_OR_GEN ← prove
   r"!x y:N word. word_add x y = word_add (word_and x y) (word_or x y)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [← GSYM VAL_CONG, CONG, VAL_WORD_ADD, VAL_WORD_SHL] THEN
    CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [← GSYM VAL_WORD_ADD_AND_OR])

  let WORD_OR_XOR_GEN ← prove
   r"!x y:N word. word_or x y = word_add (word_and x y) (word_xor x y)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [← GSYM VAL_CONG, CONG, VAL_WORD_ADD] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC [VAL_WORD_OR_AND_XOR])

  let WORD_ADD_OR_EQ ← prove
   r"!x y:N word. word_add x y = word_or x y <=> word_and x y = word 0"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [WORD_ADD_OR_GEN] THEN WR)

  let WORD_OR_XOR_EQ ← prove
   r"!x y:N word. word_or x y = word_xor x y <=> word_and x y = word 0"
   (REWRITE_TAC [WORD_OR_XOR_GEN] THEN WR)

  let WORD_ADD_OR ← prove
   r"!x y:N word. word_and x y = word 0 ==> word_add x y = word_or x y"
   (REWRITE_TAC [WORD_ADD_OR_EQ])

  let WORD_OR_XOR ← prove
   r"!x y:N word. word_and x y = word 0 ==> word_or x y = word_xor x y"
   (REWRITE_TAC [WORD_OR_XOR_EQ])

  let WORD_ADD_XOR ← prove
   r"!x y:N word. word_and x y = word 0 ==> word_add x y = word_xor x y"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [WORD_ADD_XOR_GEN] THEN
    ASM_REWRITE_TAC [] THEN WR)

  let WORD_POPCOUNT_ADD_DISJOINT ← prove
   r"!x y:N word.
        word_and x y = word 0
        ==> word_popcount(word_add x y) = word_popcount x + word_popcount y"
   (SIMP_TAC [WORD_ADD_OR, WORD_POPCOUNT_OR_DISJOINT])

  let WORD_POPCOUNT_XOR_AND ← prove
   r"!x y:N word.
        word_popcount(word_xor x y) + word_popcount(word_and x y) =
        word_popcount(word_or x y)"
   (REPEAT GEN_TAC THEN
    SIMP_TAC [← GSYM WORD_POPCOUNT_ADD_DISJOINT, WORD_ADD_OR, ← WORD_BITWISE_RULE
     (← q r"word_and (word_xor x y) (word_and x y) = word 0")] THEN
    AP_TERM_TAC THEN WBR)

  let WORD_POPCOUNT_OR_AND ← prove
   r"!x y:N word.
        word_popcount(word_or x y) + word_popcount(word_and x y) =
        word_popcount x + word_popcount y"
   (REWRITE_TAC [word_popcount, BITS_OF_WORD_OR, BITS_OF_WORD_AND] THEN
    SIMP_TAC [CARD_UNION_GEN, FINITE_BITS_OF_WORD, CARD_SUBSET, INTER_SUBSET,
              ← ARITH_RULE (← q r"x:num <= a ==> (a + b) - x + x = a + b")])

  let WORD_POPCOUNT_XOR_AND2 ← prove
   r"!x y:N word.
        word_popcount(word_xor x y) + 2 * word_popcount(word_and x y) =
        word_popcount x + word_popcount y"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM WORD_POPCOUNT_OR_AND] THEN
    REWRITE_TAC [← GSYM WORD_POPCOUNT_XOR_AND] THEN ARITH_TAC)

  let WORD_POPCOUNT_XOR ← prove
   r"!x y:N word.
      word_popcount(word_xor x y) <= word_popcount x + word_popcount y"
   (REWRITE_TAC [← GSYM WORD_POPCOUNT_XOR_AND2, LE_ADD])

  let WORD_SUB_XOR ← prove
   r"!x y:N word.
        word_and (word_not x) y = word 0 ==> word_sub x y = word_xor x y"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [← WORD_RULE (← q r"word_sub x y = z <=> word_add y z = x")] THEN
    W (MP_TAC o PART_MATCH (lhand o rand) WORD_ADD_XOR o lhand o snd) THEN
    ANTS_TAC THENL [POP_ASSUM MP_TAC, DISCH_THEN SUBST1_TAC] THEN
    WBR)

  let WORD_XOR_SUB ← prove
   r"!x y:N word.
        word_and (word_not x) y = word 0 ==> word_xor x y = word_sub x y"
   (SIMP_TAC [WORD_SUB_XOR])

  let WORD_SUB_MASK_WORD ← prove
   r"!k (x:N word).
        val x < 2 EXP k
        ==> word_sub (word(2 EXP k - 1)) x = word_xor (word(2 EXP k - 1)) x"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC WORD_SUB_XOR THEN
    SIMP_TAC [WORD_EQ_BITS_ALT, BIT_WORD_AND, BIT_WORD_0, BIT_WORD_NOT,
              BIT_MASK_WORD, ← TAUT (← q r"p ==> ~(q /\ r) <=> q /\ p ==> ~r")] THEN
    ASM_REWRITE_TAC [NOT_LT, BLOCK_BITS_ZERO, VAL_MOD_REFL])

  let WORD_XOR_MASK_WORD ← prove
   r"!k (x:N word).
        val x < 2 EXP k
        ==> word_xor (word(2 EXP k - 1)) x = word_sub (word(2 EXP k - 1)) x"
   (SIMP_TAC [WORD_SUB_MASK_WORD])

  -- Two rules evaluated as the tactic is built; the later one first.
  let _wbr ← WORD_BITWISE_RULE (← q r"x = word 0 ==> word_and x y = word 0")
  let _wr ← WORD_RULE (← q r"w:N word = word_add x w <=> x = word 0")
  let WORD_XOR_INT_MIN ← prove
   r"!w:N word. word_xor word_INT_MIN w = word_add word_INT_MIN w"
   (GEN_TAC THEN ONCE_REWRITE_TAC [WORD_ADD_XOR_GEN] THEN
    REWRITE_TAC [_wr] THEN
    REWRITE_TAC [WORD_SHL_AND] THEN
    MATCH_MP_TAC _wbr THEN
    REWRITE_TAC [WORD_EQ_BITS, BIT_WORD_0, BIT_WORD_SHL, BIT_WORD_INT_MIN] THEN
    ARITH_TAC)

  let WORD_BITVAL_NOT ← prove
   r"!b. word(bitval(~b)) = word_sub (word 1) (word(bitval b))"
   (GEN_TAC THEN BOOL_CASES_TAC (← q "b:bool") THEN
    ASM_REWRITE_TAC [BITVAL_CLAUSES] THEN WR)

  let IVAL_WORD_NOT ← prove
   r"!x:N word. ival(word_not x) = --(ival x + &1)"
   (REWRITE_TAC [IVAL_IWORD_GALOIS] THEN
    REWRITE_TAC [← INT_ARITH (← q r"--x:int <= --(y + &1) <=> y < x")] THEN
    REWRITE_TAC [← INT_ARITH (← q r"--(x + &1):int < y <=> --y <= x")] THEN
    REWRITE_TAC [IVAL_BOUND] THEN
    REWRITE_TAC [IWORD_INT_NEG, IWORD_INT_ADD, IWORD_IVAL, ← GSYM WORD_IWORD] THEN
    WR)

  let (BIT_WORD_NEG_CASES, BIT_WORD_ADD_1_CASES, BIT_WORD_SUB_1_CASES) ← do
    let th ← prove
     r"(!(x:N word) i.
        bit i (word_neg x) <=>
        i < dimindex(:N) /\
        (if ?j. j < i /\ bit j x then ~(bit i x) else bit i x)) /\
   (!(x:N word) i.
        bit i (word_add x (word 1)) <=>
        i < dimindex(:N) /\
        (if ?j. j < i /\ ~(bit j x) then bit i x else ~(bit i x))) /\
   (!(x:N word) i.
        bit i (word_sub x (word 1)) <=>
        i < dimindex(:N) /\
        (if ?j. j < i /\ bit j x then bit i x else ~(bit i x)))"
     (REPEAT CONJ_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
      REWRITE_TAC [LT, BIT_WORD_NEG_CLAUSES, BIT_WORD_ADD_CLAUSES,
                   BIT_WORD_SUB_CLAUSES, ADD1, BIT_WORD_1] THEN
      SIMP_TAC [ADD_EQ_0, LE_1, DIMINDEX_GE_1, ARITH_EQ] THEN
      X_GEN_TAC (← q "i:num") THEN DISCH_THEN SUBST1_TAC THEN
      ASM_CASES_TAC (← q "i + 1 < dimindex(:N)") THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [RIGHT_OR_DISTRIB, EXISTS_OR_THM, UNWIND_THM2] THEN
      (ASM_CASES_TAC (← q "i = 0") THEN ASM_SIMP_TAC [LT, LE_1, DIMINDEX_GE_1] THENL
        [CONV_TAC (fun t => (TAUT t).run), ALL_TAC]) THEN
      ASM_CASES_TAC (← q "bit i (x:N word)") THEN ASM_REWRITE_TAC [] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC (← q "bit (i + 1) (x:N word)") THEN ASM_REWRITE_TAC [] THEN
      ASM_ARITH_TAC)
    match CONJUNCTS th with
    | [a, b, c] => pure (a, b, c)
    | _ => throw "Match_failure"

  let BIT_WORD_AND_NEG ← prove
   r"!(x:N word) i.
        bit i (word_and x (word_neg x)) <=>
        bit i x /\ !j. j < i ==> ~(bit j x)"
   (REWRITE_TAC [BIT_WORD_AND, BIT_WORD_NEG_CASES] THEN
    MESON_TAC [BIT_TRIVIAL, NOT_LE])

  let BIT_WORD_OR_NEG ← prove
   r"!(x:N word) i.
        bit i (word_or x (word_neg x)) <=>
        i < dimindex(:N) /\ ?j. j <= i /\ bit j x"
   (REWRITE_TAC [BIT_WORD_OR, BIT_WORD_NEG_CASES] THEN MESON_TAC [LE_LT])

  let BIT_WORD_XOR_NEG ← prove
   r"!(x:N word) i.
        bit i (word_xor x (word_neg x)) <=>
        i < dimindex(:N) /\ ?j. j < i /\ bit j x"
   (REWRITE_TAC [BIT_WORD_NEG_CASES, BIT_WORD_XOR] THEN MESON_TAC [])

  let BIT_WORD_AND_ADD_1 ← prove
   r"!(x:N word) i.
        bit i (word_and x (word_add x (word 1))) <=>
        bit i x /\ ?j. j < i /\ ~bit j x"
   (REWRITE_TAC [BIT_WORD_AND, BIT_WORD_ADD_1_CASES] THEN
    MESON_TAC [BIT_TRIVIAL, NOT_LE])

  let BIT_WORD_AND_SUB_1 ← prove
   r"!(x:N word) i.
        bit i (word_and x (word_sub x (word 1))) <=>
        bit i x /\ ?j. j < i /\ bit j x"
   (REWRITE_TAC [BIT_WORD_AND, BIT_WORD_SUB_1_CASES] THEN
    MESON_TAC [BIT_TRIVIAL, NOT_LE])

  let BIT_WORD_OR_ADD_1 ← prove
   r"!(x:N word) i.
        bit i (word_or x (word_add x (word 1))) <=>
        i < dimindex(:N) /\
        (bit i x \/ !j. j < i ==> bit j x)"
   (REWRITE_TAC [BIT_WORD_OR, BIT_WORD_ADD_1_CASES] THEN MESON_TAC [])

  let BIT_WORD_OR_SUB_1 ← prove
   r"!(x:N word) i.
        bit i (word_or x (word_sub x (word 1))) <=>
        i < dimindex(:N) /\
        (bit i x \/ !j. j < i ==> ~bit j x)"
   (REWRITE_TAC [BIT_WORD_OR, BIT_WORD_SUB_1_CASES] THEN MESON_TAC [])

  let BIT_WORD_XOR_ADD_1 ← prove
   r"!(x:N word) i.
        bit i (word_xor x (word_add x (word 1))) <=>
        i < dimindex(:N) /\ !j. j < i ==> bit j x"
   (REWRITE_TAC [BIT_WORD_ADD_1_CASES, BIT_WORD_XOR] THEN MESON_TAC [])

  let BIT_WORD_XOR_SUB_1 ← prove
   r"!(x:N word) i.
        bit i (word_xor x (word_sub x (word 1))) <=>
        i < dimindex(:N) /\ !j. j < i ==> ~(bit j x)"
   (REWRITE_TAC [BIT_WORD_SUB_1_CASES, BIT_WORD_XOR] THEN MESON_TAC [])

  let BIT_WORD_AND_NOT_SUB_1 ← prove
   r"!(x:N word) i.
        bit i (word_and (word_not x) (word_sub x (word 1))) <=>
        i < dimindex(:N) /\ !j. j <= i ==> ~(bit j x)"
   (REWRITE_TAC [LE_LT, BIT_WORD_AND, BIT_WORD_NOT, BIT_WORD_SUB_1_CASES] THEN
    MESON_TAC [])

  let BIT_WORD_AND_NOT_ADD_1 ← prove
   r"!(x:N word) i.
        bit i (word_and (word_not x) (word_add x (word 1))) <=>
        i < dimindex(:N) /\
         ~(bit i x) /\ !j. j < i ==> bit j x"
   (REWRITE_TAC [BIT_WORD_AND, BIT_WORD_NOT, BIT_WORD_ADD_1_CASES] THEN
    MESON_TAC [])

  let WORD_OR_SHL_USHR ← prove
   r"!(h:N word) l m n.
        m + n = dimindex(:N)
        ==> word_or (word_shl h m) (word_ushr l n) =
            word_zx (word_ushr (word_join h l:(N tybit0)word) n)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [WORD_EQ_BITS_ALT] THEN
    X_GEN_TAC (← q "i:num") THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [BIT_WORD_JOIN, BIT_WORD_ZX, BIT_WORD_SHL, BIT_WORD_USHR,
                     BIT_WORD_OR, DIMINDEX_TYBIT0] THEN
    SUBGOAL_THEN (← q r"m <= i <=> ~(i + n < dimindex(:N))") SUBST1_TAC THENL
     [ASM_ARITH_TAC, ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [← ARITH_RULE (← q r"i < n ==> i < 2 * n")] THEN
    MATCH_MP_TAC (← TAUT (← q r"(p <=> s) /\ (q <=> F) /\ r ==> (p \/ q <=> r /\ s)")) THEN
    REPEAT CONJ_TAC THENL
     [AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC,
      MATCH_MP_TAC BIT_TRIVIAL THEN ASM_ARITH_TAC,
      ASM_ARITH_TAC])

  let WORD_OR_USHR_SHL ← prove
   r"!(h:N word) l m n.
        m + n = dimindex(:N)
        ==> word_or (word_ushr l m) (word_shl h n) =
            word_zx (word_ushr (word_join h l:(N tybit0)word) m)"
   (ONCE_REWRITE_TAC [ADD_SYM, WORD_OR_SYM] THEN
    REWRITE_TAC [WORD_OR_SHL_USHR])

  let WORD_ADD_SHL_USHR ← prove
   r"!(h:N word) l m n.
        m + n = dimindex(:N)
        ==> word_add (word_shl h m) (word_ushr l n) =
            word_zx (word_ushr (word_join h l:(N tybit0)word) n)"
   (REPEAT STRIP_TAC THEN
    W (MP_TAC o PART_MATCH (lhand o rand) WORD_ADD_OR o lhand o snd) THEN
    ASM_SIMP_TAC [WORD_OR_SHL_USHR] THEN DISCH_THEN MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [WORD_EQ_BITS_ALT] THEN
    X_GEN_TAC (← q "i:num") THEN DISCH_TAC THEN
    REWRITE_TAC [BIT_WORD_0, BIT_WORD_AND, BIT_WORD_SHL, BIT_WORD_USHR] THEN
    STRIP_TAC THEN REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP (← MESON [BIT_TRIVIAL]
     (← q r"bit i (x:N word) ==> ~(dimindex(:N) <= i)")))) THEN
    ASM_ARITH_TAC)

  let WORD_ADD_USHR_SHL ← prove
   r"!(h:N word) l m n.
        m + n = dimindex(:N)
        ==> word_add (word_ushr l m) (word_shl h n) =
            word_zx (word_ushr (word_join h l:(N tybit0)word) m)"
   (ONCE_REWRITE_TAC [ADD_SYM, WORD_ADD_SYM] THEN
    REWRITE_TAC [WORD_ADD_SHL_USHR])

  -- @@RETURN BEGIN
  return { WORD_ADD_0, WORD_ADD_SYM, WORD_ADD_ASSOC, WORD_ADD_AC, WORD_MUL_0,
           WORD_MUL_SYM, WORD_MUL_ASSOC, WORD_MUL_AC, WORD_SUB_0, WORD_SUB_LZERO,
           WORD_SUB_EQ_0, WORD_SUB_REFL, WORD_NEG_NEG, WORD_NEG_0, WORD_NEG_SUB,
           WORD_NEG_EQ_0, WORD_NOT_NOT, WORD_AND_REFL, WORD_AND_0, WORD_AND_NOT0,
           WORD_AND_SYM, WORD_AND_ASSOC, WORD_OR_REFL, WORD_OR_0, WORD_OR_NOT0,
           WORD_OR_SYM, WORD_OR_ASSOC, WORD_OR_EQ_0, WORD_NOT_AND, WORD_NOT_OR,
           WORD_XOR_EQ_0, WORD_XOR_0, WORD_XOR_NOT, WORD_XOR_NOT0, WORD_XOR_REFL,
           WORD_XOR_SYM, WORD_XOR_ASSOC, WORD_AND_1, WORD_AND_1_BITVAL, WORD_NOT_NEG,
           WORD_NOT_SUB, WORD_NOT_ADD, VAL_WORD_SUB_EQ_0, VAL_EQ_MAX_ALT, VAL_EQ_MAX,
           VAL_EQ_MAX_MASK, VAL_WORD_OR_EQ_0, VAL_WORD_AND_EQ_MAX, WORD_SHL_AND,
           WORD_USHR_AND, WORD_SHL_OR, WORD_USHR_OR, WORD_SHL_XOR, WORD_USHR_XOR,
           WORD_ADD_XOR_GEN, WORD_ADD_OR_GEN, WORD_OR_XOR_GEN, WORD_ADD_OR_EQ,
           WORD_OR_XOR_EQ, WORD_ADD_OR, WORD_OR_XOR, WORD_ADD_XOR,
           WORD_POPCOUNT_ADD_DISJOINT, WORD_POPCOUNT_XOR_AND, WORD_POPCOUNT_OR_AND,
           WORD_POPCOUNT_XOR_AND2, WORD_POPCOUNT_XOR, WORD_SUB_XOR, WORD_XOR_SUB,
           WORD_SUB_MASK_WORD, WORD_XOR_MASK_WORD, WORD_XOR_INT_MIN, WORD_BITVAL_NOT,
           IVAL_WORD_NOT, BIT_WORD_NEG_CASES, BIT_WORD_ADD_1_CASES, BIT_WORD_SUB_1_CASES,
           BIT_WORD_AND_NEG, BIT_WORD_OR_NEG, BIT_WORD_XOR_NEG, BIT_WORD_AND_ADD_1,
           BIT_WORD_AND_SUB_1, BIT_WORD_OR_ADD_1, BIT_WORD_OR_SUB_1, BIT_WORD_XOR_ADD_1,
           BIT_WORD_XOR_SUB_1, BIT_WORD_AND_NOT_SUB_1, BIT_WORD_AND_NOT_ADD_1,
           WORD_OR_SHL_USHR, WORD_OR_USHR_SHL, WORD_ADD_SHL_USHR, WORD_ADD_USHR_SHL }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- An idiom for describing a mask duplicating a bit throughout a word.       -/
/- Some lemmas about masks 000..001111..1111 and their values.               -/
/- ------------------------------------------------------------------------- -/

structure Masks where
  -- @@FIELDS
  WORD_MASK_ALT : thm
  WORD_MASK : thm
  BIT_WORD_MASK : thm
  WORD_ISHR_MSB : thm
  WORD_NOT_MASK : thm
  WORD_AND_MASK : thm
  WORD_OR_MASK : thm
  WORD_XOR_MASK : thm
  WORD_NEG_AND_MASK : thm
  WORD_AND_MASKS : thm
  WORD_OR_MASKS : thm
  WORD_XOR_MASKS : thm
  WORD_AND_CONDITIONS : thm
  WORD_OR_CONDITIONS : thm
  WORD_XOR_CONDITIONS : thm
  VAL_WORD_MASK : thm
  IVAL_WORD_MASK : thm
  INT_VAL_WORD_MASK : thm
  REAL_VAL_WORD_MASK : thm
  WORD_MUL_EXPAND_ALT : thm
  WORD_SX_ZX_GEN : thm
  BIT_WORD_SX : thm
  VAL_WORD_AND_MASK : thm
  IVAL_WORD_AND_MASK : thm
  VAL_WORD_AND_MASK_WORD : thm
  WORD_AND_MASK_WORD : thm
  VAL_WORD_AND_NOT_MASK_WORD : thm
  WORD_AND_NOT_MASK_WORD : thm
  WORD_BITMASK : thm
  MASK_WORD_SUB : thm
  WORD_AND_MASK_WORDS : thm
  WORD_OR_MASK_WORDS : thm
  WORD_USHR_MASK_WORD : thm
  deriving Inhabited

@[nospecialize]
def setupMasks [HolBase] (D : WordsDeps) (BBitval : Bitval) (BBinary : Binary) (BWordType : WordType) (BBitsOfWord : BitsOfWord) (BVal : Val) (BIval : Ival) (BWordOps1 : WordOps1) (BWordOps2 : WordOps2) (BWordOps3 : WordOps3) (BWordRule : WordRule) (BWordBitwise : WordBitwise) (BZxSx : ZxSx) (BMisc1 : Misc1) :
    ExceptT String IO Masks := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, INTEGER_RULE, INT_ARITH, INT_ARITH_TAC,
        INT_REM_DOWN_CONV, MESON, REAL_ARITH_TAC, .. } := D
  let { ADD_CLAUSES, ARITH_EQ, COND_ID, COND_SWAP, DIMINDEX_NONZERO, DIVISION,
        DIVISION_SIMP, EXP_EQ_0, .. } := D.core1
  let { FINITE_NUMSEG_LT, INT_OF_NUM_CLAUSES, INT_OF_NUM_EQ, INT_OF_NUM_LE,
        INT_OF_NUM_REM, INT_POW_MONO, INT_REM_EQ, IN_ELIM_THM, .. } := D.core2
  let { LE_0, LE_EXP, LTE_TRANS, LT_IMP_LE, MOD_LE, MULT_CLAUSES, NOT_LE, NOT_LT,
        NSUM_EQ, NSUM_RESTRICT_SET, .. } := D.core3
  let { REAL_OF_NUM_EQ, bool_INDUCT, .. } := D.core4
  let { BITVAL_BOUND, BITVAL_CLAUSES, BITVAL_EQ_0, bitval, .. } := BBitval
  let { BINARY_DIGITSUM_MOD, .. } := BBinary
  let { BIT_GUARD, WORD_EQ_BITS_ALT, .. } := BWordType
  let { BIT_WORD_OF_BITS, .. } := BBitsOfWord
  let { BIT_MASK_WORD, BIT_WORD_0, VAL_BOUND, VAL_EQ, VAL_WORD_0, VAL_WORD_BITVAL,
        VAL_WORD_EQ, WORD_OF_BITS_MASK, WORD_OF_BITS_SING_AS_WORD, WORD_VAL, val_def, .. } := BVal
  let { INT_REM_IVAL, IVAL_CONG, IVAL_IWORD, IVAL_VAL, WORD_IWORD, ival, .. } := BIval
  let { BIT_WORD_AND, BIT_WORD_NOT, BIT_WORD_OR, INT_VAL_WORD_NEG_CASES, IWORD_INT_NEG,
        REAL_VAL_WORD_NEG_CASES, VAL_WORD_NEG_CASES, VAL_WORD_OR_DISJOINT, WORD_SUB, .. } := BWordOps1
  let { BIT_WORD_SHL, VAL_WORD_SHL, WORD_NEG_1, WORD_SHL_TRIVIAL, .. } := BWordOps2
  let { BIT_WORD_ISHR, BIT_WORD_USHR, WORD_MUL_EXPAND, .. } := BWordOps3
  let { WORD_RULE, .. } := BWordRule
  let { WORD_BITWISE_RULE, .. } := BWordBitwise
  let { BIT_WORD_ZX, IVAL_WORD_SX, VAL_WORD_ZX, WORD_SX_ZX, .. } := BZxSx
  let { WORD_AND_0, WORD_AND_REFL, WORD_AND_SYM, WORD_NEG_0, WORD_OR_0, WORD_OR_REFL,
        WORD_XOR_0, WORD_XOR_REFL, .. } := BMisc1
  -- @@SCOPE END
  let WR : tactic := CONV_TAC (fun t => (WORD_RULE t).run)
  let WBR : tactic := CONV_TAC (fun t => (WORD_BITWISE_RULE t).run)

  let WORD_MASK_ALT ← prove
   r"!p. word_neg(word(bitval p)) = if p then word_neg(word 1) else word 0"
   (MATCH_MP_TAC bool_INDUCT THEN
    REWRITE_TAC [BITVAL_CLAUSES, WORD_NEG_0])

  let WORD_MASK ← prove
   r"!p. word_neg(word(bitval p)) = if p then word_not(word 0) else word 0"
   (REWRITE_TAC [WORD_MASK_ALT, WORD_NEG_1])

  let BIT_WORD_MASK ← prove
   r"!p i. bit i (word_neg(word(bitval p)):N word) <=> i < dimindex(:N) /\ p"
   (MATCH_MP_TAC bool_INDUCT THEN
    REWRITE_TAC [BITVAL_CLAUSES, WORD_NEG_0, BIT_WORD_0] THEN
    REWRITE_TAC [WORD_NEG_1, BIT_WORD_NOT, BIT_WORD_0])

  let WORD_ISHR_MSB ← prove
   r"!x:N word. word_ishr x (dimindex(:N) - 1) =
              word_neg(word(bitval(bit (dimindex(:N) - 1) x)))"
   (SIMP_TAC [WORD_EQ_BITS_ALT, BIT_WORD_MASK, BIT_WORD_ISHR] THEN
    SIMP_TAC [← ARITH_RULE (← q r"i < n ==> (i + n - 1 < n <=> i = 0)")] THEN
    REWRITE_TAC [COND_ID, ADD_CLAUSES])

  let WORD_NOT_MASK ← prove
   r"!p. word_not(word_neg(word(bitval p))) = word_neg(word(bitval(~p)))"
   (MATCH_MP_TAC bool_INDUCT THEN
    REWRITE_TAC [BITVAL_CLAUSES] THEN WR)

  let maskTac : tactic :=
    REPEAT STRIP_TAC THEN REWRITE_TAC [WORD_MASK] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN WBR

  let WORD_AND_MASK ← prove
   r"(!p x. word_and (word_neg(word(bitval p))) x =
          if p then x else word 0) /\
   (!p x. word_and x (word_neg(word(bitval p))) =
          if p then x else word 0)"
   maskTac

  let WORD_OR_MASK ← prove
   r"(!p x. word_or (word_neg(word(bitval p))) x =
          if p then word_neg(word(bitval p)) else x) /\
   (!p x. word_or x (word_neg(word(bitval p))) =
          if p then word_neg(word(bitval p)) else x)"
   maskTac

  let WORD_XOR_MASK ← prove
   r"(!p x. word_xor (word_neg(word(bitval p))) x =
          if p then word_not x else x) /\
   (!p x. word_xor x (word_neg(word(bitval p))) =
          if p then word_not x else x)"
   maskTac

  let WORD_NEG_AND_MASK ← prove
   r"(!b x. word_neg (word_and (word_neg(word(bitval b))) x) =
          word_and (word_neg(word(bitval b))) (word_neg x)) /\
   (!b x. word_neg (word_and x (word_neg(word(bitval b)))) =
          word_and (word_neg x) (word_neg(word(bitval b))))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [WORD_AND_MASK] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [WORD_NEG_0])

  let boolTac (ths : List thm) : tactic :=
    REPEAT (MATCH_MP_TAC bool_INDUCT THEN CONJ_TAC) THEN REWRITE_TAC ths

  let WORD_AND_MASKS ← prove
   r"!p q. word_and (word_neg(word(bitval p))) (word_neg(word(bitval q))) =
         word_neg(word(bitval(p /\ q)))"
   (boolTac [BITVAL_CLAUSES, WORD_NEG_0, WORD_AND_0, WORD_AND_REFL])

  let WORD_OR_MASKS ← prove
   r"!p q. word_or (word_neg(word(bitval p))) (word_neg(word(bitval q))) =
         word_neg(word(bitval(p \/ q)))"
   (boolTac [BITVAL_CLAUSES, WORD_NEG_0, WORD_OR_0, WORD_OR_REFL])

  let WORD_XOR_MASKS ← prove
   r"!p q. word_xor (word_neg(word(bitval p))) (word_neg(word(bitval q))) =
         word_neg(word(bitval(~(p <=> q))))"
   (boolTac [BITVAL_CLAUSES, WORD_NEG_0, WORD_XOR_0, WORD_XOR_REFL])

  let WORD_AND_CONDITIONS ← prove
   r"!p q. word_and (word(bitval p)) (word(bitval q)) =
         word(bitval(p /\ q))"
   (boolTac [BITVAL_CLAUSES, WORD_NEG_0, WORD_AND_0, WORD_AND_REFL])

  let WORD_OR_CONDITIONS ← prove
   r"!p q. word_or (word(bitval p)) (word(bitval q)) =
         word(bitval(p \/ q))"
   (boolTac [BITVAL_CLAUSES, WORD_NEG_0, WORD_OR_0, WORD_OR_REFL])

  let WORD_XOR_CONDITIONS ← prove
   r"!p q. word_xor (word(bitval p)) (word(bitval q)) =
         word(bitval(~(p <=> q)))"
   (boolTac [BITVAL_CLAUSES, WORD_NEG_0, WORD_XOR_0, WORD_XOR_REFL])

  let VAL_WORD_MASK ← prove
   r"!b. val(word_neg(word(bitval b):N word)) =
       (2 EXP dimindex(:N) - 1) * bitval b"
   (GEN_TAC THEN
    REWRITE_TAC [VAL_WORD_NEG_CASES, VAL_WORD_BITVAL, BITVAL_EQ_0] THEN
    REWRITE_TAC [COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [BITVAL_CLAUSES] THEN
    ARITH_TAC)

  let IVAL_WORD_MASK ← prove
   r"!b. ival(word_neg(word(bitval b):N word)) = --(&(bitval b))"
   (GEN_TAC THEN REWRITE_TAC [WORD_IWORD, ← GSYM IWORD_INT_NEG] THEN
    MATCH_MP_TAC IVAL_IWORD THEN MATCH_MP_TAC (← INT_ARITH
     (← q r"&0:int <= x /\ x <= &1 /\ &2 pow 0 <= e ==> --e <= --x /\ --x < e")) THEN
    REWRITE_TAC [INT_OF_NUM_LE, LE_0, BITVAL_BOUND] THEN
    MATCH_MP_TAC INT_POW_MONO THEN REWRITE_TAC [INT_OF_NUM_LE] THEN ARITH_TAC)

  let INT_VAL_WORD_MASK ← prove
   r"!b. &(val(word_neg(word(bitval b):N word))):int =
       (&2 pow dimindex(:N) - &1) * &(bitval b)"
   (GEN_TAC THEN
    REWRITE_TAC [INT_VAL_WORD_NEG_CASES, VAL_WORD_BITVAL, BITVAL_EQ_0,
                 INT_OF_NUM_EQ, COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [BITVAL_CLAUSES] THEN
    INT_ARITH_TAC)

  let REAL_VAL_WORD_MASK ← prove
   r"!b. &(val(word_neg(word(bitval b):N word))):real =
       (&2 pow dimindex(:N) - &1) * &(bitval b)"
   (GEN_TAC THEN
    REWRITE_TAC [REAL_VAL_WORD_NEG_CASES, VAL_WORD_BITVAL, BITVAL_EQ_0,
                 REAL_OF_NUM_EQ, COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [BITVAL_CLAUSES] THEN
    REAL_ARITH_TAC)

  let WORD_MUL_EXPAND_ALT ← prove
   r"!x y:N word.
        word_mul x y =
        word(nsum {i | i < dimindex(:N)}
                  (\i. val(word_and (word_neg(word(bitval(bit i x))))
                                    (word_shl y i))))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [WORD_MUL_EXPAND] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC NSUM_EQ THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [WORD_AND_MASK] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [BITVAL_CLAUSES, MULT_CLAUSES, WORD_VAL, VAL_WORD_0])

  let WORD_SX_ZX_GEN ← prove
   r"!x. (word_sx:M word->N word) x =
       word_or (word_shl (word_neg(word(bitval(bit (dimindex(:M)-1) x))))
                         (dimindex(:M)))
               (word_zx x)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"dimindex(:N) <= dimindex(:M)") THEN
    ASM_SIMP_TAC [WORD_SX_ZX, WORD_SHL_TRIVIAL, WORD_OR_0] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [NOT_LE]) THEN
    ASM_SIMP_TAC [← GSYM IVAL_CONG, IVAL_WORD_SX, LT_IMP_LE] THEN
    REWRITE_TAC [IVAL_VAL, ← INTEGER_RULE
     (← q r"(x:int == y - p * z) (mod p) <=> (x == y) (mod p)")] THEN
    W (MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_OR_DISJOINT o
       rand o rand o rator o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_AND, BIT_WORD_SHL, BIT_WORD_ZX,
                   BIT_WORD_MASK, BIT_WORD_0] THEN
      ONCE_REWRITE_TAC [BIT_GUARD] THEN ARITH_TAC,
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC [VAL_WORD_ZX, LT_IMP_LE] THEN
    REWRITE_TAC [VAL_WORD_SHL, ← GSYM INT_OF_NUM_CLAUSES,
                 ← GSYM INT_OF_NUM_REM, INT_VAL_WORD_MASK] THEN
    REWRITE_TAC [← GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    REWRITE_TAC [INT_REM_EQ] THEN CONV_TAC (fun t => (INTEGER_RULE t).run))

  -- Two ARITH_RULEs in one THEN chain: the later one is evaluated first.
  let _ar2 ← ARITH_RULE (← q r"n - 1 < n <=> ~(n = 0)")
  let _ar1 ← ARITH_RULE
    (← q r"~(n = 0) ==> MIN i (n - 1) = if i < n then i else n - 1")
  let BIT_WORD_SX ← prove
   r"!x i. bit i ((word_sx:M word->N word) x) <=>
         i < dimindex(:N) /\ bit (MIN i (dimindex(:M) - 1)) x"
   (REPEAT GEN_TAC THEN SIMP_TAC [DIMINDEX_NONZERO, _ar1] THEN
    REWRITE_TAC [WORD_SX_ZX_GEN, BIT_WORD_OR, BIT_WORD_SHL,
                 BIT_WORD_MASK, BIT_WORD_ZX] THEN
    ASM_CASES_TAC (← q r"i < dimindex(:N)") THEN ASM_REWRITE_TAC [] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [← GSYM NOT_LT] THEN
    ONCE_REWRITE_TAC [BIT_GUARD] THEN
    REWRITE_TAC [_ar2, DIMINDEX_NONZERO] THEN
    ASM_CASES_TAC (← q r"bit (dimindex(:M) - 1) (x:M word)") THEN
    ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC)

  let VAL_WORD_AND_MASK ← prove
   r"!(x:N word) k.
        val(word_and x (word_of_bits {i | i < k})) = val x MOD (2 EXP k)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [val_def] THEN
    SIMP_TAC [BINARY_DIGITSUM_MOD, FINITE_NUMSEG_LT, NSUM_RESTRICT_SET] THEN
    MATCH_MP_TAC NSUM_EQ THEN
    REWRITE_TAC [IN_ELIM_THM, BIT_WORD_AND, IN_ELIM_THM, BIT_WORD_OF_BITS] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [bitval] THEN ARITH_TAC)

  let IVAL_WORD_AND_MASK ← prove
   r"!(x:N word) k.
        k < dimindex(:N)
        ==> ival(word_and x (word_of_bits {i | i < k})) =
            ival x rem (&2 pow k)"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [INT_REM_IVAL, LT_IMP_LE] THEN
    REWRITE_TAC [← GSYM VAL_WORD_AND_MASK, ival] THEN
    MATCH_MP_TAC (← MESON [] (← q r"p ==> (if p then x else y) = x")) THEN
    REWRITE_TAC [VAL_WORD_AND_MASK] THEN TRANS_TAC LTE_TRANS (← q r"2 EXP k") THEN
    SIMP_TAC [DIVISION, EXP_EQ_0, ARITH_EQ, LE_EXP] THEN ASM_ARITH_TAC)

  let VAL_WORD_AND_MASK_WORD ← prove
   r"!x k. val(word_and x (word(2 EXP k - 1))) = val x MOD 2 EXP k"
   (REWRITE_TAC [← GSYM WORD_OF_BITS_MASK, VAL_WORD_AND_MASK])

  let WORD_AND_MASK_WORD ← prove
   r"(!(x:N word) k.
        word_and x (word(2 EXP k - 1)) = word(val x MOD 2 EXP k)) /\
   (!(x:N word) k.
        word_and (word(2 EXP k - 1)) x = word(val x MOD 2 EXP k))"
   (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [WORD_AND_SYM] THEN
    REWRITE_TAC [] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VAL_WORD_EQ THEN
    MATCH_MP_TAC (← ARITH_RULE (← q r"x MOD n <= x /\ x < e ==> x MOD n < e")) THEN
    REWRITE_TAC [MOD_LE, VAL_BOUND])

  let VAL_WORD_AND_NOT_MASK_WORD ← prove
   r"!(x:N word) k.
        val(word_and x (word_not(word(2 EXP k - 1)))) =
        2 EXP k * val x DIV 2 EXP k"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q "x:N word", ← q "k:num"] VAL_WORD_AND_MASK_WORD) THEN
    MATCH_MP_TAC (← ARITH_RULE (← q r"h + l:num = h' + l' ==> l = l' ==> h = h'")) THEN
    REWRITE_TAC [DIVISION_SIMP] THEN
    W (MP_TAC o PART_MATCH (rand o rand) VAL_WORD_OR_DISJOINT o lhand o snd) THEN
    ANTS_TAC THENL
     [WBR, DISCH_THEN (SUBST1_TAC o SYM)] THEN
    AP_TERM_TAC THEN WBR)

  let WORD_AND_NOT_MASK_WORD ← prove
   r"(!(x:N word) k.
        word_and x (word_not(word(2 EXP k - 1))) =
        word(2 EXP k * val x DIV 2 EXP k)) /\
   (!(x:N word) k.
        word_and (word_not(word(2 EXP k - 1))) x =
        word(2 EXP k * val x DIV 2 EXP k))"
   (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [WORD_AND_SYM] THEN
    REWRITE_TAC [] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_AND_NOT_MASK_WORD] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VAL_WORD_EQ THEN
    REWRITE_TAC [← GSYM VAL_WORD_AND_NOT_MASK_WORD, VAL_BOUND])

  let WORD_BITMASK ← prove
   r"!k. word_of_bits {i | i < k}:N word =
       word_sub (word_of_bits {k}) (word 1)"
   (REWRITE_TAC [WORD_OF_BITS_MASK, WORD_OF_BITS_SING_AS_WORD] THEN
    REWRITE_TAC [WORD_SUB, ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")] THEN
    REWRITE_TAC [EXP_EQ_0, ARITH_EQ])

  let MASK_WORD_SUB ← prove
   r"!k. word_sub (word(2 EXP k)) (word 1):N word = word(2 EXP k - 1)"
   (GEN_TAC THEN REWRITE_TAC [WORD_SUB] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")] THEN
    REWRITE_TAC [EXP_EQ_0, ARITH_EQ])

  let WORD_AND_MASK_WORDS ← prove
   r"!j k. word_and (word(2 EXP j - 1)) (word(2 EXP k - 1)):N word =
         word(2 EXP MIN j k - 1)"
   (SIMP_TAC [WORD_EQ_BITS_ALT, BIT_WORD_AND, BIT_MASK_WORD] THEN ARITH_TAC)

  let WORD_OR_MASK_WORDS ← prove
   r"!j k. word_or (word(2 EXP j - 1)) (word(2 EXP k - 1)):N word =
         word(2 EXP MAX j k - 1)"
   (SIMP_TAC [WORD_EQ_BITS_ALT, BIT_WORD_OR, BIT_MASK_WORD] THEN ARITH_TAC)

  let WORD_USHR_MASK_WORD ← prove
   r"!k i. k <= dimindex(:N)
         ==> word_ushr (word(2 EXP k - 1):N word) i = word(2 EXP (k - i) - 1)"
   (SIMP_TAC [WORD_EQ_BITS_ALT, BIT_WORD_USHR, BIT_MASK_WORD] THEN
    ARITH_TAC)

  -- @@RETURN BEGIN
  return { WORD_MASK_ALT, WORD_MASK, BIT_WORD_MASK, WORD_ISHR_MSB, WORD_NOT_MASK,
           WORD_AND_MASK, WORD_OR_MASK, WORD_XOR_MASK, WORD_NEG_AND_MASK, WORD_AND_MASKS,
           WORD_OR_MASKS, WORD_XOR_MASKS, WORD_AND_CONDITIONS, WORD_OR_CONDITIONS,
           WORD_XOR_CONDITIONS, VAL_WORD_MASK, IVAL_WORD_MASK, INT_VAL_WORD_MASK,
           REAL_VAL_WORD_MASK, WORD_MUL_EXPAND_ALT, WORD_SX_ZX_GEN, BIT_WORD_SX,
           VAL_WORD_AND_MASK, IVAL_WORD_AND_MASK, VAL_WORD_AND_MASK_WORD,
           WORD_AND_MASK_WORD, VAL_WORD_AND_NOT_MASK_WORD, WORD_AND_NOT_MASK_WORD,
           WORD_BITMASK, MASK_WORD_SUB, WORD_AND_MASK_WORDS, WORD_OR_MASK_WORDS,
           WORD_USHR_MASK_WORD }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Trailing and leading zero count (returning word size for zero input).     -/
/- ------------------------------------------------------------------------- -/

structure ClzCtz where
  -- @@FIELDS
  word_ctz : thm
  word_clz : thm
  WORD_CLZ : thm
  WORD_CTZ_0 : thm
  WORD_LE_CTZ : thm
  WORD_CTZ_LE : thm
  WORD_CTZ_LE_DIMINDEX : thm
  WORD_CTZ_LBOUND : thm
  WORD_CTZ_EQ_DIMINDEX : thm
  WORD_CTZ_LT_DIMINDEX : thm
  WORD_CTZ_EQ_0 : thm
  WORD_CTZ_UNIQUE_GEN : thm
  WORD_CTZ_UNIQUE : thm
  WORD_LE_CTZ_VAL_MOD : thm
  WORD_LE_CTZ_VAL : thm
  WORD_CTZ_UNIQUE_VAL : thm
  WORD_CLZ_0 : thm
  WORD_SIZE_SUB_CLZ : thm
  WORD_CLZ_LE_DIMINDEX : thm
  WORD_LE_CLZ : thm
  WORD_CLZ_LE : thm
  WORD_CLZ_LBOUND_ALT : thm
  WORD_CLZ_LBOUND : thm
  WORD_CLZ_EQ_DIMINDEX : thm
  WORD_CLZ_LT_DIMINDEX : thm
  WORD_CLZ_EQ_0 : thm
  WORD_CLZ_DECOMP : thm
  WORD_CLZ_UNIQUE_GEN : thm
  WORD_CLZ_UNIQUE : thm
  WORD_LE_CLZ_VAL : thm
  WORD_LE_CLZ_VAL_MULT : thm
  WORD_LE_CLZ_VAL_DIV : thm
  VAL_BOUND_CLZ : thm
  WORD_CLZ_UNIQUE_VAL : thm
  WORD_CTZ_BIT : thm
  WORD_CLZ_BIT : thm
  WORD_CTZ_MASK_WORD : thm
  WORD_CLZ_MASK_WORD : thm
  WORD_AND_NEG_CTZ : thm
  WORD_XOR_SUB_1_CTZ : thm
  WORD_AND_NOT_SUB_1_CTZ : thm
  WORD_CTZ_EMULATION_REV : thm
  WORD_CTZ_EMULATION_AND_NEG_REV : thm
  WORD_CTZ_EMULATION_XOR_SUB_1_REV : thm
  WORD_CTZ_EMULATION : thm
  WORD_CTZ_EMULATION_AND_NEG : thm
  WORD_CTZ_EMULATION_XOR_SUB_1 : thm
  WORD_CLZ_IMP : thm
  WORD_CLZ_OR : thm
  WORD_CTZ_IMP : thm
  WORD_CTZ_OR : thm
  WORD_CLZ_MONO : thm
  WORD_CTZ_EMULATION_POPCOUNT : thm
  deriving Inhabited

@[nospecialize]
def setupClzCtz [HolBase] (D : WordsDeps) (BBitval : Bitval) (BWordType : WordType) (BBitsOfWord : BitsOfWord) (BVal : Val) (BPopcount : Popcount) (BWordOps1 : WordOps1) (BWordOps3 : WordOps3) (BWordRule : WordRule) (BMisc1 : Misc1) (BMasks : Masks) :
    ExceptT String IO ClzCtz := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC,
        NUM_REDUCE_CONV, SET_TAC, new_definition, .. } := D
  let { ADD_CLAUSES, ADD_SYM, ARITH, ARITH_EQ, CARD_NUMSEG_LT, COND_SWAP, CONJ_ASSOC,
        CONTRAPOS_THM, DE_MORGAN_THM, DIMINDEX_GE_1, DIV_DIV, DIV_EQ_0, EQ_TRANS,
        EXP_ADD, EXP_EQ_0, EXP_LT_0, EXTENSION, .. } := D.core1
  let { FINITE_NUMSEG_LT, FINITE_SUBSET, FORALL_AND_THM, FORALL_IN_GSPEC, FUN_EQ_THM,
        IN_ELIM_THM, IN_SING, .. } := D.core2
  let { LE, LE_1, LE_ANTISYM, LE_CASES, LE_EXISTS, LE_EXP, LE_MINIMAL, LE_MULT_LCANCEL,
        LE_REFL, LE_SUC_LT, LE_TRANS, LT, LTE_TRANS, LT_EXP, LT_IMP_LE, LT_LE,
        LT_MULT_LCANCEL, LT_REFL, LT_TRANS, MINIMAL, MINIMAL_LE, MINIMAL_UBOUND,
        MINIMAL_UNIQUE, MOD_EQ_0, MOD_LE, MOD_MOD, MOD_REFL, MONO_FORALL, MULT_CLAUSES,
        MULT_EQ_0, MULT_SYM, NOT_FORALL_THM, NOT_IMP, NOT_LE, NOT_LT, NSUM_EQ_0_IFF,
        ODD, .. } := D.core3
  let { SUB_0, SUB_ADD, UNWIND_THM2, divides, .. } := D.core4
  let { BITVAL_EQ_0, .. } := BBitval
  let { BIT_GUARD, BIT_TRIVIAL, WORD_EQ_BITS, WORD_EQ_BITS_ALT, .. } := BWordType
  let { BIT_WORD_OF_BITS, bits_of_word, .. } := BBitsOfWord
  let { BIT_MASK_WORD, BIT_VAL, BIT_VAL_MOD, BIT_WORD_0, VAL_BOUND, VAL_DIV, VAL_EQ_0,
        VAL_MOD, VAL_WORD_0, .. } := BVal
  let { WORD_POPCOUNT_0, word_popcount, .. } := BPopcount
  let { BIT_WORD_AND, BIT_WORD_OR_ALT, WORD_POPCOUNT_NOT, .. } := BWordOps1
  let { BIT_WORD_USHR, WORD_USHR_EQ_0, .. } := BWordOps3
  let { WORD_RULE, .. } := BWordRule
  let { BIT_WORD_AND_NEG, BIT_WORD_AND_NOT_SUB_1, BIT_WORD_XOR_SUB_1, WORD_AND_REFL, .. } := BMisc1
  let { VAL_WORD_AND_MASK, .. } := BMasks
  -- @@SCOPE END
  let word_ctz ← new_definition
   r"word_ctz (a:N word) =
        if a = word 0 then dimindex(:N) else minimal i. bit i a"

  let word_clz ← new_definition
   r"word_clz (a:N word) = dimindex(:N) - minimal m. !i. m <= i ==> ~bit i a"

  let WORD_CLZ ← prove
   r"!x:N word. word_clz x = dimindex (:N) - (minimal m. val x < 2 EXP m)"
   (GEN_TAC THEN REWRITE_TAC [word_clz] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN
    X_GEN_TAC (← q "m:num") THEN REWRITE_TAC [] THEN
    SIMP_TAC [← GSYM WORD_USHR_EQ_0, WORD_EQ_BITS, BIT_WORD_USHR, BIT_WORD_0] THEN
    MESON_TAC [LE_EXISTS, ADD_SYM])

  let WORD_CTZ_0 ← prove
   r"word_ctz(word 0:N word) = dimindex(:N)"
   (REWRITE_TAC [word_ctz])

  let WORD_LE_CTZ ← prove
   r"!(a:N word) n.
        n <= word_ctz a <=> n <= dimindex(:N) /\ !i. bit i a ==> n <= i"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_ctz] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [BIT_WORD_0] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [WORD_EQ_BITS_ALT, BIT_WORD_0]) THEN
    W (MP_TAC o PART_MATCH (lhand o rand) LE_MINIMAL o lhand o snd) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN
    ASM_MESON_TAC [NOT_LE, LE_CASES, LE_TRANS])

  let _a2 ← ARITH_RULE (← q r"SUC n <= m <=> ~(m <= n)")
  let _a1 ← ARITH_RULE (← q r"m <= n <=> ~(SUC n <= m)")
  let WORD_CTZ_LE ← prove
   r"!(a:N word) n.
        word_ctz a <= n <=> n < dimindex(:N) ==> ?i. i <= n /\ bit i a"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [_a1] THEN
    REWRITE_TAC [WORD_LE_CTZ, DE_MORGAN_THM] THEN
    REWRITE_TAC [_a2] THEN
    MESON_TAC [NOT_LT])

  let WORD_CTZ_LE_DIMINDEX ← prove
   r"!a:N word. word_ctz(a) <= dimindex(:N)"
   (REWRITE_TAC [WORD_CTZ_LE, LT_REFL])

  let WORD_CTZ_LBOUND ← prove
   r"!(a:N word) i. bit i a ==> word_ctz(a) <= i"
   (REWRITE_TAC [WORD_CTZ_LE] THEN MESON_TAC [LE_REFL])

  let WORD_CTZ_EQ_DIMINDEX ← prove
   r"!a:N word. word_ctz a = dimindex(:N) <=> a = word 0"
   (REWRITE_TAC [← GSYM LE_ANTISYM, WORD_CTZ_LE_DIMINDEX, WORD_LE_CTZ] THEN
    REWRITE_TAC [LE_REFL, WORD_EQ_BITS_ALT, BIT_WORD_0] THEN MESON_TAC [NOT_LE])

  let WORD_CTZ_LT_DIMINDEX ← prove
   r"!a:N word. word_ctz a < dimindex(:N) <=> ~(a = word 0)"
   (REWRITE_TAC [LT_LE, WORD_CTZ_LE_DIMINDEX, WORD_CTZ_EQ_DIMINDEX])

  let WORD_CTZ_EQ_0 ← prove
   r"!a:N word. word_ctz a = 0 <=> bit 0 a"
   (REWRITE_TAC [← GSYM (← CONJUNCT1 LE)] THEN
    REWRITE_TAC [WORD_CTZ_LE, ← CONJUNCT1 LE, UNWIND_THM2] THEN
    SIMP_TAC [DIMINDEX_GE_1, LE_1])

  let WORD_CTZ_UNIQUE_GEN ← prove
   r"!(a:N word) n.
        word_ctz a = n <=>
        n <= dimindex(:N) /\
        (n < dimindex(:N) ==> bit n a) /\
        (!i. i < n ==> ~bit i a)"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM LE_ANTISYM] THEN
    REWRITE_TAC [WORD_CTZ_LE, WORD_LE_CTZ] THEN
    ASM_CASES_TAC (← q r"n <= dimindex(:N)") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [NOT_LT, ← MESON [] (← q r"p ==> ~bit a b <=> bit a b ==> ~p")] THEN
    ASM_CASES_TAC (← q r"n < dimindex(:N)") THEN ASM_REWRITE_TAC [] THEN
    MESON_TAC [LE_ANTISYM])

  let WORD_CTZ_UNIQUE ← prove
   r"!(a:N word) n.
        n < dimindex(:N)
        ==> (word_ctz a = n <=> bit n a /\ !i. i < n ==> ~bit i a)"
   (SIMP_TAC [WORD_CTZ_UNIQUE_GEN, LT_IMP_LE])

  let WORD_LE_CTZ_VAL_MOD ← prove
   r"!(a:N word) n.
        n <= word_ctz a <=>
        n <= dimindex(:N) /\ val a MOD 2 EXP n = 0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [WORD_LE_CTZ] THEN
    ASM_CASES_TAC (← q r"n <= dimindex(:N)") THEN ASM_REWRITE_TAC [] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [VAL_MOD, NOT_LE] THEN
    SIMP_TAC [NSUM_EQ_0_IFF, FINITE_NUMSEG_LT, IN_ELIM_THM] THEN
    REWRITE_TAC [MULT_EQ_0, EXP_EQ_0, ARITH_EQ, BITVAL_EQ_0])

  let WORD_LE_CTZ_VAL ← prove
   r"!(a:N word) n.
        n <= word_ctz a <=>
        n <= dimindex(:N) /\ 2 EXP n divides val a"
   (REWRITE_TAC [WORD_LE_CTZ_VAL_MOD] THEN
    MESON_TAC [divides, MOD_EQ_0, MULT_SYM])

  let WORD_CTZ_UNIQUE_VAL ← prove
   r"!(a:N word) n.
        val a MOD (2 EXP (n + 1)) = 2 EXP n
        ==> word_ctz a = n"
   (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o SPEC (← q r"dimindex(:N)") o MATCH_MP
     (← ARITH_RULE (← q r"a MOD p = n
                ==> !e. a MOD p <= a ==> a < 2 EXP e ==> n < 2 EXP e"))) THEN
    REWRITE_TAC [VAL_BOUND, MOD_LE, LT_EXP, ARITH] THEN
    DISCH_TAC THEN ASM_SIMP_TAC [WORD_CTZ_UNIQUE] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC [BIT_VAL_MOD, LE_REFL], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o AP_TERM (← q r"\x. x MOD (2 EXP n)")) THEN
    REWRITE_TAC [EXP_ADD, MOD_MOD, MOD_REFL] THEN
    REWRITE_TAC [← GSYM VAL_WORD_AND_MASK] THEN
    REWRITE_TAC [VAL_EQ_0, WORD_EQ_BITS, BIT_WORD_0] THEN
    REWRITE_TAC [BIT_WORD_AND, BIT_WORD_OF_BITS, IN_ELIM_THM] THEN
    ASM_MESON_TAC [LT_TRANS])

  let WORD_CLZ_0 ← prove
   r"word_clz(word 0:N word) = dimindex(:N)"
   (REWRITE_TAC [word_clz, BIT_WORD_0] THEN
    MATCH_MP_TAC (← ARITH_RULE (← q r"d = 0 ==> m - d = m")) THEN
    MATCH_MP_TAC MINIMAL_UNIQUE THEN REWRITE_TAC [LT])

  let WORD_SIZE_SUB_CLZ ← prove
   r"!(a:N word).
        dimindex(:N) - word_clz(a) = (minimal m. !i. m <= i ==> ~bit i a)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_clz] THEN
    MATCH_MP_TAC (← ARITH_RULE (← q r"m:num <= n ==> n - (n - m) = m")) THEN
    MATCH_MP_TAC MINIMAL_UBOUND THEN MESON_TAC [BIT_TRIVIAL])

  let WORD_CLZ_LE_DIMINDEX ← prove
   r"!a:N word. word_clz(a) <= dimindex(:N)"
   (REWRITE_TAC [word_clz] THEN ARITH_TAC)

  let _a3 ← ARITH_RULE (← q r"n:num <= d ==> (i < d - n <=> i + n < d)")
  let _m2 ← MESON [LE_REFL, LTE_TRANS]
    (← q r"(?m:num. m <= n /\ !i. P i ==> i < m) <=> (!i. P i ==> i < n)")
  let _t1 ← TAUT (← q r"p ==> ~q <=> q ==> ~p")
  let WORD_LE_CLZ ← prove
   r"!(a:N word) n.
        n <= word_clz(a) <=>
        n <= dimindex(:N) /\ !i. bit i a ==> i + n < dimindex(:N)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n <= dimindex(:N)") THENL
     [ASM_REWRITE_TAC [], ASM_MESON_TAC [WORD_CLZ_LE_DIMINDEX, LE_TRANS]] THEN
    TRANS_TAC EQ_TRANS
     (← q r"dimindex(:N) - word_clz(a:N word) <= dimindex(:N) - n") THEN
    CONJ_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC [WORD_SIZE_SUB_CLZ]] THEN
    W (MP_TAC o PART_MATCH (lhand o rand) MINIMAL_LE o lhand o snd) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [MESON_TAC [BIT_TRIVIAL], DISCH_THEN SUBST1_TAC] THEN
    ONCE_REWRITE_TAC [_t1] THEN
    REWRITE_TAC [NOT_LE, _m2] THEN
    ASM_SIMP_TAC [_a3])

  let _b2 ← ARITH_RULE (← q r"i + SUC n = i + n + 1")
  let _b1 ← ARITH_RULE (← q r"m <= n <=> ~(SUC n <= m)")
  let WORD_CLZ_LE ← prove
   r"!(a:N word) n.
        word_clz(a) <= n <=>
        n < dimindex(:N) ==> ?i. dimindex(:N) <= i + n + 1 /\ bit i a"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [_b1] THEN
    REWRITE_TAC [WORD_LE_CLZ, DE_MORGAN_THM] THEN REWRITE_TAC [LE_SUC_LT] THEN
    ASM_CASES_TAC (← q r"n < dimindex(:N)") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, NOT_LT] THEN
    MESON_TAC [_b2])

  let WORD_CLZ_LBOUND_ALT ← prove
   r"!(a:N word) i. bit i a ==> word_clz(a) + i < dimindex(:N)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC (← ARITH_RULE
     (← q r"~(n <= i) /\ c <= (n - 1) - i ==> c + i < n")) THEN
    CONJ_TAC THENL [ASM_MESON_TAC [BIT_TRIVIAL], ALL_TAC] THEN
    REWRITE_TAC [WORD_CLZ_LE] THEN REPEAT STRIP_TAC THEN EXISTS_TAC (← q "i:num") THEN
    ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC)

  let WORD_CLZ_LBOUND ← prove
   r"!(a:N word) i. bit i a ==> word_clz(a) < dimindex(:N) - i"
   (MESON_TAC [WORD_CLZ_LBOUND_ALT, ← ARITH_RULE (← q r"a + i:num < n ==> a < n - i")])

  let WORD_CLZ_EQ_DIMINDEX ← prove
   r"!a:N word. word_clz a = dimindex(:N) <=> a = word 0"
   (REWRITE_TAC [← GSYM LE_ANTISYM, WORD_CLZ_LE_DIMINDEX, WORD_LE_CLZ] THEN
    REWRITE_TAC [LE_REFL, ← ARITH_RULE (← q r"~(i + n:num < n)")] THEN
    REWRITE_TAC [WORD_EQ_BITS, BIT_WORD_0])

  let WORD_CLZ_LT_DIMINDEX ← prove
   r"!a:N word. word_clz a < dimindex(:N) <=> ~(a = word 0)"
   (REWRITE_TAC [LT_LE, WORD_CLZ_LE_DIMINDEX, WORD_CLZ_EQ_DIMINDEX])

  let _c2 ← ARITH_RULE (← q r"n <= i + 1 /\ ~(n <= i) <=> i = n - 1 /\ 1 <= n")
  let _c1 ← MESON [BIT_TRIVIAL]
    (← q r"bit i (a:N word) <=> ~(dimindex(:N) <= i) /\ bit i a")
  let WORD_CLZ_EQ_0 ← prove
   r"!a:N word. word_clz a = 0 <=> bit (dimindex(:N) - 1) a"
   (REWRITE_TAC [← GSYM (← CONJUNCT1 LE)] THEN
    REWRITE_TAC [WORD_CLZ_LE, ← CONJUNCT1 LE, UNWIND_THM2] THEN
    GEN_TAC THEN SIMP_TAC [DIMINDEX_GE_1, LE_1, ADD_CLAUSES] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [_c1] THEN
    REWRITE_TAC [CONJ_ASSOC, DIMINDEX_GE_1, UNWIND_THM2, _c2])

  let WORD_CLZ_DECOMP ← prove
   r"!a:N word.
        word_clz(a) + (minimal m. !i. m <= i ==> ~bit i a) = dimindex(:N)"
   (GEN_TAC THEN REWRITE_TAC [word_clz] THEN
    MATCH_MP_TAC SUB_ADD THEN MATCH_MP_TAC MINIMAL_UBOUND THEN
    MESON_TAC [BIT_TRIVIAL])

  -- Built as the tactic is: the THEN chain right to left; the MESON inside
  -- `fun th ->` runs only when the tactic is applied.
  let _d4 ← ARITH_RULE
    (← q r"N <= i + n + 1 /\ i + n < N <=> 1 <= N /\ n < N /\ i = N - n - 1")
  let _d3 ← TAUT (← q r"(r ==> (p <=> q)) ==> (p /\ r <=> q /\ r)")
  let _d2 ← ARITH_RULE (← q r"n:num <= N ==> (~(N - n <= i) <=> i + n < N)")
  let _d1 ← MESON [] (← q r"p ==> ~bit a b <=> bit a b ==> ~p")
  let _dtm ← q r"(!i. bit i a ==> P i)
             ==> (!i. bit i a <=> P i /\ bit i a)"
  let WORD_CLZ_UNIQUE_GEN ← prove
   r"!(a:N word) n.
        word_clz a = n <=>
        n <= dimindex(:N) /\
        (n < dimindex(:N) ==> bit (dimindex(:N) - n - 1) a) /\
        (!i. dimindex(:N) - n <= i ==> ~bit i a)"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM LE_ANTISYM] THEN
    REWRITE_TAC [WORD_CLZ_LE, WORD_LE_CLZ] THEN
    ASM_CASES_TAC (← q r"n <= dimindex(:N)") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [NOT_LT, _d1] THEN
    ASM_SIMP_TAC [_d2] THEN
    ASM_CASES_TAC (← q r"n < dimindex(:N)") THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC _d3 THEN
    DISCH_THEN (fun th => tactic_of do
      pure (ONCE_REWRITE_TAC [← MATCH_MP (← MESON [] _dtm) th])) THEN
    ASM_REWRITE_TAC [CONJ_ASSOC, DIMINDEX_GE_1, UNWIND_THM2, _d4] THEN
    EQ_TAC THEN SIMP_TAC [] THEN ASM_ARITH_TAC)

  let WORD_CLZ_UNIQUE ← prove
   r"!(a:N word) n.
        n < dimindex(:N)
        ==> (word_clz a = n <=>
             bit (dimindex(:N) - n - 1) a /\
             !i. dimindex(:N) - n <= i ==> ~bit i a)"
   (SIMP_TAC [WORD_CLZ_UNIQUE_GEN, LT_IMP_LE])

  let WORD_LE_CLZ_VAL ← prove
   r"!(a:N word) n.
        n <= word_clz a <=>
        n <= dimindex(:N) /\ val a < 2 EXP (dimindex(:N) - n)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [WORD_LE_CLZ] THEN
    ASM_CASES_TAC (← q r"n <= dimindex(:N)") THEN ASM_REWRITE_TAC [] THEN
    TRANS_TAC EQ_TRANS (← q r"val(a:N word) DIV 2 EXP (dimindex(:N) - n) = 0") THEN
    CONJ_TAC THENL [ALL_TAC, SIMP_TAC [DIV_EQ_0, EXP_EQ_0, ARITH_EQ]] THEN
    REWRITE_TAC [VAL_DIV] THEN
    W (MP_TAC o PART_MATCH (lhand o rand) NSUM_EQ_0_IFF o rand o snd) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{i | i < dimindex(:N)}") THEN
      REWRITE_TAC [FINITE_NUMSEG_LT] THEN SET_TAC [],
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC [FORALL_IN_GSPEC, MULT_EQ_0, EXP_EQ_0, ARITH_EQ, BITVAL_EQ_0] THEN
    ASSUME_TAC (← SPEC (← q "a:N word") BIT_TRIVIAL) THEN
    EQ_TAC THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q "i:num") THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q "i:num")) THEN
    ASM_CASES_TAC (← q "bit i (a:N word)") THEN ASM_REWRITE_TAC [] THEN
    ASM_ARITH_TAC)

  let WORD_LE_CLZ_VAL_MULT ← prove
   r"!(a:N word) n.
        n <= word_clz a <=>
        n <= dimindex(:N) /\ 2 EXP n * val a < 2 EXP dimindex(:N)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [WORD_LE_CLZ_VAL] THEN
    ASM_CASES_TAC (← q r"n <= dimindex(:N)") THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"2 EXP dimindex(:N) = 2 EXP n * 2 EXP (dimindex(:N) - n)")
    SUBST1_TAC THENL
     [REWRITE_TAC [← GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC,
      REWRITE_TAC [LT_MULT_LCANCEL, EXP_EQ_0, ARITH_EQ]])

  let WORD_LE_CLZ_VAL_DIV ← prove
   r"!(a:N word) n.
        n <= word_clz a <=>
        n <= dimindex(:N) /\ val a DIV (2 EXP (dimindex(:N) - n)) = 0"
   (SIMP_TAC [DIV_EQ_0, EXP_EQ_0, ARITH_EQ, WORD_LE_CLZ_VAL])

  let VAL_BOUND_CLZ ← prove
   r"!(a:N word) n.
        2 EXP n * val a < 2 EXP dimindex(:N) <=>
        a = word 0 \/ n <= word_clz a"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"a:N word = word 0") THEN
    ASM_REWRITE_TAC [VAL_WORD_0, MULT_CLAUSES, EXP_LT_0, EXP_EQ_0, ARITH_EQ] THEN
    REWRITE_TAC [WORD_LE_CLZ_VAL_MULT] THEN
    REWRITE_TAC [← TAUT (← q r"(p <=> q /\ p) <=> p ==> q")] THEN
    DISCH_THEN (MP_TAC o MATCH_MP (← ARITH_RULE
     (← q r"n * a < N ==> n * 1 <= n * a ==> n <= N"))) THEN
    REWRITE_TAC [LE_EXP, ARITH_EQ, EXP_EQ_0, LE_MULT_LCANCEL] THEN
    ASM_SIMP_TAC [LE_1, VAL_EQ_0])

  let _e2 ← ARITH_RULE (← q r"1 = 2 EXP 0")
  let _e1 ← MESON [ODD] (← q r"n = 0 ==> ~ODD n")
  let WORD_CLZ_UNIQUE_VAL ← prove
   r"!(a:N word) n.
        n < dimindex(:N) /\
        val a DIV (2 EXP (dimindex(:N) - n - 1)) = 1
        ==> word_clz a = n"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [WORD_CLZ_UNIQUE] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC [BIT_VAL, ARITH], ALL_TAC] THEN
    X_GEN_TAC (← q "i:num") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"i = (dimindex (:N) - n - 1) + SUC(i - (dimindex(:N) - n))")
    SUBST1_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    ASM_SIMP_TAC [BIT_VAL, EXP_ADD, ← GSYM DIV_DIV] THEN
    MATCH_MP_TAC _e1 THEN
    SIMP_TAC [DIV_EQ_0, ARITH_EQ, EXP_EQ_0] THEN
    GEN_REWRITE_TAC LAND_CONV [_e2] THEN
    REWRITE_TAC [LT_EXP] THEN ARITH_TAC)

  let WORD_CTZ_BIT ← prove
   r"!k. word_ctz (word_of_bits {k}:N word) = MIN k (dimindex(:N))"
   (GEN_TAC THEN REWRITE_TAC [WORD_CTZ_UNIQUE_GEN, BIT_WORD_OF_BITS, IN_SING] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"MIN k n = if k < n then k else n")] THEN
    ASM_MESON_TAC [LT_IMP_LE, LT_REFL, LE_REFL])

  let WORD_CLZ_BIT ← prove
   r"!k. word_clz (word_of_bits {k}:N word) =
       if k < dimindex(:N) then dimindex(:N) - 1 - k else dimindex(:N)"
   (GEN_TAC THEN REWRITE_TAC [WORD_CLZ_UNIQUE_GEN, BIT_WORD_OF_BITS, IN_SING] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC)

  let WORD_CTZ_MASK_WORD ← prove
   r"!k. word_ctz (word(2 EXP k - 1):N word) = if k = 0 then dimindex(:N) else 0"
   (GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [WORD_CTZ_0, WORD_CTZ_EQ_0] THEN
    ASM_SIMP_TAC [BIT_MASK_WORD, DIMINDEX_GE_1, LE_1])

  let WORD_CLZ_MASK_WORD ← prove
   r"!k. word_clz (word(2 EXP k - 1):N word) = dimindex(:N) - k"
   (REWRITE_TAC [WORD_CLZ_UNIQUE_GEN, BIT_MASK_WORD] THEN ASM_ARITH_TAC)

  let WORD_AND_NEG_CTZ ← prove
   r"!x:N word. word_and x (word_neg x) = word_of_bits {word_ctz x}"
   (GEN_TAC THEN REWRITE_TAC [WORD_EQ_BITS_ALT] THEN
    REWRITE_TAC [BIT_WORD_AND_NEG, BIT_WORD_OF_BITS, IN_SING] THEN
    MESON_TAC [WORD_CTZ_UNIQUE_GEN, LT_IMP_LE])

  let WORD_XOR_SUB_1_CTZ ← prove
   r"!x:N word.
        word_xor x (word_sub x (word 1)) =
        word(2 EXP (word_ctz x + 1) - 1)"
   (REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_XOR_SUB_1, BIT_MASK_WORD] THEN
    SIMP_TAC [WORD_LE_CTZ, ← ARITH_RULE (← q r"a < b + 1 <=> a <= b")] THEN
    MESON_TAC [LT_IMP_LE, NOT_LT])

  let WORD_AND_NOT_SUB_1_CTZ ← prove
   r"!x:N word.
        word_and (word_not x) (word_sub x (word 1)) =
        word(2 EXP word_ctz x - 1)"
   (SIMP_TAC [WORD_EQ_BITS_ALT, BIT_WORD_AND_NOT_SUB_1, BIT_MASK_WORD] THEN
    REWRITE_TAC [← GSYM NOT_LE, WORD_CTZ_LE] THEN MESON_TAC [NOT_LE])

  let WORD_CTZ_EMULATION_REV ← prove
   r"!x:N word.
        word_clz(word_and (word_not x) (word_sub x (word 1))) =
        dimindex(:N) - word_ctz x"
   (REWRITE_TAC [WORD_AND_NOT_SUB_1_CTZ, WORD_CLZ_MASK_WORD])

  let WORD_CTZ_EMULATION_AND_NEG_REV ← prove
   r"!x:N word.
     word_clz(word_and x (word_neg x)) =
     if x = word 0 then dimindex(:N) else dimindex(:N) - 1 - word_ctz x"
   (GEN_TAC THEN REWRITE_TAC [WORD_AND_NEG_CTZ, WORD_CLZ_BIT] THEN
    REWRITE_TAC [WORD_CTZ_LT_DIMINDEX, COND_SWAP] THEN ARITH_TAC)

  let WORD_CTZ_EMULATION_XOR_SUB_1_REV ← prove
   r"!x:N word.
    word_clz(word_xor x (word_sub x (word 1))) = dimindex(:N) - 1 - word_ctz x"
   (GEN_TAC THEN REWRITE_TAC [WORD_XOR_SUB_1_CTZ, WORD_CLZ_MASK_WORD] THEN
    ARITH_TAC)

  let WORD_CTZ_EMULATION ← prove
   r"!x:N word.
        word_ctz x =
        dimindex(:N) - word_clz(word_and (word_not x) (word_sub x (word 1)))"
   (GEN_TAC THEN MATCH_MP_TAC (← ARITH_RULE
     (← q r"t:num <= n /\ l <= n /\ l = n - t ==> t = n - l")) THEN
    REWRITE_TAC [WORD_CLZ_LE_DIMINDEX, WORD_CTZ_LE_DIMINDEX] THEN
    REWRITE_TAC [WORD_CTZ_EMULATION_REV])

  let WORD_CTZ_EMULATION_AND_NEG ← prove
   r"!x:N word.
        word_ctz x =
        if x = word 0 then dimindex(:N)
        else dimindex(:N) - 1 - word_clz(word_and x (word_neg x))"
   (GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [WORD_CTZ_0] THEN
    ASM_REWRITE_TAC [WORD_CTZ_EMULATION_AND_NEG_REV] THEN
    ASM_SIMP_TAC [WORD_CTZ_LT_DIMINDEX, DIMINDEX_GE_1, ← ARITH_RULE
     (← q r"1 <= n ==> (c = n - 1 - (n - 1 - c) <=> c < n)")])

  let WORD_CTZ_EMULATION_XOR_SUB_1 ← prove
   r"!x:N word.
        word_ctz x =
        if x = word 0 then dimindex(:N)
        else dimindex(:N) - 1 - word_clz(word_xor x (word_sub x (word 1)))"
   (GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [WORD_CTZ_0] THEN
    REWRITE_TAC [WORD_CTZ_EMULATION_XOR_SUB_1_REV] THEN
    ASM_SIMP_TAC [WORD_CTZ_LT_DIMINDEX, DIMINDEX_GE_1, ← ARITH_RULE
     (← q r"1 <= n ==> (c = n - 1 - (n - 1 - c) <=> c < n)")])

  let WORD_CLZ_IMP ← prove
   r"!(x:N word) (y:N word).
        (!i. i < dimindex(:N) /\ bit i x ==> bit i y)
        ==> word_clz y <= word_clz x"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC (← MESON [LE_TRANS, LE_REFL]
     (← q r"(!d:num. d <= x ==> d <= y) ==> x <= y")) THEN
    REWRITE_TAC [WORD_LE_CLZ] THEN ASM_MESON_TAC [BIT_TRIVIAL, NOT_LE])

  let _f3 ← TAUT (← q r"p /\ q /\ r <=> (p /\ q) /\ (p /\ r)")
  let _f2 ← TAUT (← q r"p \/ q ==> r <=> (p ==> r) /\ (q ==> r)")
  let _f1 ← ARITH_RULE
    (← q r"p = MIN m n <=> p <= m /\ p <= n /\ (m <= p \/ n <= p)")
  let WORD_CLZ_OR ← prove
   r"!(x:N word) y. word_clz (word_or x y) = MIN (word_clz x) (word_clz y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [_f1] THEN
    SIMP_TAC [WORD_CLZ_IMP, BIT_WORD_OR_ALT] THEN
    MP_TAC (← ISPEC (← q r"word_or x y:N word") WORD_LE_CLZ) THEN
    REWRITE_TAC [BIT_WORD_OR_ALT, FORALL_AND_THM, _f2] THEN
    ONCE_REWRITE_TAC [_f3] THEN
    SIMP_TAC [← GSYM WORD_LE_CLZ] THEN ARITH_TAC)

  let WORD_CTZ_IMP ← prove
   r"!(x:N word) (y:N word).
        (!i. i < dimindex(:N) /\ bit i x ==> bit i y)
        ==> word_ctz y <= word_ctz x"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC (← MESON [LE_TRANS, LE_REFL]
     (← q r"(!d:num. d <= x ==> d <= y) ==> x <= y")) THEN
    REWRITE_TAC [WORD_LE_CTZ] THEN ASM_MESON_TAC [BIT_TRIVIAL, NOT_LE])

  let _g3 ← TAUT (← q r"p /\ q /\ r <=> (p /\ q) /\ (p /\ r)")
  let _g2 ← TAUT (← q r"p \/ q ==> r <=> (p ==> r) /\ (q ==> r)")
  let _g1 ← ARITH_RULE
    (← q r"p = MIN m n <=> p <= m /\ p <= n /\ (m <= p \/ n <= p)")
  let WORD_CTZ_OR ← prove
   r"!(x:N word) y. word_ctz (word_or x y) = MIN (word_ctz x) (word_ctz y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [_g1] THEN
    SIMP_TAC [WORD_CTZ_IMP, BIT_WORD_OR_ALT] THEN
    MP_TAC (← ISPEC (← q r"word_or x y:N word") WORD_LE_CTZ) THEN
    REWRITE_TAC [BIT_WORD_OR_ALT, FORALL_AND_THM, _g2] THEN
    ONCE_REWRITE_TAC [_g3] THEN
    SIMP_TAC [← GSYM WORD_LE_CTZ] THEN ARITH_TAC)

  let WORD_CLZ_MONO ← prove
   r"!(x:N word) (y:N word). val x <= val y ==> word_clz y <= word_clz x"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC (← MESON [LE_TRANS, LE_REFL]
     (← q r"(!d:num. d <= x ==> d <= y) ==> x <= y")) THEN
    REWRITE_TAC [WORD_LE_CLZ_VAL] THEN ASM_ARITH_TAC)

  let WORD_CTZ_EMULATION_POPCOUNT ← prove
   r"!x:N word.
        word_ctz x =
        word_popcount(word_and (word_not x) (word_sub x (word 1)))"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"x:N word = word 0") THEN
    ASM_REWRITE_TAC [word_ctz, WORD_AND_REFL, WORD_POPCOUNT_NOT,
                     WORD_POPCOUNT_0, SUB_0, ← WORD_RULE
                       (← q r"word_sub (word 0) (word 1) = word_not(word 0)")] THEN
    REWRITE_TAC [word_popcount, bits_of_word, BIT_WORD_AND_NOT_SUB_1] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [WORD_EQ_BITS]) THEN
    REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, BIT_WORD_0] THEN
    GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN
    ABBREV_TAC (← q r"m = minimal i. bit i (x:N word)") THEN POP_ASSUM (fun _ => ALL_TAC) THEN
    STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM CARD_NUMSEG_LT] THEN
    AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
    ASM_MESON_TAC [BIT_GUARD, LTE_TRANS, LT_TRANS, LE_REFL, NOT_LE])

  -- @@RETURN BEGIN
  return { word_ctz, word_clz, WORD_CLZ, WORD_CTZ_0, WORD_LE_CTZ, WORD_CTZ_LE,
           WORD_CTZ_LE_DIMINDEX, WORD_CTZ_LBOUND, WORD_CTZ_EQ_DIMINDEX,
           WORD_CTZ_LT_DIMINDEX, WORD_CTZ_EQ_0, WORD_CTZ_UNIQUE_GEN, WORD_CTZ_UNIQUE,
           WORD_LE_CTZ_VAL_MOD, WORD_LE_CTZ_VAL, WORD_CTZ_UNIQUE_VAL, WORD_CLZ_0,
           WORD_SIZE_SUB_CLZ, WORD_CLZ_LE_DIMINDEX, WORD_LE_CLZ, WORD_CLZ_LE,
           WORD_CLZ_LBOUND_ALT, WORD_CLZ_LBOUND, WORD_CLZ_EQ_DIMINDEX,
           WORD_CLZ_LT_DIMINDEX, WORD_CLZ_EQ_0, WORD_CLZ_DECOMP, WORD_CLZ_UNIQUE_GEN,
           WORD_CLZ_UNIQUE, WORD_LE_CLZ_VAL, WORD_LE_CLZ_VAL_MULT, WORD_LE_CLZ_VAL_DIV,
           VAL_BOUND_CLZ, WORD_CLZ_UNIQUE_VAL, WORD_CTZ_BIT, WORD_CLZ_BIT,
           WORD_CTZ_MASK_WORD, WORD_CLZ_MASK_WORD, WORD_AND_NEG_CTZ, WORD_XOR_SUB_1_CTZ,
           WORD_AND_NOT_SUB_1_CTZ, WORD_CTZ_EMULATION_REV,
           WORD_CTZ_EMULATION_AND_NEG_REV, WORD_CTZ_EMULATION_XOR_SUB_1_REV,
           WORD_CTZ_EMULATION, WORD_CTZ_EMULATION_AND_NEG, WORD_CTZ_EMULATION_XOR_SUB_1,
           WORD_CLZ_IMP, WORD_CLZ_OR, WORD_CTZ_IMP, WORD_CTZ_OR, WORD_CLZ_MONO,
           WORD_CTZ_EMULATION_POPCOUNT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Reversal of the b-bit fields in an N-bit word. If N isn't a multiple      -/
/- of b, this leaves bits above the highest b multiple unchanged.            -/
/- Byte reversal, with type constrained to multiple of 8.                    -/
/- Multiplication of binary polynomials as words, "carryless multiplication" -/
/- ------------------------------------------------------------------------- -/

structure Reverse where
  -- @@FIELDS
  word_reversefields : thm
  BIT_WORD_REVERSEFIELDS : thm
  WORD_REVERSEFIELDS_REVERSEFIELDS : thm
  BIT_REVERSEFIELDS_1 : thm
  WORD_CTZ_REVERSEFIELDS : thm
  WORD_CLZ_REVERSEFIELDS : thm
  WORD_CLZ_USHR : thm
  WORD_SHL_AS_USHR : thm
  WORD_USHR_AS_SHL : thm
  WORD_CTZ_SHL : thm
  word_bytereverse : thm
  BIT_WORD_BYTEREVERSE : thm
  WORD_BYTEREVERSE_BYTEREVERSE : thm
  WORD_BYTEREVERSE_REVERSEFIELDS : thm
  word_pmul : thm
  BIT_WORD_PMUL_ALT : thm
  BIT_WORD_PMUL : thm
  BITVAL_BIT_WORD_PMUL : thm
  WORD_PMUL_0 : thm
  WORD_PMUL_XOR : thm
  WORD_PMUL_ZX : thm
  WORD_PMUL_STEP : thm
  WORD_PMUL_SYM : thm
  WORD_PMUL_POW2 : thm
  deriving Inhabited

@[nospecialize]
def setupReverse [HolBase] (D : WordsDeps) (BBitval : Bitval) (BWordType : WordType) (BBitsOfWord : BitsOfWord) (BVal : Val) (BWordOps1 : WordOps1) (BWordOps2 : WordOps2) (BWordOps3 : WordOps3) (BZxSx : ZxSx) (BClzCtz : ClzCtz) :
    ExceptT String IO Reverse := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, MESON, MESON_TAC, NUM_REDUCE_CONV,
        SET_TAC, define, new_definition, .. } := D
  let { ADD1, ADD_CLAUSES, ARITH_EQ, ARITH_ODD, CARD_CLAUSES, COND_RAND, CONJ_ASSOC,
        DIMINDEX_TYBIT0, DIVISION, DIVISION_SIMP, DIV_1, DIV_LT, DIV_MULT,
        DIV_MULT_ADD, DIV_ZERO, EMPTY_GSPEC, EQ_TRANS, EVEN, EVEN_ADD, EXTENSION, .. } := D.core1
  let { FINITE_NUMSEG, FINITE_RESTRICT, FUN_EQ_THM, IN_ELIM_THM, IN_NUMSEG, .. } := D.core2
  let { LE_0, LE_1, LE_ANTISYM, LE_MULT_LCANCEL, LE_REFL, LT, LTE_TRANS, MOD_1,
        MOD_LT_EQ, MOD_LT_EQ_LT, MOD_MOD_REFL, MOD_MULT_ADD, MOD_ZERO, MULT_ASSOC,
        MULT_CLAUSES, MULT_SYM, NOT_ODD, NSUM_ADD_NUMSEG, NSUM_CLAUSES_LEFT,
        NSUM_CLAUSES_NUMSEG, NSUM_CLOSED, NSUM_CONST, NSUM_DELTA, NSUM_OFFSET,
        NSUM_REFLECT, NSUM_RESTRICT_SET, ODD, ODD_ADD, ODD_MULT, .. } := D.core3
  let { RDIV_LT_EQ, SUB_0, .. } := D.core4
  let { BITVAL_AND, BITVAL_CLAUSES, BITVAL_ODD, BITVAL_XOR, bitval, .. } := BBitval
  let { BIT_GUARD, WORD_EQ_BITS_ALT, .. } := BWordType
  let { BIT_WORD_OF_BITS, WORD_OF_BITS_EQ, .. } := BBitsOfWord
  let { BIT_WORD_0, BIT_WORD_POW2, WORD_OF_BITS_EMPTY, .. } := BVal
  let { BIT_WORD_XOR, BIT_WORD_XOR_ALT, .. } := BWordOps1
  let { BIT_WORD_SHL, .. } := BWordOps2
  let { BIT_WORD_USHR, .. } := BWordOps3
  let { BIT_WORD_ZX, .. } := BZxSx
  let { WORD_CLZ_UNIQUE_GEN, WORD_LE_CLZ, WORD_LE_CTZ, .. } := BClzCtz
  -- @@SCOPE END
  let word_reversefields ← new_definition
   r"(word_reversefields:num->(N)word->(N)word) (b:num) w =
  word_of_bits
    { i | i < dimindex(:N) /\
          bit (if i < b * dimindex(:N) DIV b
               then b * (dimindex(:N) DIV b - 1 - i DIV b) + i MOD b
               else i) w}"

  let BIT_WORD_REVERSEFIELDS ← prove
   r"!(x:(N)word) b i.
        bit i (word_reversefields b x) <=>
        i < dimindex(:N) /\
        bit (if i < b * dimindex(:N) DIV b
             then b * (dimindex(:N) DIV b - 1 - i DIV b) + i MOD b
             else i) x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_reversefields, BIT_WORD_OF_BITS] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC [])

  let _a3 ← ARITH_RULE (← q r"x < n ==> n - 1 - (n - 1 - x) = x")
  let _a2 ← ARITH_RULE (← q r"m < n /\ n * (x + 1) <= n * q ==> n * x + m < n * q")
  let _a1 ← ARITH_RULE (← q r"b = 0 \/ 0 < b")
  let WORD_REVERSEFIELDS_REVERSEFIELDS ← prove
   r"!(x:(N)word) b. word_reversefields b (word_reversefields b x) = x"
   (ONCE_REWRITE_TAC [WORD_EQ_BITS_ALT] THEN
    REWRITE_TAC [BIT_WORD_REVERSEFIELDS] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    DISJ_CASES_TAC _a1 THEN
    ASM_REWRITE_TAC [MOD_ZERO, DIV_ZERO, MULT_CLAUSES, ADD_CLAUSES, LT] THEN
    ABBREV_TAC (← q r"q = dimindex (:N) DIV b") THEN
    ASM_CASES_TAC (← q r"i:num < b * q") THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [← ONCE_REWRITE_RULE [MULT_SYM] DIV_MULT, LE_1, DIV_MULT_ADD,
      MOD_MULT_ADD, MOD_MOD_REFL, DIV_LT, MOD_LT_EQ_LT, ADD_CLAUSES] THEN
    SUBGOAL_THEN (← q r"b * (q - 1 - i DIV b) + i MOD b < b * q") ASSUME_TAC THENL
     [MATCH_MP_TAC _a2 THEN
      ASM_REWRITE_TAC [MOD_LT_EQ_LT, LE_MULT_LCANCEL] THEN
      UNDISCH_TAC (← q r"i:num < b * q") THEN
      ASM_CASES_TAC (← q r"q = 0") THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
      ASM_REWRITE_TAC []] THEN
    MATCH_MP_TAC (← TAUT (← q r"p /\ (q <=> q') ==> (p /\ q <=> q')")) THEN CONJ_TAC THENL
     [TRANS_TAC LTE_TRANS (← q r"b * q:num") THEN ASM_REWRITE_TAC [] THEN
      MP_TAC (← SPECL [← q r"dimindex(:N)", ← q "b:num"] DIVISION) THEN
      ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
      AP_THM_TAC THEN AP_TERM_TAC THEN
      TRANS_TAC EQ_TRANS (← q r"b * i DIV b + i MOD b") THEN
      CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [DIVISION_SIMP]] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC _a3 THEN
      ASM_SIMP_TAC [RDIV_LT_EQ, LE_1] THEN ASM_ARITH_TAC])

  let BIT_REVERSEFIELDS_1 ← prove
   r"!(x:N word) i.
        bit i (word_reversefields 1 x) <=>
        i < dimindex(:N) /\ bit (dimindex(:N) - 1 - i) x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [BIT_WORD_REVERSEFIELDS] THEN
    REWRITE_TAC [MULT_CLAUSES, DIV_1, MOD_1, ADD_CLAUSES] THEN
    MESON_TAC [])

  let _b2 ← ARITH_RULE (← q r"i < n ==> n - 1 - (n - 1 - i) = i")
  let _b1 ← MESON [LE_REFL, LE_ANTISYM] (← q r"a = b <=> !x:num. x <= a <=> x <= b")
  let WORD_CTZ_REVERSEFIELDS ← prove
   r"!x:N word. word_ctz(word_reversefields 1 x) = word_clz x"
   (GEN_TAC THEN REWRITE_TAC [_b1] THEN
    REWRITE_TAC [WORD_LE_CTZ, WORD_LE_CLZ] THEN
    X_GEN_TAC (← q "k:num") THEN REWRITE_TAC [BIT_REVERSEFIELDS_1] THEN
    MATCH_MP_TAC (← TAUT (← q r"(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)")) THEN
    DISCH_TAC THEN EQ_TAC THEN DISCH_TAC THEN
    X_GEN_TAC (← q "i:num") THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"dimindex(:N) - 1 - i")) THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE id [BIT_GUARD]) THEN
    ASM_SIMP_TAC [_b2] THEN
    ASM_ARITH_TAC)

  let WORD_CLZ_REVERSEFIELDS ← prove
   r"!x:N word. word_clz(word_reversefields 1 x) = word_ctz x"
   (MESON_TAC [WORD_REVERSEFIELDS_REVERSEFIELDS, WORD_CTZ_REVERSEFIELDS])

  let _c3 ← ARITH_RULE (← q r"N - MIN N c <= i <=> N <= i + c")
  let _c2 ← ARITH_RULE (← q r"c + n < N ==> N - MIN N (c + n) - 1 + n = N - c - 1")
  let _c1 ← ARITH_RULE (← q r"MIN a b < a <=> b < a")
  let WORD_CLZ_USHR ← prove
   r"!(x:N word) n.
        word_clz (word_ushr x n) = MIN (dimindex(:N)) (word_clz x + n)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [WORD_CLZ_UNIQUE_GEN, BIT_WORD_USHR] THEN
    CONJ_TAC THENL [ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [_c1] THEN
    SIMP_TAC [_c2] THEN
    REWRITE_TAC [_c3] THEN
    MP_TAC (← ISPECL [← q "x:N word", ← q r"word_clz(x:N word)"] WORD_CLZ_UNIQUE_GEN) THEN
    REWRITE_TAC [LE_REFL] THEN STRIP_TAC THEN CONJ_TAC THENL
     [DISCH_TAC, GEN_TAC THEN DISCH_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC)

  let WORD_SHL_AS_USHR ← prove
   r"!(x:N word) n.
        word_shl x n =
        word_reversefields 1 (word_ushr (word_reversefields 1 x) n)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [WORD_EQ_BITS_ALT] THEN
    REWRITE_TAC [BIT_REVERSEFIELDS_1, BIT_WORD_SHL, BIT_WORD_USHR] THEN
    X_GEN_TAC (← q "i:num") THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"i < N ==> (N - 1 - i + n < N <=> n <= i)")] THEN
    ASM_CASES_TAC (← q r"n:num <= i") THEN ASM_REWRITE_TAC [] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC)

  let WORD_USHR_AS_SHL ← prove
   r"!(x:N word) n.
        word_ushr x n =
        word_reversefields 1 (word_shl (word_reversefields 1 x) n)"
   (REWRITE_TAC [WORD_SHL_AS_USHR, WORD_REVERSEFIELDS_REVERSEFIELDS])

  let WORD_CTZ_SHL ← prove
   r"!(x:N word) n.
        word_ctz (word_shl x n) = MIN (dimindex(:N)) (word_ctz x + n)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [← GSYM WORD_CLZ_REVERSEFIELDS, WORD_SHL_AS_USHR,
                 WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
    REWRITE_TAC [WORD_CLZ_USHR])

  let word_bytereverse ← new_definition
   r"(word_bytereverse
    :((((N)tybit0)tybit0)tybit0)word->((((N)tybit0)tybit0)tybit0)word) x =
  word_of_bits { i | i < 8 * dimindex(:N) /\
                     bit (8 * (dimindex(:N) - 1 - i DIV 8) + i MOD 8) x}"

  let BIT_WORD_BYTEREVERSE ← prove
   r"!(x:((((N)tybit0)tybit0)tybit0)word) i.
        bit i (word_bytereverse x) <=>
        i < 8 * dimindex(:N) /\
        bit (8 * (dimindex(:N) - 1 - i DIV 8) + i MOD 8) x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_bytereverse, BIT_WORD_OF_BITS] THEN
    REWRITE_TAC [DIMINDEX_TYBIT0, ← ARITH_RULE (← q r"2 * 2 * 2 * n = 8 * n")] THEN
    SET_TAC [])

  let _d2 ← ARITH_RULE (← q r"i < 8 * n ==> 8 * (n - 1 - i DIV 8) + i MOD 8 < 8 * n")
  let _d1 ← ARITH_RULE (← q r"2 * 2 * 2 * n = 8 * n")
  let WORD_BYTEREVERSE_BYTEREVERSE ← prove
   r"!(x:((((N)tybit0)tybit0)tybit0)word).
        word_bytereverse(word_bytereverse x) = x"
   (ONCE_REWRITE_TAC [WORD_EQ_BITS_ALT] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC [BIT_WORD_BYTEREVERSE] THEN
    REWRITE_TAC [DIMINDEX_TYBIT0, _d1] THEN
    DISCH_TAC THEN ASM_SIMP_TAC [_d2] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC [MOD_MULT_ADD, MOD_MOD_REFL, DIV_MULT_ADD, ARITH_EQ] THEN
    SIMP_TAC [DIV_LT, MOD_LT_EQ, ARITH_EQ] THEN ASM_ARITH_TAC)

  let WORD_BYTEREVERSE_REVERSEFIELDS ← prove
   r"word_bytereverse = word_reversefields 8"
   (REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
    GEN_REWRITE_TAC id [WORD_EQ_BITS_ALT] THEN
    REWRITE_TAC [BIT_WORD_BYTEREVERSE, BIT_WORD_REVERSEFIELDS] THEN
    REWRITE_TAC [DIMINDEX_TYBIT0, MULT_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC [DIV_MULT, ARITH_EQ])

  let word_pmul ← define
   r"(word_pmul:M word->N word->P word) x y =
  word_of_bits {k | ODD(CARD {i | i <= k /\ bit i x /\ bit (k - i) y})}"

  let BIT_WORD_PMUL_ALT ← prove
   r"!x y k. bit k ((word_pmul:M word->N word->P word) x y) <=>
           k < dimindex(:P) /\
           ODD(CARD {i | i <= k /\ bit i x /\ bit (k - i) y})"
   (REWRITE_TAC [word_pmul, BIT_WORD_OF_BITS, IN_ELIM_THM])

  let BIT_WORD_PMUL ← prove
   r"!x y k. bit k ((word_pmul:M word->N word->P word) x y) <=>
           k < dimindex(:P) /\
           ODD(nsum (0..k) (\i. bitval(bit i x) * bitval(bit (k - i) y)))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [BIT_WORD_PMUL_ALT] THEN
    AP_TERM_TAC THEN REWRITE_TAC [← GSYM BITVAL_AND] THEN
    REWRITE_TAC [bitval, ← GSYM NSUM_RESTRICT_SET] THEN
    SIMP_TAC [NSUM_CONST, FINITE_RESTRICT, FINITE_NUMSEG] THEN
    REWRITE_TAC [MULT_CLAUSES, LE_0, IN_NUMSEG])

  let BITVAL_BIT_WORD_PMUL ← prove
   r"!x y k. bitval(bit k ((word_pmul:M word->N word->P word) x y)) =
           if k < dimindex(:P)
           then nsum(0..k) (\i. bitval(bit i x) * bitval(bit (k - i) y)) MOD 2
           else 0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [BIT_WORD_PMUL] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [BITVAL_CLAUSES, BITVAL_ODD])

  let WORD_PMUL_0 ← prove
   r"(!y. (word_pmul:M word->N word->P word) (word 0) y = word 0) /\
   (!x. (word_pmul:M word->N word->P word) x (word 0) = word 0)"
   (REWRITE_TAC [word_pmul, BIT_WORD_0, MULT_CLAUSES, EMPTY_GSPEC,
                 CARD_CLAUSES, ODD, WORD_OF_BITS_EMPTY])

  let WORD_PMUL_XOR ← prove
   r"(!x y z. (word_pmul:M word->N word->P word) (word_xor x y) z =
            word_xor (word_pmul x z) (word_pmul y z)) /\
   (!x y z. (word_pmul:M word->N word->P word) x (word_xor y z) =
            word_xor (word_pmul x y) (word_pmul x z))"
   (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC id [WORD_EQ_BITS_ALT] THEN
    REWRITE_TAC [BIT_WORD_PMUL, BIT_WORD_XOR_ALT] THEN
    X_GEN_TAC (← q "i:num") THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [← GSYM ODD_ADD] THEN
    REWRITE_TAC [← MESON [ODD_ADD, NOT_ODD] (← q r"(ODD x <=> ODD y) <=> EVEN(x + y)")] THEN
    REWRITE_TAC [← GSYM NSUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC (← ISPEC (← q "EVEN") NSUM_CLOSED) THEN
    SIMP_TAC [EVEN, EVEN_ADD] THEN X_GEN_TAC (← q "j:num") THEN DISCH_TAC THEN
    REWRITE_TAC [IN_NUMSEG, LE_0, BITVAL_XOR] THEN
    REWRITE_TAC [bitval] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    CONV_TAC NUM_REDUCE_CONV)

  let WORD_PMUL_ZX ← prove
   r"(!x y. word_pmul (word_zx x:P word) y =
          (word_pmul:M word->N word->P word) x y) /\
   (!x y. word_pmul x (word_zx y:P word) =
          (word_pmul:M word->N word->P word) x y)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [word_pmul, BIT_WORD_ZX] THEN
    GEN_REWRITE_TAC id [WORD_OF_BITS_EQ] THEN SIMP_TAC [IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC id [EXTENSION] THEN GEN_TAC THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC)

  let _e8 ← ARITH_RULE (← q r"(i + j) + j = 2 * j + i")
  let _e7 ← ARITH_RULE (← q r"~(SUC i <= i)")
  let _e6 ← ARITH_RULE (← q r"1 <= SUC n")
  let _e5 ← ARITH_RULE (← q r"1 <= i - j <=> j + 1 <= i")
  let _e4 ← ARITH_RULE (← q r"i - j - 1 = i - (j + 1)")
  let _e3 ← ARITH_RULE (← q r"i:num < N ==> i - j < N")
  let WORD_PMUL_STEP ← prove
   r"!x y. (word_pmul:M word->N word->N word) x y =
         word_xor (if bit 0 x then y else word 0)
                  (word_pmul (word_ushr x 1) (word_shl y 1))"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC id [WORD_EQ_BITS_ALT] THEN
    X_GEN_TAC (← q "i:num") THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [BIT_WORD_XOR, BIT_WORD_PMUL] THEN
    REWRITE_TAC [← TAUT (← q r"(p <=> ~(q <=> r)) <=> ~(p <=> r) <=> q")] THEN
    REWRITE_TAC [← GSYM ODD_ADD] THEN
    REWRITE_TAC [BIT_WORD_USHR, BIT_WORD_SHL] THEN
    ASM_SIMP_TAC [_e3] THEN
    REWRITE_TAC [_e4] THEN
    REWRITE_TAC [_e5] THEN
    REWRITE_TAC [← GSYM (← SPEC (← q "1") NSUM_OFFSET)] THEN
    SIMP_TAC [NSUM_CLAUSES_LEFT, LE_0] THEN REWRITE_TAC [ADD_CLAUSES] THEN
    REWRITE_TAC [← GSYM ADD1, NSUM_CLAUSES_NUMSEG, _e6] THEN
    SIMP_TAC [_e7, BITVAL_CLAUSES, MULT_CLAUSES] THEN
    REWRITE_TAC [ADD_CLAUSES, _e8] THEN
    REWRITE_TAC [ODD_ADD, ODD_MULT, ARITH_ODD, SUB_0] THEN
    REWRITE_TAC [bitval] THEN REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REWRITE_TAC [BIT_WORD_0] THEN CONV_TAC NUM_REDUCE_CONV)

  let WORD_PMUL_SYM ← prove
   r"!x y. (word_pmul:M word->M word->N word) x y = word_pmul y x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [WORD_EQ_BITS_ALT] THEN
    REWRITE_TAC [BIT_WORD_PMUL] THEN X_GEN_TAC (← q "i:num") THEN DISCH_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [NSUM_REFLECT] THEN
    ASM_SIMP_TAC [LT, SUB_0, ← ARITH_RULE (← q r"j:num <= i ==> i - (i - j) = j")] THEN
    REWRITE_TAC [MULT_SYM])

  let WORD_PMUL_POW2 ← prove
   r"(!(x:N word) n. word_pmul (word(2 EXP n):N word) x = word_shl x n) /\
   (!(x:N word) n. word_pmul x (word(2 EXP n):N word) = word_shl x n)"
   (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [WORD_PMUL_SYM] THEN
    REWRITE_TAC [] THEN REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [WORD_EQ_BITS_ALT] THEN
    X_GEN_TAC (← q "i:num") THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [BIT_WORD_PMUL, BIT_WORD_SHL, BIT_WORD_POW2] THEN
    REWRITE_TAC [← GSYM BITVAL_AND] THEN
    REWRITE_TAC [← GSYM CONJ_ASSOC, bitval] THEN
    ONCE_REWRITE_TAC [← MESON []
     (← q r"(if p /\ q then 1 else 0) = if p then (if q then 1 else 0) else 0")] THEN
    SIMP_TAC [NSUM_DELTA, IN_NUMSEG, LE_0] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [ODD] THEN
    ONCE_REWRITE_TAC [COND_RAND] THEN
    REWRITE_TAC [ARITH_ODD, ← TAUT (← q r"(if x then T else F) <=> x")] THEN
    MATCH_MP_TAC (← TAUT (← q r"p ==> (p /\ q <=> q)")) THEN ASM_ARITH_TAC)

  -- @@RETURN BEGIN
  return { word_reversefields, BIT_WORD_REVERSEFIELDS, WORD_REVERSEFIELDS_REVERSEFIELDS,
           BIT_REVERSEFIELDS_1, WORD_CTZ_REVERSEFIELDS, WORD_CLZ_REVERSEFIELDS,
           WORD_CLZ_USHR, WORD_SHL_AS_USHR, WORD_USHR_AS_SHL, WORD_CTZ_SHL,
           word_bytereverse, BIT_WORD_BYTEREVERSE, WORD_BYTEREVERSE_BYTEREVERSE,
           WORD_BYTEREVERSE_REVERSEFIELDS, word_pmul, BIT_WORD_PMUL_ALT, BIT_WORD_PMUL,
           BITVAL_BIT_WORD_PMUL, WORD_PMUL_0, WORD_PMUL_XOR, WORD_PMUL_ZX,
           WORD_PMUL_STEP, WORD_PMUL_SYM, WORD_PMUL_POW2 }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Alignment. The definition rolls in the assumption that the value is a     -/
/- power of 2 no more than the wordsize, which seems intuitively natural.    -/
/- JVM-specific word operations, though they may well work in other places.  -/
/- ------------------------------------------------------------------------- -/

structure Align where
  -- @@FIELDS
  aligned : thm
  ALIGNED : thm
  ALIGNED_WORD : thm
  ALIGNED_IWORD : thm
  ALIGNED_WORD_0 : thm
  ALIGNED_WORD_NEG : thm
  ALIGNED_WORD_ADD : thm
  ALIGNED_WORD_MUL : thm
  ALIGNED_WORD_SUB : thm
  ALIGNED_WORD_ADD_EQ : thm
  ALIGNED_WORD_SUB_EQ : thm
  word_jshl : thm
  word_jshr : thm
  word_jushr : thm
  word_jdiv : thm
  word_jrem : thm
  word_jror : thm
  word_jrol : thm
  VAL_WORD_NEG_MOD_DIMINDEX : thm
  WORD_JROL_JROR : thm
  WORD_JROR_JROL : thm
  WORD_JROR : thm
  WORD_JROL : thm
  WORD_JUSHR_NEG : thm
  WORD_JSHL_NEG : thm
  deriving Inhabited

@[nospecialize]
def setupAlign [HolBase] (D : WordsDeps) (BVal : Val) (BIval : Ival) (BWordOps1 : WordOps1) (BWordOps2 : WordOps2) (BWordOps3 : WordOps3) (BWordRule : WordRule) (BWordBitwise : WordBitwise) (BMisc1 : Misc1) :
    ExceptT String IO Align := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, INTEGER_RULE, MESON, MESON_TAC, NUMBER_RULE,
        new_definition, .. } := D
  let { CONG, DIMINDEX_GE_1, DIMINDEX_NONZERO, DIVIDES_MOD, DIVISION, .. } := D.core1
  let { INT_OF_NUM_CLAUSES, INT_OF_NUM_REM, INT_OF_NUM_SUB, INT_REM_MOD_SELF, .. } := D.core2
  let { LT_IMP_LE, MOD_LT, MOD_MOD, MOD_MULT, MOD_REFL, .. } := D.core3
  let { SUB_0, divides, num_congruent, num_divides, .. } := D.core4
  let { FORALL_WORD, VAL_BOUND, VAL_EQ_0, VAL_WORD, VAL_WORD_0, .. } := BVal
  let { IVAL_IWORD_CONG, IVAL_VAL_CONG, .. } := BIval
  let { ICONG_WORD_NEG, VAL_WORD_NEG, WORD_ADD, .. } := BWordOps1
  let { VAL_WORD_SHL, WORD_MUL, WORD_SHL_ZERO, .. } := BWordOps2
  let { WORD_ROL_PERIODIC, WORD_ROL_ROR_GEN, WORD_ROR_MOD, WORD_ROR_PERIODIC,
        WORD_ROR_ROL_GEN, WORD_ROR_SHIFTS, WORD_USHR_ZERO, .. } := BWordOps3
  let { WORD_RULE, .. } := BWordRule
  let { WORD_BITWISE_RULE, .. } := BWordBitwise
  let { WORD_ADD_SYM, .. } := BMisc1
  -- @@SCOPE END
  let NR : tactic := CONV_TAC (fun t => (NUMBER_RULE t).run)
  let WBR : tactic := CONV_TAC (fun t => (WORD_BITWISE_RULE t).run)

  let aligned ← new_definition
   r"aligned n (a:N word) <=>
    n divides 2 EXP dimindex(:N) /\ n divides val a"

  let ALIGNED ← prove
   r"!n x:N word.
        aligned n x <=>
        n divides 2 EXP dimindex(:N) /\ &n divides ival(x)"
   (← do
    let ir ← INTEGER_RULE
     (← q r"(y:int == x) (mod m)
    ==> n divides m
        ==> (n divides x <=> n divides y)")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [aligned] THEN
      MATCH_MP_TAC (← TAUT (← q r"(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)")) THEN
      REWRITE_TAC [num_divides, ← GSYM INT_OF_NUM_CLAUSES] THEN
      MATCH_MP_TAC ir THEN
      REWRITE_TAC [IVAL_VAL_CONG]))

  let ALIGNED_WORD ← prove
   r"!n k. aligned n (word k:N word) <=>
         n divides 2 EXP dimindex(:N) /\ n divides k"
   (REPEAT GEN_TAC THEN REWRITE_TAC [aligned] THEN
    MATCH_MP_TAC (← TAUT (← q r"(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)")) THEN
    GEN_REWRITE_TAC LAND_CONV [divides] THEN
    REWRITE_TAC [aligned, VAL_WORD, DIVIDES_MOD] THEN
    DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN REWRITE_TAC [MOD_MOD])

  let ALIGNED_IWORD ← prove
   r"!n k. aligned n (iword k:N word) <=>
         n divides 2 EXP dimindex(:N) /\ &n divides k"
   (← do
    let ir ← INTEGER_RULE
     (← q r"(x:int == y) (mod m)
    ==> n divides m
        ==> (n divides x <=> n divides y)")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [ALIGNED] THEN
      MATCH_MP_TAC (← TAUT (← q r"(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)")) THEN
      REWRITE_TAC [num_divides, ← GSYM INT_OF_NUM_CLAUSES] THEN
      MATCH_MP_TAC ir THEN
      REWRITE_TAC [IVAL_IWORD_CONG]))

  let ALIGNED_WORD_0 ← prove
   r"!n. aligned n (word 0:N word) <=> n divides 2 EXP dimindex(:N)"
   (REWRITE_TAC [ALIGNED_WORD, VAL_WORD_0] THEN NR)

  let ALIGNED_WORD_NEG ← prove
   r"!n x:N word. aligned n (word_neg x) <=> aligned n x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [ALIGNED] THEN
    REWRITE_TAC [num_divides, ← GSYM INT_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC (← INTEGER_RULE
     (← q r"(y:int == --x) (mod e)
    ==> (n divides e /\ n divides y <=> n divides e /\ n divides x)")) THEN
    REWRITE_TAC [ICONG_WORD_NEG])

  let ALIGNED_WORD_ADD ← prove
   r"!n a b:N word.
        aligned n a /\ aligned n b ==> aligned n (word_add a b)"
   (REWRITE_TAC [FORALL_WORD, ALIGNED_WORD, ← GSYM WORD_ADD] THEN NR)

  let ALIGNED_WORD_MUL ← prove
   r"!n a b:N word.
        aligned n a \/ aligned n b ==> aligned n (word_mul a b)"
   (REWRITE_TAC [FORALL_WORD, ALIGNED_WORD, ← GSYM WORD_MUL] THEN NR)

  let ALIGNED_WORD_SUB ← prove
   r"!n a b:N word.
        aligned n a /\ aligned n b ==> aligned n (word_sub a b)"
   (REWRITE_TAC [← WORD_RULE (← q r"word_sub x y:N word = word_add x (word_neg y)")] THEN
    SIMP_TAC [ALIGNED_WORD_NEG, ALIGNED_WORD_ADD])

  let ALIGNED_WORD_ADD_EQ ← prove
   r"(!n x y:N word.
        aligned n x ==> (aligned n (word_add x y) <=> aligned n y)) /\
   (!n x y:N word.
        aligned n y ==> (aligned n (word_add x y) <=> aligned n x))"
   (MESON_TAC [ALIGNED_WORD_ADD, ALIGNED_WORD_NEG, WORD_ADD_SYM,
               ← WORD_RULE (← q r"word_add (word_neg x) (word_add x y) = y")])

  let ALIGNED_WORD_SUB_EQ ← prove
   r"(!n x y:N word.
        aligned n x ==> (aligned n (word_sub x y) <=> aligned n y)) /\
   (!n x y:N word.
        aligned n y ==> (aligned n (word_sub x y) <=> aligned n x))"
   (REWRITE_TAC [← WORD_RULE (← q r"word_sub x y = word_add x (word_neg y)")] THEN
    MESON_TAC [ALIGNED_WORD_ADD_EQ, ALIGNED_WORD_NEG])

  let word_jshl ← new_definition
   r"word_jshl (x:N word) (y:N word) =
        word_shl x (val y MOD dimindex(:N))"

  let word_jshr ← new_definition
   r"word_jshr (x:N word) (y:N word) =
        word_ishr x (val y MOD dimindex(:N))"

  let word_jushr ← new_definition
   r"word_jushr (x:N word) (y:N word) =
        word_ushr x (val y MOD dimindex(:N))"

  let word_jdiv ← new_definition
   r"word_jdiv:N word->N word->N word =
   imodular (\a b. int_sgn a * int_sgn b * (abs(a) div abs(b)))"

  let word_jrem ← new_definition
   r"word_jrem (x:N word) (y:N word) =
    word_sub x (word_mul (word_jdiv x y) y)"

  let word_jror ← new_definition
   r"word_jror (w:N word) (k:N word) = word_ror w (val k)"

  let word_jrol ← new_definition
   r"word_jrol (w:N word) (k:N word) = word_rol w (val k)"

  let _f2 ← INTEGER_RULE
    (← q r"n divides e /\ (k':int == k) (mod n) ==> (e - k == n - k') (mod n)")
  let _f1 ← MESON []
    (← q r"x MOD n MOD m = x MOD m /\ x MOD m = y ==> x MOD n MOD m = y")
  let VAL_WORD_NEG_MOD_DIMINDEX ← prove
   r"!k:N word.
        dimindex(:N) divides 2 EXP dimindex(:N)
        ==> (val(word_neg k) == dimindex (:N) - val k MOD dimindex(:N))
            (mod dimindex(:N))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [VAL_WORD_NEG, CONG] THEN
    MATCH_MP_TAC _f1 THEN
    CONJ_TAC THENL [ASM_MESON_TAC [divides, MOD_MOD], ALL_TAC] THEN
    REWRITE_TAC [← GSYM CONG, num_congruent] THEN
    SIMP_TAC [← GSYM INT_OF_NUM_SUB, LT_IMP_LE, VAL_BOUND, DIVISION,
              DIMINDEX_NONZERO, ← GSYM INT_OF_NUM_REM] THEN
    MATCH_MP_TAC _f2 THEN
    ASM_REWRITE_TAC [← GSYM num_divides, INT_REM_MOD_SELF])

  let WORD_JROL_JROR ← prove
   r"!w k:N word.
        dimindex(:N) divides 2 EXP dimindex(:N)
        ==> word_jrol w k = word_jror w (word_neg k)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [word_jrol, word_jror] THEN
    REWRITE_TAC [WORD_ROL_ROR_GEN] THEN MATCH_MP_TAC WORD_ROR_PERIODIC THEN
    ONCE_REWRITE_TAC [← NUMBER_RULE
     (← q r"(x:num == y) (mod n) <=> (y == x) (mod n)")] THEN
    MATCH_MP_TAC VAL_WORD_NEG_MOD_DIMINDEX THEN ASM_REWRITE_TAC [])

  let WORD_JROR_JROL ← prove
   r"!w k:N word.
        dimindex(:N) divides 2 EXP dimindex(:N)
        ==> word_jror w k = word_jrol w (word_neg k)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [word_jrol, word_jror] THEN
    REWRITE_TAC [WORD_ROR_ROL_GEN] THEN MATCH_MP_TAC WORD_ROL_PERIODIC THEN
    ONCE_REWRITE_TAC [← NUMBER_RULE
     (← q r"(x:num == y) (mod n) <=> (y == x) (mod n)")] THEN
    MATCH_MP_TAC VAL_WORD_NEG_MOD_DIMINDEX THEN ASM_REWRITE_TAC [])

  let _g2 ← ARITH_RULE (← q r"n - k < n <=> ~(k = 0) /\ ~(n = 0)")
  let _g1 ← WORD_BITWISE_RULE (← q r"y = word 0 ==> word_or x y = word_or x x")
  let WORD_JROR ← prove
   r"!w k:N word.
        dimindex(:N) divides 2 EXP dimindex(:N)
        ==> word_jror w k =
            word_or (word_jushr w k) (word_jshl w (word_neg k))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [word_jror, word_jushr, word_jshl] THEN
    ONCE_REWRITE_TAC [WORD_ROR_MOD] THEN
    SIMP_TAC [WORD_ROR_SHIFTS, DIVISION, DIMINDEX_NONZERO, LT_IMP_LE] THEN
    FIRST_X_ASSUM (MP_TAC o ISPEC (← q "k:N word") o
      MATCH_MP VAL_WORD_NEG_MOD_DIMINDEX) THEN
    REWRITE_TAC [CONG] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_CASES_TAC (← q r"val(k:N word) MOD dimindex(:N) = 0") THENL
     [ASM_REWRITE_TAC [SUB_0, MOD_REFL, WORD_USHR_ZERO, WORD_SHL_ZERO] THEN
      MATCH_MP_TAC _g1 THEN
      REWRITE_TAC [← GSYM VAL_EQ_0, VAL_WORD_SHL, MOD_MULT],
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
      REWRITE_TAC [_g2] THEN
      ASM_REWRITE_TAC [DIMINDEX_NONZERO]])

  let WORD_JROL ← prove
   r"!w k:N word.
        dimindex(:N) divides 2 EXP dimindex(:N)
        ==> word_jrol w k =
            word_or (word_jshl w k) (word_jushr w (word_neg k))"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [WORD_JROL_JROR, WORD_JROR] THEN
    ONCE_REWRITE_TAC [← WORD_RULE (← q r"word_neg(word_neg x):N word = x")] THEN
    WBR)

  let WORD_JUSHR_NEG ← prove
   r"!w k:N word.
        dimindex(:N) divides 2 EXP dimindex(:N)
        ==> word_jushr w (word_neg k) =
            if val k MOD dimindex(:N) = 0 then w
            else word_ushr w (dimindex(:N) - val k MOD dimindex(:N))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [word_jushr] THEN
    ASM_SIMP_TAC [← REWRITE_RULE [CONG] VAL_WORD_NEG_MOD_DIMINDEX] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [SUB_0, MOD_REFL, WORD_USHR_ZERO] THEN
    ASM_SIMP_TAC [MOD_LT, DIMINDEX_GE_1, ← ARITH_RULE
      (← q r"1 <= n /\ ~(m = 0) ==> n - m < n")])

  let WORD_JSHL_NEG ← prove
   r"!w k:N word.
        dimindex(:N) divides 2 EXP dimindex(:N)
        ==> word_jshl w (word_neg k) =
            if val k MOD dimindex(:N) = 0 then w
            else word_shl w (dimindex(:N) - val k MOD dimindex(:N))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [word_jshl] THEN
    ASM_SIMP_TAC [← REWRITE_RULE [CONG] VAL_WORD_NEG_MOD_DIMINDEX] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [SUB_0, MOD_REFL, WORD_SHL_ZERO] THEN
    ASM_SIMP_TAC [MOD_LT, DIMINDEX_GE_1, ← ARITH_RULE
      (← q r"1 <= n /\ ~(m = 0) ==> n - m < n")])

  -- @@RETURN BEGIN
  return { aligned, ALIGNED, ALIGNED_WORD, ALIGNED_IWORD, ALIGNED_WORD_0,
           ALIGNED_WORD_NEG, ALIGNED_WORD_ADD, ALIGNED_WORD_MUL, ALIGNED_WORD_SUB,
           ALIGNED_WORD_ADD_EQ, ALIGNED_WORD_SUB_EQ, word_jshl, word_jshr, word_jushr,
           word_jdiv, word_jrem, word_jror, word_jrol, VAL_WORD_NEG_MOD_DIMINDEX,
           WORD_JROL_JROR, WORD_JROR_JROL, WORD_JROR, WORD_JROL, WORD_JUSHR_NEG,
           WORD_JSHL_NEG }
  -- @@RETURN END

/-- equal.ml's `BINOP2_CONV` on `ioconv`s: `MK_COMB(AP_TERM op (conv1 l),
conv2 r)`, whose arguments OCaml evaluates right to left, so `conv2` runs
first. -/
def binop2ConvIO (conv1 conv2 : ioconv) : ioconv := fun tm => ExceptT.run do
  let (lop, r) ← liftExcept (dest_comb tm)
  let (op, l) ← liftExcept (dest_comb lop)
  let rth ← ExceptT.mk (conv2 r)
  let lth ← ExceptT.mk (conv1 l)
  liftExcept (do HolCore.Kernel.MK_COMB (← HolCore.Equal.AP_TERM op lth) rth)

/- ------------------------------------------------------------------------- -/
/- Conversion for "j" forms applied to numeral shift/rotate word.            -/
/- Emulation of unsigned comparisons using signed (useful for the JVM).      -/
/- Characterizing exactness of word add or add-with-carry via comparison.    -/
/- ------------------------------------------------------------------------- -/

structure Topflip where
  -- @@FIELDS
  WORD_WORD_OPERATION_CONV : ioconv
  IVAL_TOPFLIP_VAL : thm
  WORD_ULE_TOPFLIP : thm
  WORD_ULT_TOPFLIP : thm
  WORD_UGE_TOPFLIP : thm
  WORD_UGT_TOPFLIP : thm
  WORD_ILT_TOPFLIP : thm
  WORD_ILE_TOPFLIP : thm
  WORD_IGT_TOPFLIP : thm
  WORD_IGE_TOPFLIP : thm
  WORD_LE_ADD_EXACT : thm
  WORD_ADD_LT_EXACT : thm
  WORD_ADD_LT_INEXACT : thm
  WORD_LT_ADC_EXACT : thm
  WORD_ADC_LE_EXACT : thm
  WORD_ADC_LE_INEXACT : thm
  deriving Inhabited

@[nospecialize]
def setupTopflip [HolBase] (D : WordsDeps) (BVal : Val) (BIval : Ival) (BLimits : Limits) (BGeneralOps : GeneralOps) (BWordOps1 : WordOps1) (BWordOps3 : WordOps3) (BWordBitwise : WordBitwise) (BWordArith : WordArith) (BMisc1 : Misc1) (BAlign : Align) :
    ExceptT String IO Topflip := do
  -- @@SCOPE BEGIN
  let { INT_ARITH_TAC, NUM_MOD_CONV, .. } := D
  let { GE, GT, INT_GE, INT_GT, INT_OF_NUM_LE, INT_OF_NUM_LT, .. } := D.core2
  let { MSB_INT_VAL, VAL_WORD, .. } := BVal
  let { INT_IVAL, .. } := BIval
  let { INT_VAL_WORD_INT_MIN, .. } := BLimits
  let { irelational2, relational2, .. } := BGeneralOps
  let { INT_VAL_WORD_ADD_CASES, .. } := BWordOps1
  let { WORD_ROL_MOD, WORD_ROR_MOD, word_ige, word_igt, word_ile, word_ilt, word_uge,
        word_ugt, word_ule, word_ult, .. } := BWordOps3
  let { WORD_BITWISE_RULE, .. } := BWordBitwise
  let { WORD_ARITH_TAC, .. } := BWordArith
  let { WORD_XOR_INT_MIN, .. } := BMisc1
  let { word_jrol, word_jror, word_jshl, word_jshr, word_jushr, .. } := BAlign
  -- @@SCOPE END
  let WORD_WORD_OPERATION_CONV : ioconv ← do
    let pth ← prove
     r"word_jshl (x:N word) (word n) =
     word_shl x (n MOD (2 EXP dimindex(:N)) MOD dimindex(:N)) /\
     word_jshr x (word n) =
     word_ishr x (n MOD (2 EXP dimindex(:N)) MOD dimindex(:N)) /\
     word_jushr x (word n) =
     word_ushr x (n MOD (2 EXP dimindex(:N)) MOD dimindex(:N)) /\
     word_jrol x (word n) =
     word_rol x (n MOD (2 EXP dimindex(:N)) MOD dimindex(:N)) /\
     word_jror x (word n) =
     word_ror x (n MOD (2 EXP dimindex(:N)) MOD dimindex(:N))"
     (REWRITE_TAC [word_jshl, word_jshr, word_jushr, word_jrol, word_jror] THEN
      REWRITE_TAC [VAL_WORD, ← GSYM WORD_ROL_MOD, ← GSYM WORD_ROR_MOD])
    -- `!word_SIZE_CONV` and `!word_POW2SIZE_CONV` are read here, when the
    -- conversion is built.
    let sizeConv ← D.word_SIZE_CONV.get
    let pow2Conv ← D.word_POW2SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RAND_CONV
       (binop2ConvIO (RAND_CONV pow2Conv THENC NUM_MOD_CONV) sizeConv THENC
        NUM_MOD_CONV))

  let IVAL_TOPFLIP_VAL ← prove
   r"!w:N word.
        ival(word_xor word_INT_MIN w) =
        &(val w) - &2 pow (dimindex(:N) - 1)"
   (REWRITE_TAC [INT_IVAL, WORD_XOR_INT_MIN] THEN
    REWRITE_TAC [INT_VAL_WORD_ADD_CASES, INT_VAL_WORD_INT_MIN, MSB_INT_VAL] THEN
    WORD_ARITH_TAC)

  let WORD_ULE_TOPFLIP ← prove
   r"!v w:N word.
        word_ule v w <=>
        word_ile (word_xor (word_INT_MIN) v) (word_xor (word_INT_MIN) w)"
   (REWRITE_TAC [word_ule, word_ile, relational2, irelational2] THEN
    REWRITE_TAC [IVAL_TOPFLIP_VAL, ← GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC)

  let WORD_ULT_TOPFLIP ← prove
   r"!v w:N word.
        word_ult v w <=>
        word_ilt (word_xor (word_INT_MIN) v) (word_xor (word_INT_MIN) w)"
   (REWRITE_TAC [word_ult, word_ilt, relational2, irelational2] THEN
    REWRITE_TAC [IVAL_TOPFLIP_VAL, ← GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC)

  let WORD_UGE_TOPFLIP ← prove
   r"!v w:N word.
        word_uge v w <=>
        word_ige (word_xor (word_INT_MIN) v) (word_xor (word_INT_MIN) w)"
   (REWRITE_TAC [word_uge, word_ige, relational2, irelational2] THEN
    REWRITE_TAC [IVAL_TOPFLIP_VAL, INT_GE, GE, ← GSYM INT_OF_NUM_LE] THEN
    INT_ARITH_TAC)

  let WORD_UGT_TOPFLIP ← prove
   r"!v w:N word.
        word_ugt v w <=>
        word_igt (word_xor (word_INT_MIN) v) (word_xor (word_INT_MIN) w)"
   (REWRITE_TAC [word_ugt, word_igt, relational2, irelational2] THEN
    REWRITE_TAC [IVAL_TOPFLIP_VAL, INT_GT, GT, ← GSYM INT_OF_NUM_LT] THEN
    INT_ARITH_TAC)

  let WORD_ILT_TOPFLIP ← prove
   r"!v w:N word.
        word_ilt v w <=>
        word_ult (word_xor word_INT_MIN v) (word_xor word_INT_MIN w)"
   (REWRITE_TAC [WORD_ULT_TOPFLIP] THEN
    REWRITE_TAC [← WORD_BITWISE_RULE (← q r"word_xor m (word_xor m x) = x")])

  let WORD_ILE_TOPFLIP ← prove
   r"!v w:N word.
        word_ile v w <=>
        word_ule (word_xor word_INT_MIN v) (word_xor word_INT_MIN w)"
   (REWRITE_TAC [WORD_ULE_TOPFLIP] THEN
    REWRITE_TAC [← WORD_BITWISE_RULE (← q r"word_xor m (word_xor m x) = x")])

  let WORD_IGT_TOPFLIP ← prove
   r"!v w:N word.
        word_igt v w <=>
        word_ugt (word_xor word_INT_MIN v) (word_xor word_INT_MIN w)"
   (REWRITE_TAC [WORD_UGT_TOPFLIP] THEN
    REWRITE_TAC [← WORD_BITWISE_RULE (← q r"word_xor m (word_xor m x) = x")])

  let WORD_IGE_TOPFLIP ← prove
   r"!v w:N word.
        word_ige v w <=>
        word_uge (word_xor word_INT_MIN v) (word_xor word_INT_MIN w)"
   (REWRITE_TAC [WORD_UGE_TOPFLIP] THEN
    REWRITE_TAC [← WORD_BITWISE_RULE (← q r"word_xor m (word_xor m x) = x")])

  let WORD_LE_ADD_EXACT ← prove
   r"(!x y:N word.
        val x <= val(word_add x y) <=> val(word_add x y) = val x + val y) /\
   (!x y:N word.
        val y <= val(word_add x y) <=> val(word_add x y) = val x + val y)"
   WORD_ARITH_TAC

  let WORD_ADD_LT_EXACT ← prove
   r"(!x y:N word.
        val(word_add x y) < val x <=>
        val(word_add x y) + 2 EXP dimindex(:N) = val x + val y) /\
   (!x y:N word.
        val(word_add x y) < val y <=>
        val(word_add x y) + 2 EXP dimindex(:N) = val x + val y)"
   WORD_ARITH_TAC

  let WORD_ADD_LT_INEXACT ← prove
   r"(!x y:N word.
        val(word_add x y) < val x <=> ~(val(word_add x y) = val x + val y)) /\
   (!x y:N word.
        val(word_add x y) < val y <=> ~(val(word_add x y) = val x + val y))"
   WORD_ARITH_TAC

  let WORD_LT_ADC_EXACT ← prove
   r"(!x y:N word.
        val x < val(word_add (word_add x y) (word 1)) <=>
        val(word_add (word_add x y) (word 1)) = val x + val y + 1) /\
  (!x y:N word.
        val y < val(word_add (word_add x y) (word 1)) <=>
        val(word_add (word_add x y) (word 1)) = val x + val y + 1)"
   WORD_ARITH_TAC

  let WORD_ADC_LE_EXACT ← prove
   r"(!x y:N word.
        val(word_add (word_add x y) (word 1)) <= val x <=>
        val(word_add (word_add x y) (word 1)) + 2 EXP dimindex(:N) =
        val x + val y + 1) /\
  (!x y:N word.
        val(word_add (word_add x y) (word 1)) <= val y <=>
        val(word_add (word_add x y) (word 1)) + 2 EXP dimindex(:N) =
        val x + val y + 1)"
   WORD_ARITH_TAC

  let WORD_ADC_LE_INEXACT ← prove
   r"(!x y:N word.
        val(word_add (word_add x y) (word 1)) <= val x <=>
        ~(val(word_add (word_add x y) (word 1)) = val x + val y + 1)) /\
  (!x y:N word.
        val(word_add (word_add x y) (word 1)) <= val y <=>
        ~(val(word_add (word_add x y) (word 1)) = val x + val y + 1))"
   WORD_ARITH_TAC

  -- @@RETURN BEGIN
  return { WORD_WORD_OPERATION_CONV, IVAL_TOPFLIP_VAL, WORD_ULE_TOPFLIP,
           WORD_ULT_TOPFLIP, WORD_UGE_TOPFLIP, WORD_UGT_TOPFLIP, WORD_ILT_TOPFLIP,
           WORD_ILE_TOPFLIP, WORD_IGT_TOPFLIP, WORD_IGE_TOPFLIP, WORD_LE_ADD_EXACT,
           WORD_ADD_LT_EXACT, WORD_ADD_LT_INEXACT, WORD_LT_ADC_EXACT, WORD_ADC_LE_EXACT,
           WORD_ADC_LE_INEXACT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Conversion for explicit numeric bits of word operations, one level.       -/
/- For example BIT_WORD_CONV `bit 7 (word_sub x y:int16)`                    -/
/- ------------------------------------------------------------------------- -/

structure BitWordConv where
  -- @@FIELDS
  BIT_WORD_CONV : ioconv
  deriving Inhabited

@[nospecialize]
def setupBitWordConv [HolBase] (D : WordsDeps) (BWordType : WordType) (BVal : Val) (BWordOps1 : WordOps1) (BWordOps2 : WordOps2) (BWordOps3 : WordOps3) (BZxSx : ZxSx) (BJoinSubword : JoinSubword) (BInsertDup : InsertDup) (BBitRec : BitRec) (BMasks : Masks) (BReverse : Reverse) :
    ExceptT String IO BitWordConv := do
  -- @@SCOPE BEGIN
  let { NUM_ADD_CONV, NUM_DIV_CONV, NUM_EQ_CONV, NUM_EXP_CONV, NUM_LE_CONV,
        NUM_LT_CONV, NUM_MIN_CONV, NUM_MOD_CONV, NUM_ODD_CONV, NUM_RED_CONV,
        NUM_SUB_CONV, num_CONV, .. } := D
  let { ADD1, AND_CLAUSES, COND_CLAUSES, CONJ_ASSOC, .. } := D.core1
  let { BIT_TRIVIAL, .. } := BWordType
  let { BIT_WORD, BIT_WORD_0, BIT_WORD_1, BIT_WORD_BITVAL, .. } := BVal
  let { BIT_WORD_AND_ALT, BIT_WORD_NOT, BIT_WORD_OR_ALT, BIT_WORD_XOR_ALT, .. } := BWordOps1
  let { BIT_WORD_SHL, .. } := BWordOps2
  let { BIT_WORD_ISHR, BIT_WORD_ROL, BIT_WORD_ROR, BIT_WORD_USHR, .. } := BWordOps3
  let { BIT_WORD_SXFROM, BIT_WORD_ZX, .. } := BZxSx
  let { BIT_WORD_JOIN, BIT_WORD_SUBWORD, .. } := BJoinSubword
  let { BIT_WORD_DUPLICATE, BIT_WORD_INSERT, .. } := BInsertDup
  let { BIT_WORD_ADD_CLAUSES, BIT_WORD_NEG_CLAUSES, BIT_WORD_SUB_CLAUSES, .. } := BBitRec
  let { BIT_WORD_MASK, BIT_WORD_SX, .. } := BMasks
  let { BIT_WORD_BYTEREVERSE, BIT_WORD_REVERSEFIELDS, .. } := BReverse
  -- @@SCOPE END
  let BIT_WORD_CONV : ioconv ← do
    let pth_ror ← prove
     r"bit i (word_ror (w:N word) n) <=>
          (\m. (\s. if s < dimindex(:N) then bit s w
                    else i < dimindex(:N) /\ bit (s - dimindex(:N)) w)
               (i + m))
          (n MOD dimindex(:N))"
     (REWRITE_TAC [BIT_WORD_ROR])
    let pth_rol ← prove
     r"bit i (word_rol (w:N word) n) <=>
          (\m. if i < m then bit (i + dimindex(:N) - m) w
               else i < dimindex(:N) /\ bit (i - m) w)
          (n MOD dimindex(:N))"
     (REWRITE_TAC [BIT_WORD_ROL])
    let rule_add_th ← prove
     r"n = SUC m
     ==> (bit n (word_add x y:N word) <=>
          n < dimindex(:N) /\
          ((bit n x <=> bit n y) <=>
           bit m x /\ bit m y \/
           (bit m x \/ bit m y) /\ ~bit m (word_add x y)))"
     (SIMP_TAC [← REWRITE_RULE [← GSYM ADD1] BIT_WORD_ADD_CLAUSES])
    let rule_sub_th ← prove
     r"n = SUC m
     ==> (bit n (word_sub x y:N word) <=>
          n < dimindex(:N) /\
          ((bit n x <=> bit n y) <=>
           ~bit m x /\ bit m y \/
           (~bit m x \/ bit m y) /\ bit m (word_sub x y)))"
     (SIMP_TAC [← REWRITE_RULE [← GSYM ADD1] BIT_WORD_SUB_CLAUSES])
    let rule_neg_th ← prove
     r"n = SUC m
     ==> (bit n (word_neg x:N word) <=>
          n < dimindex(:N) /\
          (bit n x <=> ~bit m x /\ ~bit m (word_neg x)))"
     (SIMP_TAC [← REWRITE_RULE [← GSYM ADD1] BIT_WORD_NEG_CLAUSES])
    let conv_shl ← GEN_REWRITE_CONV_NET id [← REWRITE_RULE [CONJ_ASSOC] BIT_WORD_SHL]
    let conv_ror ← GEN_REWRITE_CONV_NET id [pth_ror]
    let conv_rol ← GEN_REWRITE_CONV_NET id [pth_rol]
    let conv_cond_t ← GEN_REWRITE_CONV_NET id [← CONJUNCT1 (← SPEC_ALL COND_CLAUSES)]
    let conv_cond_f ← GEN_REWRITE_CONV_NET id [← CONJUNCT2 (← SPEC_ALL COND_CLAUSES)]
    let conv_and ← GEN_REWRITE_CONV_NET id [AND_CLAUSES]
    let conv_and_t ← GEN_REWRITE_CONV_NET id [← CONJUNCT1 (← SPEC_ALL AND_CLAUSES)]
    let some and3 := (CONJUNCTS (← SPEC_ALL AND_CLAUSES))[2]? | throw "el"
    let conv_and_f ← GEN_REWRITE_CONV_NET id [and3]
    let zero_tm ← q "0"
    let one_tm ← q "1"
    let isNum := HolMath.Nums.is_numeral
    pure (fun tm => ExceptT.run do
      -- `!word_SIZE_CONV` is read when a call is made.
      let sz ← D.word_SIZE_CONV.get
      let run (c : ioconv) : ExceptT String IO thm := ExceptT.mk (c tm)
      let szlt := RAND_CONV sz THENC NUM_LT_CONV
      let trivial (n x : term) : ExceptT String IO thm := do
        let th ← ISPECL [x, n] BIT_TRIVIAL
        let tm' ← liftExcept (lhand (concl th))
        let ath ← ExceptT.mk ((LAND_CONV sz THENC NUM_LE_CONV) tm')
        tryCatch (do MP th (← EQT_ELIM ath))
          (fun _ => throw "BIT_WORD_CONV: no change")
      match tm with
      | .Comb (.Comb (.Const "bit" _) n) x =>
        let nn := isNum n
        match x with
        | .Comb (.Const "word" _) (.Comb (.Const "bitval" _) _) =>
          if nn then
            run (GEN_REWRITE_CONV id [BIT_WORD_BITVAL] THENC
                 LAND_CONV NUM_EQ_CONV THENC conv_and)
          else trivial n x
        | .Comb (.Const "word" _) m =>
          if nn && isNum m then
            if m == zero_tm then
              run (GEN_REWRITE_CONV id [BIT_WORD_0])
            else if m == one_tm then
              run (GEN_REWRITE_CONV id [BIT_WORD_1] THENC NUM_EQ_CONV)
            else
              run (GEN_REWRITE_CONV id [BIT_WORD] THENC
                   binop2ConvIO (RAND_CONV sz THENC NUM_LT_CONV)
                                (RAND_CONV (RAND_CONV NUM_EXP_CONV THENC
                                            NUM_DIV_CONV) THENC
                                 NUM_ODD_CONV) THENC
                   conv_and)
          else if nn && m == one_tm then
            run (GEN_REWRITE_CONV id [BIT_WORD_1] THENC NUM_EQ_CONV)
          else trivial n x
        | .Comb (.Const "word_not" _) _ =>
          if nn then
            run (GEN_REWRITE_CONV id [BIT_WORD_NOT] THENC
                 LAND_CONV szlt THENC conv_and)
          else trivial n x
        | .Comb (.Comb (.Const "word_and" _) _) _ =>
          if nn then run (GEN_REWRITE_CONV id [BIT_WORD_AND_ALT]) else trivial n x
        | .Comb (.Comb (.Const "word_or" _) _) _ =>
          if nn then run (GEN_REWRITE_CONV id [BIT_WORD_OR_ALT]) else trivial n x
        | .Comb (.Comb (.Const "word_xor" _) _) _ =>
          if nn then run (GEN_REWRITE_CONV id [BIT_WORD_XOR_ALT]) else trivial n x
        | .Comb (.Comb (.Const "word_add" _) _) _ =>
          if nn then
            if n == zero_tm then
              run (GEN_REWRITE_CONV id [← CONJUNCT1 BIT_WORD_ADD_CLAUSES])
            else
              run (GEN_REWRITE_CONV id [← MATCH_MP rule_add_th (← ExceptT.mk (num_CONV n))] THENC
                   LAND_CONV szlt THENC conv_and)
          else trivial n x
        | .Comb (.Comb (.Const "word_sub" _) _) _ =>
          if nn then
            if n == zero_tm then
              run (GEN_REWRITE_CONV id [← CONJUNCT1 BIT_WORD_SUB_CLAUSES])
            else
              run (GEN_REWRITE_CONV id [← MATCH_MP rule_sub_th (← ExceptT.mk (num_CONV n))] THENC
                   LAND_CONV szlt THENC conv_and)
          else trivial n x
        | .Comb (.Const "word_neg" _) (.Comb (.Const "word" _) (.Comb (.Const "bitval" _) _)) =>
          if nn then
            run (GEN_REWRITE_CONV id [BIT_WORD_MASK] THENC
                 LAND_CONV szlt THENC conv_and)
          else trivial n x
        | .Comb (.Const "word_neg" _) _ =>
          if nn then
            if n == zero_tm then
              run (GEN_REWRITE_CONV id [← CONJUNCT1 BIT_WORD_NEG_CLAUSES])
            else
              run (GEN_REWRITE_CONV id [← MATCH_MP rule_neg_th (← ExceptT.mk (num_CONV n))] THENC
                   LAND_CONV szlt THENC conv_and)
          else trivial n x
        | .Comb (.Comb (.Const "word_shl" _) _) m =>
          if nn && isNum m then
            run (conv_shl THENC
                 binop2ConvIO (binop2ConvIO NUM_LE_CONV szlt THENC conv_and)
                              (LAND_CONV NUM_SUB_CONV) THENC
                 conv_and)
          else trivial n x
        | .Comb (.Comb (.Const "word_ushr" _) _) m =>
          if nn && isNum m then
            run (GEN_REWRITE_CONV id [BIT_WORD_USHR] THENC LAND_CONV NUM_ADD_CONV)
          else trivial n x
        | .Comb (.Comb (.Const "word_ishr" _) _) m =>
          if nn && isNum m then
            run (GEN_REWRITE_CONV id [BIT_WORD_ISHR] THENC
                 RATOR_CONV (LAND_CONV
                   (binop2ConvIO NUM_ADD_CONV sz THENC NUM_LT_CONV)) THENC
                 ((conv_cond_t THENC LAND_CONV NUM_ADD_CONV) ORELSEC
                  (conv_cond_f THENC
                   COMB2_CONV
                     (RAND_CONV szlt)
                     (LAND_CONV (LAND_CONV sz THENC NUM_SUB_CONV)) THENC
                   conv_and)))
          else trivial n x
        | .Comb (.Comb (.Const "word_ror" _) _) m =>
          if nn && isNum m then
            run (conv_ror THENC
                 RAND_CONV (RAND_CONV sz THENC NUM_MOD_CONV) THENC
                 BETA_CONV THENC RAND_CONV NUM_ADD_CONV THENC BETA_CONV THENC
                 RATOR_CONV (LAND_CONV szlt) THENC
                 (conv_cond_t ORELSEC
                  (conv_cond_f THENC
                   LAND_CONV szlt THENC
                   ((conv_and_t THENC
                     LAND_CONV (RAND_CONV sz THENC NUM_SUB_CONV)) ORELSEC
                    conv_and_f))))
          else trivial n x
        | .Comb (.Comb (.Const "word_rol" _) _) m =>
          if nn && isNum m then
            run (conv_rol THENC
                 RAND_CONV (RAND_CONV sz THENC NUM_MOD_CONV) THENC
                 BETA_CONV THENC
                 RATOR_CONV (LAND_CONV NUM_LT_CONV) THENC
                 ((conv_cond_t THENC
                   LAND_CONV (RAND_CONV
                    (LAND_CONV sz THENC NUM_SUB_CONV) THENC
                   NUM_ADD_CONV)) ORELSEC
                  (conv_cond_f THENC
                   LAND_CONV szlt THENC
                   ((conv_and_t THENC
                     LAND_CONV NUM_SUB_CONV) ORELSEC
                    conv_and_f))))
          else trivial n x
        | .Comb (.Const "word_zx" _) _ =>
          if nn then
            run (GEN_REWRITE_CONV id [BIT_WORD_ZX] THENC
                 LAND_CONV szlt THENC
                 (conv_and_f ORELSEC conv_and_t))
          else trivial n x
        | .Comb (.Const "word_sx" _) _ =>
          if nn then
            run (GEN_REWRITE_CONV id [BIT_WORD_SX] THENC
                 LAND_CONV szlt THENC
                 (conv_and_f ORELSEC
                  (conv_and_t THENC
                   LAND_CONV (RAND_CONV
                     (LAND_CONV sz THENC NUM_SUB_CONV) THENC
                     NUM_MIN_CONV))))
          else trivial n x
        | .Comb (.Comb (.Const "word_sxfrom" _) i) _ =>
          if nn && isNum i then
            run (GEN_REWRITE_CONV id [BIT_WORD_SXFROM] THENC
                 LAND_CONV szlt THENC
                 (conv_and_f ORELSEC
                  (conv_and_t THENC LAND_CONV NUM_MIN_CONV)))
          else trivial n x
        | .Comb (.Comb (.Const "word_join" _) _) _ =>
          if nn then
            run (GEN_REWRITE_CONV id [BIT_WORD_JOIN] THENC
                 LAND_CONV szlt THENC
                 (conv_and_f ORELSEC
                  (conv_and_t THENC
                   RATOR_CONV (LAND_CONV szlt) THENC
                   (conv_cond_t ORELSEC
                    (conv_cond_f THENC
                     LAND_CONV (RAND_CONV sz THENC NUM_SUB_CONV))))))
          else trivial n x
        | .Comb (.Comb (.Const "word_subword" _) _) (.Comb (.Comb (.Const "," _) p) q') =>
          if nn && isNum p && isNum q' then
            run (GEN_REWRITE_CONV id [BIT_WORD_SUBWORD] THENC
                 LAND_CONV
                  (RAND_CONV (RAND_CONV sz THENC NUM_MIN_CONV) THENC
                   NUM_LT_CONV) THENC
                 ((conv_and_t THENC
                    LAND_CONV NUM_ADD_CONV) ORELSEC
                   conv_and_f))
          else trivial n x
        | .Comb (.Const "word_bytereverse" _) _ =>
          if nn then
            run (GEN_REWRITE_CONV id [BIT_WORD_BYTEREVERSE] THENC
                 binop2ConvIO (DEPTH_CONV (sz ORELSEC NUM_RED_CONV))
                  (LAND_CONV (DEPTH_CONV (sz ORELSEC NUM_RED_CONV))) THENC
                 (conv_and_t ORELSEC conv_and_f))
          else trivial n x
        | .Comb (.Comb (.Const "word_reversefields" _) b) _ =>
          if nn && isNum b then
            run (GEN_REWRITE_CONV id [BIT_WORD_REVERSEFIELDS] THENC
                 binop2ConvIO (DEPTH_CONV (sz ORELSEC NUM_RED_CONV))
                  (LAND_CONV (DEPTH_CONV (sz ORELSEC NUM_RED_CONV))) THENC
                 (conv_and_t ORELSEC conv_and_f))
          else trivial n x
        | .Comb (.Comb (.Comb (.Const "word_insert" _) _)
                       (.Comb (.Comb (.Const "," _) pos) len)) _ =>
          if nn && isNum pos && isNum len then
            run (GEN_REWRITE_CONV id [BIT_WORD_INSERT] THENC
                 LAND_CONV (DEPTH_CONV (sz ORELSEC NUM_RED_CONV)) THENC
                 (conv_and_f ORELSEC
                  (conv_and_t THENC
                   RATOR_CONV (LAND_CONV (DEPTH_CONV NUM_RED_CONV)) THENC
                   (conv_cond_f ORELSEC
                    (conv_cond_t THENC LAND_CONV NUM_SUB_CONV)))))
          else trivial n x
        | .Comb (.Const "word_duplicate" _) _ =>
          if nn then
            run (GEN_REWRITE_CONV id [BIT_WORD_DUPLICATE] THENC
                 LAND_CONV szlt THENC
                 (conv_and_f ORELSEC
                  (conv_and_t THENC
                   LAND_CONV (RAND_CONV sz THENC NUM_MOD_CONV))))
          else trivial n x
        | _ => trivial n x
      | _ => throw "BIT_WORD_CONV: not of expected form")

  -- @@RETURN BEGIN
  return { BIT_WORD_CONV }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- A kind of bit-blasting, but with just arithmetic not SAT at the base.     -/
/- Subadditivity (and a bit more) of popcount.                               -/
/- ------------------------------------------------------------------------- -/

structure Blast where
  -- @@FIELDS
  WORD_BLAST : term → ExceptT String IO thm
  WORD_POPCOUNT_ADD_OR : thm
  WORD_POPCOUNT_ADD : thm
  WORD_POPCOUNT_MUL : thm
  WORD_ODDPARITY_POPCOUNT : thm
  WORD_EVENPARITY_POPCOUNT : thm
  deriving Inhabited

@[nospecialize]
def setupBlast [HolBase] (D : WordsDeps) (BBitval : Bitval) (BVal : Val) (BPopcount : Popcount) (BWordOps1 : WordOps1) (BWordOps3 : WordOps3) (BWordRule : WordRule) (BValExpand : ValExpand) (BZxSx : ZxSx) (BBitRec : BitRec) (BMisc1 : Misc1) (BMasks : Masks) (BBitWordConv : BitWordConv) :
    ExceptT String IO Blast := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, INTEGER_RULE, INT_ARITH_TAC, INT_REDUCE_CONV, INT_RING, MESON_TAC,
        NUM_REDUCE_CONV, REAL_ARITH, REAL_ARITH_TAC, mk_intconst, .. } := D
  let { ADD_EQ_0, ADD_SUB, ARITH, ARITH_EQ, CONG, DIMINDEX_1, DIVIDES_MOD, DIV_EQ_0, .. } := D.core1
  let { FINITE_NUMSEG_LT, IMP_CONJ_ALT, INT_OF_NUM_CLAUSES, INT_OF_NUM_POW,
        INT_OF_NUM_REM, INT_SUB_0, .. } := D.core2
  let { LE_0, LE_ADD2, LE_REFL, LE_TRANS, LT, MULT_CLAUSES, NOT_ODD,
        NSUM_CLAUSES_NUMSEG_LT, NUMSEG_LT_DIMINDEX, .. } := D.core3
  let { REAL_OF_INT_CLAUSES, REAL_OF_NUM_ADD, REAL_OF_NUM_CLAUSES, REAL_OF_NUM_LE,
        REAL_OF_NUM_SUM, REAL_SUB_LE, RIGHT_ADD_DISTRIB, SUM_ADD, SUM_DIFFS_ALT,
        SUM_LMUL, SUM_SUB, num_INDUCTION, .. } := D.core4
  let { BINT_POLY_CONV, BITVAL_CLAUSES, INT_BITVAL_AND, INT_BITVAL_IFF, INT_BITVAL_IMP,
        INT_BITVAL_NOT, INT_BITVAL_OR, .. } := BBitval
  let { BIT_LSB_WORD, VAL_EQ, WORD_VAL, .. } := BVal
  let { WORD_POPCOUNT_0, WORD_POPCOUNT_LE_BITS, WORD_POPCOUNT_NSUM, word_evenparity,
        word_oddparity, .. } := BPopcount
  let { BIT_WORD_AND, BIT_WORD_NOT, BIT_WORD_OR, BIT_WORD_XOR, WORD_ADD,
        WORD_POPCOUNT_OR, .. } := BWordOps1
  let { WORD_POPCOUNT_SHL, .. } := BWordOps3
  let { WORD_VAL_CONG_CONV, .. } := BWordRule
  let { VAL_EXPAND_CONV, .. } := BValExpand
  let { WORD_ZX_BITVAL, .. } := BZxSx
  let { BIT_WORD_ADD, .. } := BBitRec
  let { WORD_POPCOUNT_OR_AND, .. } := BMisc1
  let { WORD_AND_MASK, WORD_MUL_EXPAND_ALT, .. } := BMasks
  let { BIT_WORD_CONV, .. } := BBitWordConv
  -- @@SCOPE END
  let WORD_BLAST : term → ExceptT String IO thm ← do
    let pth_lt ← prove
     r"~(n = 0) ==> (val x < n <=> val x DIV n = 0)"
     (SIMP_TAC [DIV_EQ_0])
    let pth_le ← prove
     r"val x <= n <=> val x DIV (n + 1) = 0"
     (REWRITE_TAC [← ARITH_RULE (← q r"x <= n <=> x < n + 1")] THEN
      SIMP_TAC [DIV_EQ_0, ADD_EQ_0, ARITH])
    let icong_lemma ← INTEGER_RULE
      (← q r"(x:int == y) (mod n) <=> (x - y == &0) (mod n)")
    let idiv_lemma ← INTEGER_RULE
      (← q r"!d. d * n = x ==> (x:int == &0) (mod n)")
    let imon_lemma ← INTEGER_RULE
      (← q r"(x:int == &0) (mod n) ==> (x * y == &0) (mod n)")
    let ipol_lemma ← INTEGER_RULE
      (← q r"(x:int == &0) (mod n) /\ (y == &0) (mod n) ==> (x + y == &0) (mod n)")
    let conv : ioconv :=
      ONCE_DEPTH_CONV VAL_EXPAND_CONV THENC
      TOP_DEPTH_CONV BIT_WORD_CONV THENC
      (← REWRITE_CONV_NET [BITVAL_CLAUSES]) THENC
      (← REWRITE_CONV_NET [← GSYM INT_OF_NUM_CLAUSES, ← GSYM INT_OF_NUM_REM]) THENC
      (← REWRITE_CONV_NET [INT_BITVAL_AND, INT_BITVAL_OR, INT_BITVAL_NOT,
                           INT_BITVAL_IMP, INT_BITVAL_IFF]) THENC
      ONCE_DEPTH_CONV
       (((← GEN_REWRITE_CONV_NET id [← GSYM INT_SUB_0]) THENC
         LAND_CONV BINT_POLY_CONV) ORELSEC
        ((← GEN_REWRITE_CONV_NET id [icong_lemma]) THENC
         RATOR_CONV (LAND_CONV BINT_POLY_CONV)))
    let conv_lt : ioconv := fun tm => ExceptT.run do
      let th ← PART_MATCH (lhand o rand) pth_lt tm
      MP th (← EQT_ELIM (← ExceptT.mk (NUM_REDUCE_CONV (← liftExcept (lhand (concl th))))))
    -- `!word_POW2SIZE_CONV` is read here, when the tactic is built.
    let pow2Conv ← D.word_POW2SIZE_CONV.get
    let tac_word : tactic :=
      CONV_TAC WORD_VAL_CONG_CONV THEN
      TRY (CONV_TAC (RAND_CONV (RAND_CONV
       ((← GEN_REWRITE_CONV_NET id [INT_OF_NUM_POW]) THENC
        RAND_CONV pow2Conv)))) THEN
      CONV_TAC conv THEN
      REPEAT
       ((MATCH_MP_TAC idiv_lemma THEN
         (fun gl => ExceptT.run do
           let (l, r) ← liftExcept (do dest_eq (← dest_exists gl.2).2)
           -- `dest_intconst r // dest_intconst(rand l)`: right argument first.
           let dn ← liftExcept (do HolMath.Int.dest_intconst (← rand l))
           let dr ← liftExcept (HolMath.Int.dest_intconst r)
           ExceptT.mk (EXISTS_TAC (← liftExcept (mk_intconst (dr / dn))) gl)) THEN
         CONV_TAC INT_REDUCE_CONV THEN HolCore.Tactics.NO_TAC) ORELSE
        (MATCH_MP_TAC ipol_lemma ORELSE MATCH_MP_TAC imon_lemma))
    let tac_num : tactic :=
      REWRITE_TAC [← GSYM VAL_EQ] THEN
      REWRITE_TAC [REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC [REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC [CONG, DIVIDES_MOD, pth_le] THEN
      CONV_TAC (ONCE_DEPTH_CONV conv_lt) THEN
      CONV_TAC conv THEN
      (INT_ARITH_TAC ORELSE CONV_TAC (fun t => (INT_RING t).run))
    pure (fun tm =>
      tryCatch (ExceptT.mk (HolCore.Tactics.prove HolBase.B tm
                  (REPEAT (GEN_TAC ORELSE CONJ_TAC) THEN (tac_word ORELSE tac_num))))
        (fun m => do
          let s ← HolCore.Printer.string_of_term tm
          throw ("WORD_BLAST `" ++ s ++ "`: " ++ m)))

  let _r1 ← REAL_ARITH
    (← q r"(x + y) - (((x + y) + w - &2 * z) + z):real = z - w")
  let _a2 ← ARITH_RULE (← q r"i < n ==> i - 1 < n")
  let _a1 ← ARITH_RULE (← q r"!x y:num. x <= y /\ a + y <= b + x ==> a <= b")
  let WORD_POPCOUNT_ADD_OR ← prove
   r"!x y:N word. word_popcount(word_add x y) <= word_popcount(word_or x y)"
   (REPEAT GEN_TAC THEN ABBREV_TAC
     (← q r"word_carryout:N word->N word->N word =
      \x y. word_or (word_and x y)
                    (word_and (word_xor x y) (word_not(word_add x y)))") THEN
    MATCH_MP_TAC _a1 THEN
    MAP_EVERY EXISTS_TAC
     [← q r"word_popcount(word_and x y:N word)",
      ← q r"word_popcount(word_carryout (x:N word) (y:N word):N word)"] THEN
    REWRITE_TAC [WORD_POPCOUNT_OR_AND] THEN CONJ_TAC THENL
     [EXPAND_TAC "word_carryout" THEN
      MATCH_MP_TAC WORD_POPCOUNT_LE_BITS THEN
      SIMP_TAC [BIT_WORD_AND, BIT_WORD_OR, BIT_WORD_XOR],
      ALL_TAC] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [WORD_POPCOUNT_NSUM] THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_LE, ← GSYM REAL_OF_NUM_ADD] THEN
    ONCE_REWRITE_TAC [← GSYM REAL_SUB_LE] THEN
    SIMP_TAC [REAL_OF_NUM_SUM, FINITE_NUMSEG_LT, ← GSYM SUM_ADD,
              ← GSYM SUM_LMUL, ← GSYM SUM_SUB, ← GSYM REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN
     (← q r"!x (y:N word) i.
      i < dimindex(:N)
      ==> &(bitval(bit i (word_add x y))):real =
          (&(bitval(bit i x)) + &(bitval(bit i y))) +
          ((if i = 0 then &0
            else &(bitval(bit (i - 1) (word_carryout x y:N word)))) -
           &2 * &(bitval(bit i (word_carryout x y))))")
    (fun th => SIMP_TAC [th]) THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "word_carryout" THEN
      REWRITE_TAC [BIT_WORD_AND, BIT_WORD_OR, BIT_WORD_NOT, BIT_WORD_XOR] THEN
      MP_TAC (← ISPECL [← q "x:N word", ← q "y:N word", ← q "i:num"] BIT_WORD_ADD) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [ADD_SUB, ADD_EQ_0, ARITH_EQ] THEN
      ASM_SIMP_TAC [_a2] THEN
      ASM_CASES_TAC (← q "i = 0") THEN ASM_REWRITE_TAC [] THEN
      SPEC_TAC (← q r"word_add x y:N word", ← q "z:N word") THEN
      CONV_TAC (fun t => (WORD_BLAST t).run),
      REWRITE_TAC [_r1]] THEN
    MP_TAC (← ISPECL
     [← q r"\i. if i = 0 then &0:real else
         &(bitval(bit (i - 1) (word_carryout (x:N word) (y:N word): N word)))",
      ← q "0", ← q r"dimindex(:N)-1"] (← GEN_ALL SUM_DIFFS_ALT)) THEN
    REWRITE_TAC [ADD_EQ_0, ARITH_EQ, NUMSEG_LT_DIMINDEX, ADD_SUB] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [LE_0] THEN REAL_ARITH_TAC)

  let WORD_POPCOUNT_ADD ← prove
   r"!x y:N word.
    word_popcount(word_add x y) <= word_popcount x + word_popcount y"
   (MESON_TAC [LE_TRANS, WORD_POPCOUNT_ADD_OR, WORD_POPCOUNT_OR])

  let WORD_POPCOUNT_MUL ← prove
   r"!x y:N word.
        word_popcount(word_mul x y) <= word_popcount x * word_popcount y"
   (REPEAT GEN_TAC THEN REWRITE_TAC [WORD_MUL_EXPAND_ALT] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [WORD_POPCOUNT_NSUM] THEN
    SPEC_TAC (← q r"dimindex(:N)", ← q "n:num") THEN MATCH_MP_TAC num_INDUCTION THEN
    REWRITE_TAC [← CONJUNCT1 LT, NSUM_CLAUSES_NUMSEG_LT] THEN
    REWRITE_TAC [WORD_POPCOUNT_0, MULT_CLAUSES, LE_REFL] THEN
    X_GEN_TAC (← q "n:num") THEN DISCH_TAC THEN REWRITE_TAC [WORD_ADD] THEN
    W (MP_TAC o PART_MATCH lhand WORD_POPCOUNT_ADD o lhand o snd) THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] LE_TRANS) THEN
    REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN MATCH_MP_TAC LE_ADD2 THEN
    ASM_REWRITE_TAC [WORD_VAL] THEN REWRITE_TAC [WORD_AND_MASK] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [MULT_CLAUSES, BITVAL_CLAUSES] THEN
    REWRITE_TAC [WORD_POPCOUNT_0, LE_REFL, WORD_POPCOUNT_SHL])

  let WORD_ODDPARITY_POPCOUNT ← prove
   r"!x:N word. word(bitval(word_oddparity x)):M word =
              word_zx(word(word_popcount x):1 word)"
   (GEN_TAC THEN REWRITE_TAC [word_oddparity] THEN
    ONCE_REWRITE_TAC [← WORD_BLAST (← q r"x:1 word = word(bitval(bit 0 x))")] THEN
    REWRITE_TAC [WORD_ZX_BITVAL, BIT_LSB_WORD])

  let WORD_EVENPARITY_POPCOUNT ← prove
   r"!x:N word. word(bitval(word_evenparity x)):M word =
              word_zx(word_not(word(word_popcount x)):1 word)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_evenparity, ← GSYM NOT_ODD] THEN
    ONCE_REWRITE_TAC [← WORD_BLAST (← q r"x:1 word = word(bitval(bit 0 x))")] THEN
    REWRITE_TAC [WORD_ZX_BITVAL, BIT_WORD_NOT, DIMINDEX_1, ARITH, BIT_LSB_WORD])

  -- @@RETURN BEGIN
  return { WORD_BLAST, WORD_POPCOUNT_ADD_OR, WORD_POPCOUNT_ADD, WORD_POPCOUNT_MUL,
           WORD_ODDPARITY_POPCOUNT, WORD_EVENPARITY_POPCOUNT }
  -- @@RETURN END

/-- The local `let rec conv` of `WORD_BIT_CONV` (words.ml 7218-7222). -/
partial def wordBitConvGo [HolBase] (conv0 conv1 num_CONV : ioconv) : ioconv := fun tm =>
  (conv0 ORELSEC
   (funpow 3 RAND_CONV num_CONV THENC
    conv1 THENC
    wordBitConvGo conv0 conv1 num_CONV)) tm

/- ------------------------------------------------------------------------- -/
/- Conversions for explicit calculations with terms of the form "word n"     -/
/- where n is a numeral. They all work for arbitrary n and whenever they     -/
/- return "word m", then that will be canonical, i.e. m < 2^wordsize.        -/
/- ------------------------------------------------------------------------- -/

structure Reduce1 where
  -- @@FIELDS
  WORD_WORD_CONV : ioconv
  WORD_IWORD_CONV : ioconv
  WORD_SATURATE_CONV : ioconv
  IWORD_SATURATE_CONV : ioconv
  WORD_VAL_CONV : ioconv
  WORD_IVAL_CONV : ioconv
  WORD_BIT_CONV : ioconv
  BIT_WORD_PMUL_CONV : ioconv
  WORD_EQ_CONV : ioconv
  WORD_ULT_CONV : ioconv
  WORD_ULE_CONV : ioconv
  WORD_UGT_CONV : ioconv
  WORD_UGE_CONV : ioconv
  WORD_ILT_CONV : ioconv
  WORD_ILE_CONV : ioconv
  WORD_IGT_CONV : ioconv
  WORD_IGE_CONV : ioconv
  WORD_ADD_CONV : ioconv
  WORD_MUL_CONV : ioconv
  WORD_SUB_CONV : ioconv
  WORD_NEG_CONV : ioconv
  WORD_UDIV_CONV : ioconv
  WORD_UMOD_CONV : ioconv
  WORD_UMAX_CONV : ioconv
  WORD_UMIN_CONV : ioconv
  WORD_IMAX_CONV : ioconv
  WORD_IMIN_CONV : ioconv
  WORD_SHL_CONV : ioconv
  WORD_USHR_CONV : ioconv
  WORD_ISHR_CONV : ioconv
  WORD_NOT_CONV : ioconv
  deriving Inhabited

@[nospecialize]
def setupReduce1 [HolBase] (D : WordsDeps) (BBitval : Bitval) (BVal : Val) (BIval : Ival) (BLimits : Limits) (BGeneralOps : GeneralOps) (BWordOps1 : WordOps1) (BWordOps2 : WordOps2) (BWordOps3 : WordOps3) (BReverse : Reverse) :
    ExceptT String IO Reduce1 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, DIMINDEX_CONV, EXPAND_NSUM_CONV, INTEGER_RULE,
        INT_ARITH, INT_DIV_CONV, INT_GE_CONV, INT_GT_CONV, INT_LE_CONV, INT_LT_CONV,
        INT_POW_CONV, INT_REM_CONV, INT_SUB_CONV, MESON, MOD_DOWN_CONV, NUM_ADD_CONV,
        NUM_DIV_CONV, NUM_EQ_CONV, NUM_EXP_CONV, NUM_GE_CONV, NUM_GT_CONV, NUM_LE_CONV,
        NUM_LT_CONV, NUM_MAX_CONV, NUM_MIN_CONV, NUM_MOD_CONV, NUM_MULT_CONV,
        NUM_ODD_CONV, NUM_SUB_CONV, num_CONV, .. } := D
  let { ADD_CLAUSES, AND_CLAUSES, ARITH_EQ, BIT0, BIT1, COND_CLAUSES, COND_SWAP, CONG,
        DIMINDEX_NONZERO, DIVISION, DIV_0, DIV_1, DIV_DIV, DIV_LE, EXP, EXP_EQ_0, .. } := D.core1
  let { GT, INT_MAX, INT_MIN, INT_OF_NUM_CLAUSES, INT_OF_NUM_SUB, INT_POW, .. } := D.core2
  let { LE_1, MOD_LE, MOD_LT, NUMERAL, NUM_OF_INT_OF_NUM, ODD, ODD_ADD, .. } := D.core3
  let { BITVAL_CLAUSES, .. } := BBitval
  let { BIT_WORD, VAL_EQ, VAL_WORD, WORD_EQ, WORD_MOD_SIZE, .. } := BVal
  let { IVAL_EQ, IWORD_EQ, WORD_IWORD, ival, iword, .. } := BIval
  let { IVAL_WORD_INT_MAX, IVAL_WORD_INT_MIN, VAL_WORD_UINT_MAX, iword_saturate,
        word_INT_MAX, word_INT_MIN, word_UINT_MAX, word_saturate, .. } := BLimits
  let { irelational2, modular, relational2, .. } := BGeneralOps
  let { VAL_WORD_NOT, word_add, word_neg, word_sub, .. } := BWordOps1
  let { IVAL_WORD_IMAX, IVAL_WORD_IMIN, VAL_WORD_UDIV, VAL_WORD_UMAX, VAL_WORD_UMIN,
        VAL_WORD_UMOD, word_mul, word_shl, .. } := BWordOps2
  let { word_ige, word_igt, word_ile, word_ilt, word_ishr, word_uge, word_ugt,
        word_ule, word_ult, word_ushr, .. } := BWordOps3
  let { BIT_WORD_PMUL, .. } := BReverse
  -- @@SCOPE END
  let isNum := HolMath.Nums.is_numeral
  let isInt := HolMath.Int.is_intconst

  let WORD_WORD_CONV : ioconv ← do
    let pth ← prove
     r"word n:N word = word(n MOD (2 EXP dimindex(:N)))"
     (REWRITE_TAC [WORD_MOD_SIZE])
    pure (fun tm => do
      match tm with
      | .Comb (.Const "word" _) t =>
        if isNum t then
          let p2 ← D.word_POW2SIZE_CONV.get
          (GEN_REWRITE_CONV id [pth] THENC
           funpow 2 RAND_CONV p2 THENC
           RAND_CONV NUM_MOD_CONV) tm
        else pure (.error "WORD_WORD_CONV")
      | _ => pure (.error "WORD_WORD_CONV"))

  let WORD_IWORD_CONV : ioconv ← pure (fun tm => do
    match tm with
    | .Comb (.Const "iword" _) t =>
      if isInt t then
        let sz ← D.word_SIZE_CONV.get
        (REWR_CONV iword THENC
         funpow 4 RAND_CONV sz THENC
         funpow 3 RAND_CONV INT_POW_CONV THENC
         funpow 2 RAND_CONV INT_REM_CONV THENC
         GEN_REWRITE_CONV RAND_CONV [NUM_OF_INT_OF_NUM]) tm
      else pure (.error "WORD_IWORD_CONV")
    | _ => pure (.error "WORD_IWORD_CONV"))

  let WORD_SATURATE_CONV : ioconv ← do
    let pth ← prove
     r"word_saturate n:N word =
        (\t. if n < t then word n else word (t - 1)) (2 EXP dimindex(:N))"
     (REWRITE_TAC [word_saturate, VAL_WORD_UINT_MAX, GT] THEN
      SIMP_TAC [← ARITH_RULE (← q r"~(m = 0) ==> (m - 1 < n <=> ~(n < m))"),
                EXP_EQ_0, ARITH_EQ, COND_SWAP, word_UINT_MAX])
    let n_tm ← q "n:num"
    let n_ty ← qty "N"
    let conv_cond_t ← GEN_REWRITE_CONV_NET id [← CONJUNCT1 (← SPEC_ALL COND_CLAUSES)]
    let conv_cond_f ← GEN_REWRITE_CONV_NET id [← CONJUNCT2 (← SPEC_ALL COND_CLAUSES)]
    pure (fun tm => ExceptT.run do
      match tm with
      | .Comb (.Const "word_saturate" (.Tyapp "fun" [_, .Tyapp "word" [nty]]))
              ntm@(.Comb (.Const "NUMERAL" _) _) =>
        let th1 ← INST [(ntm, n_tm)] (← HolLight.INST_TYPE [(nty, n_ty)] pth)
        let p2 ← D.word_POW2SIZE_CONV.get
        let th2 ← ExceptT.mk ((RAND_CONV p2 THENC BETA_CONV THENC
                   RATOR_CONV (LAND_CONV NUM_LT_CONV) THENC
                   (conv_cond_t ORELSEC
                    (conv_cond_f THENC RAND_CONV NUM_SUB_CONV)))
                  (← liftExcept (rand (concl th1))))
        TRANS th1 th2
      | _ => throw "WORD_SATURATE_CONV")

  let IWORD_SATURATE_CONV : ioconv ← do
    let _a1 ← ARITH_RULE (← q r"~(n = 0) ==> SUC(n - 1) = n")
    let _i1 ← INTEGER_RULE (← q r"&2 * x:int = n ==> (--x == x) (mod n)")
    let _n1 ← INT_ARITH (← q r"n:int > m - &1 <=> m <= n")
    let pth ← prove
     r"iword_saturate n:N word =
        (\t. if n < -- &t then word t
             else if &t <= n then word(t - 1)
             else iword n) (2 EXP (dimindex(:N) - 1))"
     (REWRITE_TAC [iword_saturate, IVAL_WORD_INT_MIN, IVAL_WORD_INT_MAX] THEN
      REWRITE_TAC [word_INT_MIN, word_INT_MAX] THEN
      REWRITE_TAC [_n1] THEN
      REWRITE_TAC [← GSYM INT_OF_NUM_CLAUSES, WORD_IWORD] THEN
      SIMP_TAC [← GSYM INT_OF_NUM_SUB, LE_1, EXP_EQ_0, ARITH_EQ] THEN
      REWRITE_TAC [← GSYM INT_OF_NUM_CLAUSES] THEN
      REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
      REWRITE_TAC [IWORD_EQ] THEN MATCH_MP_TAC _i1 THEN
      REWRITE_TAC [← GSYM (← CONJUNCT2 INT_POW)] THEN
      SIMP_TAC [DIMINDEX_NONZERO, _a1])
    let n_tm ← q "n:int"
    let n_ty ← qty "N"
    let conv_cond_t ← GEN_REWRITE_CONV_NET id [← CONJUNCT1 (← SPEC_ALL COND_CLAUSES)]
    let conv_cond_f ← GEN_REWRITE_CONV_NET id [← CONJUNCT2 (← SPEC_ALL COND_CLAUSES)]
    pure (fun tm => ExceptT.run do
      match tm with
      | .Comb (.Const "iword_saturate" (.Tyapp "fun" [_, .Tyapp "word" [nty]])) ntm =>
        if isInt ntm then
          let th1 ← INST [(ntm, n_tm)] (← HolLight.INST_TYPE [(nty, n_ty)] pth)
          let sz ← D.word_SIZE_CONV.get
          let th2 ← ExceptT.mk ((RAND_CONV
                      (RAND_CONV
                        (LAND_CONV sz THENC NUM_SUB_CONV) THENC
                       NUM_EXP_CONV) THENC
                     BETA_CONV THENC
                     RATOR_CONV (LAND_CONV INT_LT_CONV) THENC
                     (conv_cond_t ORELSEC
                      (conv_cond_f THENC
                       RATOR_CONV (LAND_CONV INT_LE_CONV) THENC
                       ((conv_cond_t THENC RAND_CONV NUM_SUB_CONV) ORELSEC
                        (conv_cond_f THENC WORD_IWORD_CONV)))))
                    (← liftExcept (rand (concl th1))))
          TRANS th1 th2
        else throw "WORD_SATURATE_CONV"
      | _ => throw "WORD_SATURATE_CONV")

  let WORD_VAL_CONV : ioconv ← pure (fun tm => do
    match tm with
    | .Comb (.Const "val" _) (.Comb (.Const "word" _) n) =>
      if isNum n then
        let sz ← D.word_SIZE_CONV.get
        (GEN_REWRITE_CONV id [VAL_WORD] THENC
         funpow 2 RAND_CONV sz THENC
         RAND_CONV NUM_EXP_CONV THENC NUM_MOD_CONV) tm
      else pure (.error "WORD_VAL_CONV")
    | _ => pure (.error "WORD_VAL_CONV"))

  let WORD_IVAL_CONV : ioconv ← do
    let pth ← prove
     r"ival(word n:N word) =
        (\v. if v < 2 EXP (dimindex (:N) - 1)
             then &v else &v - &2 pow dimindex(:N))
        (val(word n:N word))"
     (REWRITE_TAC [ival])
    let (cth1, cth2) ← CONJ_PAIR (← MESON []
      (← q r"(if T then x:int else y:int) = x /\
             (if F then x:int else y:int) = y"))
    pure (fun tm => do
      match tm with
      | .Comb (.Const "ival" _) (.Comb (.Const "word" _) n) =>
        if isNum n then
          let sz ← D.word_SIZE_CONV.get
          (GEN_REWRITE_CONV id [pth] THENC
           RAND_CONV WORD_VAL_CONV THENC
           BETA_CONV THENC
           RATOR_CONV (LAND_CONV
            (RAND_CONV (RAND_CONV
                (LAND_CONV sz THENC NUM_SUB_CONV) THENC
              NUM_EXP_CONV) THENC
             NUM_LT_CONV)) THENC
           (GEN_REWRITE_CONV id [cth1] ORELSEC
            (GEN_REWRITE_CONV id [cth2] THENC
             (RAND_CONV o RAND_CONV) sz THENC
             RAND_CONV INT_POW_CONV THENC INT_SUB_CONV))) tm
        else pure (.error "WORD_IVAL_CONV")
      | _ => pure (.error "WORD_IVAL_CONV"))

  let WORD_BIT_CONV : ioconv ← do
    let pth0 ← prove
     r"(ODD(0 DIV 2 EXP k) <=> F) /\
     (ODD(NUMERAL(BIT0 n) DIV 2 EXP 0) <=> F) /\
     (ODD(NUMERAL(BIT1 n) DIV 2 EXP 0) <=> T)"
     (REWRITE_TAC [DIV_0, ODD, EXP, DIV_1] THEN
      REWRITE_TAC [NUMERAL, BIT0, BIT1] THEN
      REWRITE_TAC [ODD, ODD_ADD])
    let pth1 ← prove
     r"(ODD(NUMERAL(BIT0 n) DIV 2 EXP SUC k) <=> ODD(NUMERAL n DIV (2 EXP k))) /\
     (ODD(NUMERAL(BIT1 n) DIV 2 EXP SUC k) <=> ODD(NUMERAL n DIV (2 EXP k)))"
     (CONJ_TAC THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV) [NUMERAL] THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [BIT0, BIT1] THEN
      REWRITE_TAC [EXP, ← GSYM DIV_DIV] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC)
    let conv0 ← GEN_REWRITE_CONV_NET id [pth0]
    let conv1 ← GEN_REWRITE_CONV_NET id [pth1]
    let conva ← GEN_REWRITE_CONV_NET id [AND_CLAUSES]
    let conv := wordBitConvGo conv0 conv1 num_CONV
    pure (fun tm => do
      match tm with
      | .Comb (.Comb (.Const "bit" _) k) (.Comb (.Const "word" _) n) =>
        if isNum k && isNum n then
          let sz ← D.word_SIZE_CONV.get
          (GEN_REWRITE_CONV id [BIT_WORD] THENC
           binop2ConvIO (RAND_CONV sz THENC NUM_LT_CONV) conv THENC
           conva) tm
        else pure (.error "WORD_BIT_CONV")
      | _ => pure (.error "WORD_BIT_CONV"))

  let BIT_WORD_PMUL_CONV : ioconv ← do
    let main_conv : ioconv :=
      RAND_CONV
       (EXPAND_NSUM_CONV THENC
        DEPTH_BINOP_CONV (← q r"(+):num->num->num")
           (binop2ConvIO
             (RAND_CONV WORD_BIT_CONV THENC (← GEN_REWRITE_CONV_NET id [BITVAL_CLAUSES]))
             (RAND_CONV (LAND_CONV NUM_SUB_CONV THENC WORD_BIT_CONV) THENC
              (← GEN_REWRITE_CONV_NET id [BITVAL_CLAUSES])) THENC
            NUM_MULT_CONV) THENC
        DEPTH_CONV NUM_ADD_CONV) THENC
      NUM_ODD_CONV
    let tF ← TAUT (← q r"F /\ p <=> F")
    let tT ← TAUT (← q r"T /\ p <=> p")
    let conv : ioconv :=
      (← GEN_REWRITE_CONV_NET id [BIT_WORD_PMUL]) THENC
      LAND_CONV (RAND_CONV DIMINDEX_CONV THENC NUM_LT_CONV) THENC
      (((← GEN_REWRITE_CONV_NET id [tT]) THENC main_conv) ORELSEC
       (← GEN_REWRITE_CONV_NET id [tF]))
    pure (fun tm => do
      match tm with
      | .Comb (.Comb (.Const "bit" _) i)
              (.Comb (.Comb (.Const "word_pmul" _) (.Comb (.Const "word" _) m))
                     (.Comb (.Const "word" _) n)) =>
        if isNum i && isNum m && isNum n then conv tm
        else pure (.error "BIT_WORD_PMUL_CONV")
      | _ => pure (.error "BIT_WORD_PMUL_CONV"))

  let relConv (goal : String) (defs : List thm) (inner tail : ioconv) :
      ExceptT String IO ioconv := do
    let pth ← prove goal (REWRITE_TAC defs)
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC BINOP_CONV inner THENC tail)

  let WORD_EQ_CONV : ioconv ← relConv
   r"word(NUMERAL m):N word = (word(NUMERAL n):N word) <=>
     val(word(NUMERAL m):N word) = val(word(NUMERAL n):N word)"
   [VAL_EQ] WORD_VAL_CONV NUM_EQ_CONV

  let WORD_ULT_CONV : ioconv ← relConv
   r"word_ult (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     val(word(NUMERAL m):N word) < val(word(NUMERAL n):N word)"
   [word_ult, relational2] WORD_VAL_CONV NUM_LT_CONV

  let WORD_ULE_CONV : ioconv ← relConv
   r"word_ule (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     val(word(NUMERAL m):N word) <= val(word(NUMERAL n):N word)"
   [word_ule, relational2] WORD_VAL_CONV NUM_LE_CONV

  let WORD_UGT_CONV : ioconv ← relConv
   r"word_ugt (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     val(word(NUMERAL m):N word) > val(word(NUMERAL n):N word)"
   [word_ugt, relational2] WORD_VAL_CONV NUM_GT_CONV

  let WORD_UGE_CONV : ioconv ← relConv
   r"word_uge (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     val(word(NUMERAL m):N word) >= val(word(NUMERAL n):N word)"
   [word_uge, relational2] WORD_VAL_CONV NUM_GE_CONV

  let WORD_ILT_CONV : ioconv ← relConv
   r"word_ilt (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     ival(word(NUMERAL m):N word) < ival(word(NUMERAL n):N word)"
   [word_ilt, irelational2] WORD_IVAL_CONV INT_LT_CONV

  let WORD_ILE_CONV : ioconv ← relConv
   r"word_ile (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     ival(word(NUMERAL m):N word) <= ival(word(NUMERAL n):N word)"
   [word_ile, irelational2] WORD_IVAL_CONV INT_LE_CONV

  let WORD_IGT_CONV : ioconv ← relConv
   r"word_igt (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     ival(word(NUMERAL m):N word) > ival(word(NUMERAL n):N word)"
   [word_igt, irelational2] WORD_IVAL_CONV INT_GT_CONV

  let WORD_IGE_CONV : ioconv ← relConv
   r"word_ige (word(NUMERAL m):N word) (word(NUMERAL n):N word) <=>
     ival(word(NUMERAL m):N word) >= ival(word(NUMERAL n):N word)"
   [word_ige, irelational2] WORD_IVAL_CONV INT_GE_CONV

  -- `!word_POW2SIZE_CONV` is read as each of the following is defined.
  let WORD_ADD_CONV : ioconv ← do
    let pth ← prove
     r"word_add (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word((NUMERAL m + NUMERAL n) MOD (2 EXP dimindex(:N)))"
     (REWRITE_TAC [word_add, modular, VAL_WORD, WORD_EQ, CONG] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC [])
    let p2 ← D.word_POW2SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RAND_CONV (binop2ConvIO NUM_ADD_CONV p2 THENC NUM_MOD_CONV))

  let WORD_MUL_CONV : ioconv ← do
    let pth ← prove
     r"word_mul (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word((NUMERAL m * NUMERAL n) MOD (2 EXP dimindex(:N)))"
     (REWRITE_TAC [word_mul, modular, VAL_WORD, WORD_EQ, CONG] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC [])
    let p2 ← D.word_POW2SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RAND_CONV (binop2ConvIO NUM_MULT_CONV p2 THENC NUM_MOD_CONV))

  let WORD_SUB_CONV : ioconv ← do
    let pth ← prove
     r"word_sub (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     (\p. word((NUMERAL m + (p - NUMERAL n MOD p)) MOD p))
     (2 EXP dimindex(:N))"
     (REWRITE_TAC [word_sub, modular, VAL_WORD, WORD_EQ, CONG] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC [])
    let p2 ← D.word_POW2SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RAND_CONV p2 THENC BETA_CONV THENC
      RAND_CONV
       (LAND_CONV
        (RAND_CONV (RAND_CONV NUM_MOD_CONV THENC NUM_SUB_CONV) THENC
         NUM_ADD_CONV) THENC
        NUM_MOD_CONV))

  let WORD_NEG_CONV : ioconv ← do
    let pth ← prove
     r"word_neg (word(NUMERAL n):N word) =
     (\p. word((p - NUMERAL n MOD p) MOD p))
     (2 EXP dimindex(:N))"
     (REWRITE_TAC [word_neg, word_sub, modular, VAL_WORD, WORD_EQ, CONG] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC [ADD_CLAUSES])
    let p2 ← D.word_POW2SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RAND_CONV p2 THENC BETA_CONV THENC
      RAND_CONV
       (LAND_CONV
        (RAND_CONV NUM_MOD_CONV THENC NUM_SUB_CONV) THENC
        NUM_MOD_CONV))

  let WORD_UDIV_CONV : ioconv ← do
    let pth ← prove
     r"word_udiv (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     (\p. word((NUMERAL m MOD p) DIV (NUMERAL n MOD p)))
     (2 EXP dimindex(:N))"
     (REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_UDIV, VAL_WORD] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC (← ARITH_RULE
       (← q r"m DIV n <= m /\ m < p ==> m DIV n < p")) THEN
      SIMP_TAC [DIV_LE, DIVISION, EXP_EQ_0, ARITH_EQ])
    let p2 ← D.word_POW2SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RAND_CONV p2 THENC BETA_CONV THENC
      RAND_CONV (BINOP_CONV NUM_MOD_CONV THENC NUM_DIV_CONV))

  let WORD_UMOD_CONV : ioconv ← do
    let pth ← prove
     r"word_umod (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     (\p. word((NUMERAL m MOD p) MOD (NUMERAL n MOD p)))
     (2 EXP dimindex(:N))"
     (REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_UMOD, VAL_WORD] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC (← ARITH_RULE
       (← q r"m MOD n <= m /\ m < p ==> m MOD n < p")) THEN
      SIMP_TAC [MOD_LE, DIVISION, EXP_EQ_0, ARITH_EQ])
    let p2 ← D.word_POW2SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RAND_CONV p2 THENC BETA_CONV THENC
      RAND_CONV (BINOP_CONV NUM_MOD_CONV THENC NUM_MOD_CONV))

  let WORD_UMAX_CONV : ioconv ← do
    let pth ← prove
     r"word_umax (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     (\p. word(MAX (NUMERAL m MOD p) (NUMERAL n MOD p)))
     (2 EXP dimindex(:N))"
     (REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_UMAX, VAL_WORD] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
      REWRITE_TAC [← ARITH_RULE (← q r"MAX a b < n <=> a < n /\ b < n")] THEN
      SIMP_TAC [DIVISION, EXP_EQ_0, ARITH_EQ])
    let p2 ← D.word_POW2SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RAND_CONV p2 THENC BETA_CONV THENC
      RAND_CONV (BINOP_CONV NUM_MOD_CONV THENC NUM_MAX_CONV))

  let WORD_UMIN_CONV : ioconv ← do
    let pth ← prove
     r"word_umin (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     (\p. word(MIN (NUMERAL m MOD p) (NUMERAL n MOD p)))
     (2 EXP dimindex(:N))"
     (REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_UMIN, VAL_WORD] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
      REWRITE_TAC [← ARITH_RULE (← q r"MIN a b < n <=> a < n \/ b < n")] THEN
      SIMP_TAC [DIVISION, EXP_EQ_0, ARITH_EQ])
    let p2 ← D.word_POW2SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RAND_CONV p2 THENC BETA_CONV THENC
      RAND_CONV (BINOP_CONV NUM_MOD_CONV THENC NUM_MIN_CONV))

  let WORD_IMAX_CONV : ioconv ← do
    let pth ← prove
     r"word_imax (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     if ival(word(NUMERAL m):N word) <= ival(word(NUMERAL n):N word)
     then word((NUMERAL n) MOD (2 EXP dimindex(:N)))
     else word((NUMERAL m) MOD (2 EXP dimindex(:N)))"
     (COND_CASES_TAC THEN
      REWRITE_TAC [← GSYM IVAL_EQ, IVAL_WORD_IMAX, WORD_MOD_SIZE] THEN
      ASM_REWRITE_TAC [INT_MAX])
    let c1 ← GEN_REWRITE_CONV_NET id [pth]
    let c2 ← GEN_REWRITE_CONV_NET id [COND_CLAUSES]
    let p2 ← D.word_POW2SIZE_CONV.get
    pure (c1 THENC
      RATOR_CONV (LAND_CONV (BINOP_CONV WORD_IVAL_CONV THENC INT_LE_CONV)) THENC
      c2 THENC
      funpow 2 RAND_CONV p2 THENC RAND_CONV NUM_MOD_CONV)

  let WORD_IMIN_CONV : ioconv ← do
    let pth ← prove
     r"word_imin (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     if ival(word(NUMERAL m):N word) <= ival(word(NUMERAL n):N word)
     then word((NUMERAL m) MOD (2 EXP dimindex(:N)))
     else word((NUMERAL n) MOD (2 EXP dimindex(:N)))"
     (COND_CASES_TAC THEN
      REWRITE_TAC [← GSYM IVAL_EQ, IVAL_WORD_IMIN, WORD_MOD_SIZE] THEN
      ASM_REWRITE_TAC [INT_MIN])
    let c1 ← GEN_REWRITE_CONV_NET id [pth]
    let c2 ← GEN_REWRITE_CONV_NET id [COND_CLAUSES]
    let p2 ← D.word_POW2SIZE_CONV.get
    pure (c1 THENC
      RATOR_CONV (LAND_CONV (BINOP_CONV WORD_IVAL_CONV THENC INT_LE_CONV)) THENC
      c2 THENC
      funpow 2 RAND_CONV p2 THENC RAND_CONV NUM_MOD_CONV)

  let WORD_SHL_CONV : ioconv ← do
    let pth ← prove
     r"word_shl (word(NUMERAL m):N word) (NUMERAL n) =
     (\p. word((NUMERAL m * 2 EXP (NUMERAL n)) MOD p))
     (2 EXP dimindex(:N))"
     (REWRITE_TAC [word_shl, WORD_EQ, VAL_WORD, CONG] THEN
      CONV_TAC MOD_DOWN_CONV THEN REFL_TAC)
    let p2 ← D.word_POW2SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RAND_CONV p2 THENC BETA_CONV THENC
      RAND_CONV
       (LAND_CONV
         (RAND_CONV NUM_EXP_CONV THENC
          NUM_MULT_CONV) THENC
        NUM_MOD_CONV))

  let WORD_USHR_CONV : ioconv ← do
    let pth ← prove
     r"word_ushr (word(NUMERAL m):N word) (NUMERAL n) =
     (\p. word((NUMERAL m MOD p) DIV (2 EXP NUMERAL n) MOD p))
     (2 EXP dimindex(:N))"
     (REWRITE_TAC [word_ushr, WORD_EQ, VAL_WORD, CONG] THEN
      CONV_TAC MOD_DOWN_CONV THEN REFL_TAC)
    let p2 ← D.word_POW2SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RAND_CONV p2 THENC BETA_CONV THENC
      RAND_CONV
       (LAND_CONV
         (binop2ConvIO NUM_MOD_CONV NUM_EXP_CONV THENC NUM_DIV_CONV) THENC
        NUM_MOD_CONV))

  let WORD_ISHR_CONV : ioconv ← do
    let pth ← prove
     r"word_ishr (word(NUMERAL m):N word) (NUMERAL n) =
     iword (ival(word(NUMERAL m):N word) div &2 pow (NUMERAL n))"
     (REWRITE_TAC [word_ishr])
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RAND_CONV (binop2ConvIO WORD_IVAL_CONV INT_POW_CONV THENC INT_DIV_CONV) THENC
      WORD_IWORD_CONV)

  let WORD_NOT_CONV : ioconv ← do
    let pth ← prove
     r"word_not(word n:N word) =
     (\p. word(p - 1 - n MOD p)) (2 EXP dimindex(:N))"
     (REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_NOT, VAL_WORD] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
      MATCH_MP_TAC (← ARITH_RULE (← q r"~(p = 0) ==> p - 1 - n < p")) THEN
      REWRITE_TAC [EXP_EQ_0, ARITH_EQ])
    pure (fun tm => do
      match tm with
      | .Comb (.Const "word_not" _) (.Comb (.Const "word" _) n) =>
        if isNum n then
          let p2 ← D.word_POW2SIZE_CONV.get
          (GEN_REWRITE_CONV id [pth] THENC
           RAND_CONV p2 THENC BETA_CONV THENC
           RAND_CONV (binop2ConvIO NUM_SUB_CONV NUM_MOD_CONV THENC
                      NUM_SUB_CONV)) tm
        else pure (.error "WORD_NOT_CONV")
      | _ => pure (.error "WORD_NOT_CONV"))

  -- @@RETURN BEGIN
  return { WORD_WORD_CONV, WORD_IWORD_CONV, WORD_SATURATE_CONV, IWORD_SATURATE_CONV,
           WORD_VAL_CONV, WORD_IVAL_CONV, WORD_BIT_CONV, BIT_WORD_PMUL_CONV,
           WORD_EQ_CONV, WORD_ULT_CONV, WORD_ULE_CONV, WORD_UGT_CONV, WORD_UGE_CONV,
           WORD_ILT_CONV, WORD_ILE_CONV, WORD_IGT_CONV, WORD_IGE_CONV, WORD_ADD_CONV,
           WORD_MUL_CONV, WORD_SUB_CONV, WORD_NEG_CONV, WORD_UDIV_CONV, WORD_UMOD_CONV,
           WORD_UMAX_CONV, WORD_UMIN_CONV, WORD_IMAX_CONV, WORD_IMIN_CONV, WORD_SHL_CONV,
           WORD_USHR_CONV, WORD_ISHR_CONV, WORD_NOT_CONV }
  -- @@RETURN END

/-- The local `let rec conv` of `WORD_AND_CONV`, `WORD_OR_CONV` and
`WORD_XOR_CONV` (words.ml 7588-7590 and twice more). -/
partial def bitwiseDigitConv [HolBase] (base_conv step_conv fix_conv : ioconv) : ioconv :=
  fun t =>
    (base_conv ORELSEC
     (step_conv THENC RAND_CONV (bitwiseDigitConv base_conv step_conv fix_conv) THENC
      fix_conv)) t

/-- The procedure `WORD_AND_CONV`, `WORD_OR_CONV` and `WORD_XOR_CONV` share
after their theorems are proved (words.ml 7578-7596): `op` is the constant
matched, `err` the failure message. -/
def bitwiseNumeralConv [HolBase] (op err : String) (pth qth : thm) (nty : hol_type)
    (WORD_WORD_CONV : ioconv) : ioconv := fun tm => ExceptT.run do
  match tm with
  | .Comb (.Comb (.Const c _) (.Comb (.Const "word" _) m)) (.Comb (.Const "word" _) n) =>
    if c == op && HolMath.Nums.is_numeral m && HolMath.Nums.is_numeral n then
      let ty ← liftExcept (do pure (type_of (← rand tm)))
      let a ← match (ty : hol_type) with
        | .Tyapp _ (a :: _) => pure a
        | _ => throw "hd"
      let th1 ← HolLight.INST_TYPE [(a, nty)] pth
      let (f, bod) ← liftExcept (dest_exists (concl th1))
      let (pth_base, th2) ← CONJ_PAIR (← ASSUME bod)
      let (pth_step, pth_trans) ← CONJ_PAIR th2
      let base_conv := GEN_REWRITE_CONV id [pth_base]
      let step_conv := GEN_REWRITE_CONV id [pth_step]
      let fix_conv := GEN_REWRITE_CONV TRY_CONV [qth]
      let conv := bitwiseDigitConv base_conv step_conv fix_conv
      let th3 ← ExceptT.mk (REWR_CONV pth_trans tm)
      let th4 ← CONV_RULE (funpow 3 RAND_CONV conv) th3
      let th5 ← PROVE_HYP th1 (← SIMPLE_CHOOSE f th4)
      CONV_RULE (RAND_CONV WORD_WORD_CONV) th5
    else throw err
  | _ => throw err

/-- The local `let rec conv` of `WORD_BITS_OF_WORD_CONV` (words.ml 8020-8023). -/
partial def bitsOfWordDigitConv [HolBase] (conv_z conv_0 conv_1 NUM_ADD_CONV : ioconv) :
    ioconv := fun t =>
  let conv := bitsOfWordDigitConv conv_z conv_0 conv_1 NUM_ADD_CONV
  (conv_z ORELSEC
   (conv_0 THENC LAND_CONV NUM_ADD_CONV THENC conv) ORELSEC
   (conv_1 THENC RAND_CONV (LAND_CONV NUM_ADD_CONV THENC conv))) t

/-- The local `let rec conv` of `WORD_POPCOUNT_CONV` (words.ml 8090-8093). -/
partial def popcountDigitConv [HolBase] (conv_z conv_0 conv_1 NUM_SUC_CONV : ioconv) :
    ioconv := fun t =>
  let conv := popcountDigitConv conv_z conv_0 conv_1 NUM_SUC_CONV
  (conv_z ORELSEC
   (conv_0 THENC conv) ORELSEC
   (conv_1 THENC RAND_CONV conv THENC NUM_SUC_CONV)) t

structure Reduce2 where
  -- @@FIELDS
  WORD_AND_CONV : ioconv
  WORD_OR_CONV : ioconv
  WORD_XOR_CONV : ioconv
  WORD_ROL_CONV : ioconv
  WORD_ROR_CONV : ioconv
  WORD_ZX_CONV : ioconv
  WORD_SX_CONV : ioconv
  WORD_SXFROM_CONV : ioconv
  WORD_CAND_CONV : ioconv
  WORD_COR_CONV : ioconv
  WORD_JOIN_CONV : ioconv
  WORD_SUBWORD_CONV : ioconv
  WORD_INSERT_CONV : ioconv
  WORD_DUPLICATE_CONV : ioconv
  WORD_BITS_OF_WORD_CONV : ioconv
  WORD_POPCOUNT_CONV : ioconv
  deriving Inhabited

@[nospecialize]
def setupReduce2 [HolBase] (D : WordsDeps) (BWordType : WordType) (BBitsOfWord : BitsOfWord) (BVal : Val) (BPopcount : Popcount) (BWordOps1 : WordOps1) (BWordOps3 : WordOps3) (BZxSx : ZxSx) (BJoinSubword : JoinSubword) (BInsertDup : InsertDup) (BReduce1 : Reduce1) :
    ExceptT String IO Reduce2 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, NUM_ADD_CONV,
        NUM_DIV_CONV, NUM_EXP_CONV, NUM_LE_CONV, NUM_MIN_CONV, NUM_MOD_CONV,
        NUM_MULT_CONV, NUM_REDUCE_CONV, NUM_SUB_CONV, NUM_SUC_CONV, mk_small_numeral,
        prove_general_recursive_function_exists, .. } := D
  let { ADD1, ADD_CLAUSES, ADD_EQ_0, AND_CLAUSES, AND_FORALL_THM, ARITH, ARITH_EQ,
        ARITH_ZERO, BINARY_INDUCT, BIT0, BIT1, CARD_CLAUSES, CARD_IMAGE_INJ,
        COND_CLAUSES, COND_ID, CONG, DIMINDEX_NONZERO, DIVISION, DIV_0, DIV_1, DIV_DIV,
        EMPTY_GSPEC, EQ_ADD_RCANCEL, EQ_SYM_EQ, EXP, EXP_EXP, EXTENSION, .. } := D.core1
  let { FINITE_EMPTY, FINITE_IMAGE, FINITE_INSERT, FORALL_AND_THM, HAS_SIZE,
        INSERT_UNION_EQ, IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_UNION, .. } := D.core2
  let { LE_0, LE_REFL, LT_IMP_LE, MOD_MOD_EXP_MIN, MOD_MOD_REFL, MOD_MULT,
        MOD_MULT_ADD, MONO_EXISTS, MULT_2, MULT_EQ_0, MULT_SYM, NOT_IN_EMPTY, NOT_SUC,
        NUMERAL, ODD, ODD_ADD, ODD_MULT, OR_CLAUSES, .. } := D.core3
  let { SING_GSPEC, SUB_0, SUB_REFL, SUC_INJ, UNION_EMPTY, num_CASES, .. } := D.core4
  let { WORD_EQ_BITS, .. } := BWordType
  let { bits_of_word, .. } := BBitsOfWord
  let { BIT_VAL, BIT_WORD, VAL_EQ, VAL_WORD, WORD_EQ, WORD_MOD_SIZE, .. } := BVal
  let { word_popcount, .. } := BPopcount
  let { BIT_WORD_AND, BIT_WORD_OR, BIT_WORD_XOR, .. } := BWordOps1
  let { WORD_ROL_MOD, WORD_ROL_SHIFTS, WORD_ROR_MOD, WORD_ROR_SHIFTS, .. } := BWordOps3
  let { VAL_WORD_ZX_GEN, WORD_CAND, WORD_COR, word_sx, word_sxfrom, .. } := BZxSx
  let { VAL_WORD_JOIN, word_subword, .. } := BJoinSubword
  let { WORD_DUPLICATE, word_insert, .. } := BInsertDup
  let { WORD_EQ_CONV, WORD_ISHR_CONV, WORD_IVAL_CONV, WORD_IWORD_CONV, WORD_SHL_CONV,
        WORD_USHR_CONV, WORD_VAL_CONV, WORD_WORD_CONV, .. } := BReduce1
  -- @@SCOPE END
  let isNum := HolMath.Nums.is_numeral
  let pgrfe (s : String) : ExceptT String IO thm := do
    ExceptT.mk (prove_general_recursive_function_exists (← q s))

  let WORD_AND_CONV : ioconv ← do
    let rf ← pgrfe
     r"?f. !m n. f m n =
                if m = 0 then 0 else if n = 0 then 0
                else (if m MOD 2 = 1 /\ n MOD 2 = 1 then 1 else 0) +
                     2 * f (m DIV 2) (n DIV 2)"
    let pth ← prove
     r"?f. ((!n. f _0 n = _0) /\ (!m. f m _0 = _0)) /\
         ((!m n. f (BIT0 m) (BIT0 n) = BIT0(f m n)) /\
          (!m n. f (BIT0 m) (BIT1 n) = BIT0(f m n)) /\
          (!m n. f (BIT1 m) (BIT0 n) = BIT0(f m n)) /\
          (!m n. f (BIT1 m) (BIT1 n) = BIT1(f m n))) /\
         (!m n. word_and (word(NUMERAL m):N word) (word(NUMERAL n)) =
                word(NUMERAL(f m n)))"
     (MP_TAC rf THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q "f:num->num->num") THEN
      DISCH_TAC THEN
      SUBGOAL_THEN
       (← q r"(!n. f 0 n = 0) /\ (!m. f m 0 = 0) /\
      (!m n. f (2 * m) (2 * n) = 2 * f m n) /\
      (!m n. f (2 * m + 1) (2 * n) = 2 * f m n) /\
      (!m n. f (2 * m) (2 * n + 1) = 2 * f m n) /\
      (!m n. f (2 * m + 1) (2 * n + 1) = 2 * f m n + 1)")
      MP_TAC THENL
       [REPEAT STRIP_TAC THEN
        FIRST_ASSUM (fun th => GEN_REWRITE_TAC LAND_CONV [th]) THEN
        REWRITE_TAC [← ARITH_RULE (← q r"(2 * n) DIV 2 = n /\ (2 * n + 1) DIV 2 = n"),
                     ← ONCE_REWRITE_RULE [MULT_SYM] MOD_MULT_ADD,
                     MOD_MULT, ADD_EQ_0, MULT_EQ_0] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC [ADD_CLAUSES, ← ARITH_RULE (← q r"1 + 2 * n = 2 * n + 1")] THEN
        REPEAT (COND_CASES_TAC THEN REWRITE_TAC []) THEN
        REWRITE_TAC [← ARITH_RULE (← q r"0 = 2 * n <=> n = 0")] THEN
        FIRST_X_ASSUM (fun th => GEN_REWRITE_TAC LAND_CONV [th]) THEN
        ASM_REWRITE_TAC [COND_ID],
        FIRST_X_ASSUM (fun _ => ALL_TAC) THEN STRIP_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [NUMERAL], ALL_TAC] THEN CONJ_TAC THENL
       [REWRITE_TAC [BIT0, BIT1] THEN ASM_REWRITE_TAC [← GSYM MULT_2, ADD1],
        REWRITE_TAC [NUMERAL]] THEN
      REWRITE_TAC [WORD_EQ_BITS, BIT_WORD_AND, BIT_WORD] THEN
      SIMP_TAC [← TAUT (← q r"(p /\ q <=> p /\ r) <=> (p ==> (q <=> r))")] THEN
      MATCH_MP_TAC BINARY_INDUCT THEN ASM_REWRITE_TAC [DIV_0, ODD] THEN
      X_GEN_TAC (← q "m:num") THEN DISCH_TAC THEN CONJ_TAC THEN
      MATCH_MP_TAC BINARY_INDUCT THEN ASM_REWRITE_TAC [DIV_0, ODD] THEN
      X_GEN_TAC (← q "n:num") THEN DISCH_THEN (fun _ => ALL_TAC) THEN CONJ_TAC THEN
      INDUCT_TAC THEN REWRITE_TAC [EXP, DIV_1, ODD_MULT, ARITH, ODD_ADD] THEN
      DISCH_TAC THEN REWRITE_TAC [← GSYM DIV_DIV] THEN
      REWRITE_TAC [← ARITH_RULE (← q r"(2 * n) DIV 2 = n /\ (2 * n + 1) DIV 2 = n"),
                   MOD_MULT, ← ONCE_REWRITE_RULE [MULT_SYM] MOD_MULT_ADD] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC)
    let qth ← prove
     r"BIT0 _0 = _0"
     (REWRITE_TAC [ARITH_ZERO])
    let nty ← qty "N"
    pure (bitwiseNumeralConv "word_and" "WORD_AND_CONV" pth qth nty WORD_WORD_CONV)

  let WORD_OR_CONV : ioconv ← do
    let rf ← pgrfe
     r"?f. !m n. f m n =
                if m = 0 then n else if n = 0 then m
                else (if m MOD 2 = 1 \/ n MOD 2 = 1 then 1 else 0) +
                     2 * f (m DIV 2) (n DIV 2)"
    let pth ← prove
     r"?f. ((!n. f _0 n = n) /\ (!m. f m _0 = m)) /\
         ((!m n. f (BIT0 m) (BIT0 n) = BIT0(f m n)) /\
          (!m n. f (BIT0 m) (BIT1 n) = BIT1(f m n)) /\
          (!m n. f (BIT1 m) (BIT0 n) = BIT1(f m n)) /\
          (!m n. f (BIT1 m) (BIT1 n) = BIT1(f m n))) /\
         (!m n. word_or (word(NUMERAL m):N word) (word(NUMERAL n)) =
                word(NUMERAL(f m n)))"
     (MP_TAC rf THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q "f:num->num->num") THEN
      DISCH_TAC THEN
      SUBGOAL_THEN
       (← q r"(!n. f 0 n = n) /\ (!m. f m 0 = m) /\
      (!m n. f (2 * m) (2 * n) = 2 * f m n) /\
      (!m n. f (2 * m + 1) (2 * n) = 2 * f m n + 1) /\
      (!m n. f (2 * m) (2 * n + 1) = 2 * f m n + 1) /\
      (!m n. f (2 * m + 1) (2 * n + 1) = 2 * f m n + 1)")
      MP_TAC THENL
       [REPEAT STRIP_TAC THEN
        FIRST_ASSUM (fun th => GEN_REWRITE_TAC LAND_CONV [th]) THEN
        REWRITE_TAC [← ARITH_RULE (← q r"(2 * n) DIV 2 = n /\ (2 * n + 1) DIV 2 = n"),
                     ← ONCE_REWRITE_RULE [MULT_SYM] MOD_MULT_ADD,
                     MOD_MULT, ADD_EQ_0, MULT_EQ_0] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC [ADD_CLAUSES, ← ARITH_RULE (← q r"1 + 2 * n = 2 * n + 1")] THEN
        REPEAT (COND_CASES_TAC THEN REWRITE_TAC []) THEN
        ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
        TRY (AP_THM_TAC THEN AP_TERM_TAC) THEN AP_TERM_TAC THEN
        FIRST_X_ASSUM (fun th => GEN_REWRITE_TAC LAND_CONV [th]) THEN
        ASM_REWRITE_TAC [COND_ID] THEN MESON_TAC [],
        FIRST_X_ASSUM (fun _ => ALL_TAC) THEN STRIP_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [NUMERAL], ALL_TAC] THEN CONJ_TAC THENL
       [REWRITE_TAC [BIT0, BIT1] THEN ASM_REWRITE_TAC [← GSYM MULT_2, ADD1],
        REWRITE_TAC [NUMERAL]] THEN
      REWRITE_TAC [WORD_EQ_BITS, BIT_WORD_OR, BIT_WORD] THEN
      SIMP_TAC [← TAUT (← q r"(p /\ q <=> p /\ r) <=> (p ==> (q <=> r))")] THEN
      MATCH_MP_TAC BINARY_INDUCT THEN ASM_REWRITE_TAC [DIV_0, ODD] THEN
      X_GEN_TAC (← q "m:num") THEN DISCH_TAC THEN CONJ_TAC THEN
      MATCH_MP_TAC BINARY_INDUCT THEN ASM_REWRITE_TAC [DIV_0, ODD] THEN
      X_GEN_TAC (← q "n:num") THEN DISCH_THEN (fun _ => ALL_TAC) THEN CONJ_TAC THEN
      INDUCT_TAC THEN REWRITE_TAC [EXP, DIV_1, ODD_MULT, ARITH, ODD_ADD] THEN
      DISCH_TAC THEN REWRITE_TAC [← GSYM DIV_DIV] THEN
      REWRITE_TAC [← ARITH_RULE (← q r"(2 * n) DIV 2 = n /\ (2 * n + 1) DIV 2 = n"),
                   MOD_MULT, ← ONCE_REWRITE_RULE [MULT_SYM] MOD_MULT_ADD] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC)
    let qth ← prove
     r"BIT0 _0 = _0"
     (REWRITE_TAC [ARITH_ZERO])
    let nty ← qty "N"
    pure (bitwiseNumeralConv "word_or" "WORD_OR_CONV" pth qth nty WORD_WORD_CONV)

  let WORD_XOR_CONV : ioconv ← do
    let rf ← pgrfe
     r"?f. !m n. f m n =
                if m = 0 then n else if n = 0 then m
                else (if m MOD 2 = 1 <=> n MOD 2 = 1 then 0 else 1) +
                     2 * f (m DIV 2) (n DIV 2)"
    let pth ← prove
     r"?f. ((!n. f _0 n = n) /\ (!m. f m _0 = m)) /\
         ((!m n. f (BIT0 m) (BIT0 n) = BIT0(f m n)) /\
          (!m n. f (BIT0 m) (BIT1 n) = BIT1(f m n)) /\
          (!m n. f (BIT1 m) (BIT0 n) = BIT1(f m n)) /\
          (!m n. f (BIT1 m) (BIT1 n) = BIT0(f m n))) /\
         (!m n. word_xor (word(NUMERAL m):N word) (word(NUMERAL n)) =
                word(NUMERAL(f m n)))"
     (MP_TAC rf THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q "f:num->num->num") THEN
      DISCH_TAC THEN
      SUBGOAL_THEN
       (← q r"(!n. f 0 n = n) /\ (!m. f m 0 = m) /\
      (!m n. f (2 * m) (2 * n) = 2 * f m n) /\
      (!m n. f (2 * m + 1) (2 * n) = 2 * f m n + 1) /\
      (!m n. f (2 * m) (2 * n + 1) = 2 * f m n + 1) /\
      (!m n. f (2 * m + 1) (2 * n + 1) = 2 * f m n)")
      MP_TAC THENL
       [REPEAT STRIP_TAC THEN
        FIRST_ASSUM (fun th => GEN_REWRITE_TAC LAND_CONV [th]) THEN
        REWRITE_TAC [← ARITH_RULE (← q r"(2 * n) DIV 2 = n /\ (2 * n + 1) DIV 2 = n"),
                     ← ONCE_REWRITE_RULE [MULT_SYM] MOD_MULT_ADD,
                     MOD_MULT, ADD_EQ_0, MULT_EQ_0] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC [ADD_CLAUSES, ← ARITH_RULE (← q r"1 + 2 * n = 2 * n + 1")] THEN
        REPEAT (COND_CASES_TAC THEN REWRITE_TAC []) THEN
        ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
        TRY (AP_THM_TAC THEN AP_TERM_TAC) THEN AP_TERM_TAC THEN
        FIRST_X_ASSUM (fun th => GEN_REWRITE_TAC LAND_CONV [th]) THEN
        ASM_REWRITE_TAC [COND_ID] THEN MESON_TAC [],
        FIRST_X_ASSUM (fun _ => ALL_TAC) THEN STRIP_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [NUMERAL], ALL_TAC] THEN CONJ_TAC THENL
       [REWRITE_TAC [BIT0, BIT1] THEN ASM_REWRITE_TAC [← GSYM MULT_2, ADD1],
        REWRITE_TAC [NUMERAL]] THEN
      REWRITE_TAC [WORD_EQ_BITS, BIT_WORD_XOR, BIT_WORD] THEN
      SIMP_TAC [← TAUT (← q r"(p /\ q <=> p /\ r) <=> (p ==> (q <=> r))")] THEN
      MATCH_MP_TAC BINARY_INDUCT THEN ASM_REWRITE_TAC [DIV_0, ODD] THEN
      X_GEN_TAC (← q "m:num") THEN DISCH_TAC THEN CONJ_TAC THEN
      MATCH_MP_TAC BINARY_INDUCT THEN ASM_REWRITE_TAC [DIV_0, ODD] THEN
      X_GEN_TAC (← q "n:num") THEN DISCH_THEN (fun _ => ALL_TAC) THEN CONJ_TAC THEN
      INDUCT_TAC THEN REWRITE_TAC [EXP, DIV_1, ODD_MULT, ARITH, ODD_ADD] THEN
      DISCH_TAC THEN REWRITE_TAC [← GSYM DIV_DIV] THEN
      REWRITE_TAC [← ARITH_RULE (← q r"(2 * n) DIV 2 = n /\ (2 * n + 1) DIV 2 = n"),
                   MOD_MULT, ← ONCE_REWRITE_RULE [MULT_SYM] MOD_MULT_ADD] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC)
    let qth ← prove
     r"BIT0 _0 = _0"
     (REWRITE_TAC [ARITH_ZERO])
    let nty ← qty "N"
    pure (bitwiseNumeralConv "word_xor" "WORD_XOR_CONV" pth qth nty WORD_WORD_CONV)

  -- `!word_SIZE_CONV` and `!word_POW2SIZE_CONV` are read as each of the
  -- following is defined.
  let WORD_ROL_CONV : ioconv ← do
    let pth ← prove
     r"word_rol (word(NUMERAL m):N word) n =
     (\n. word_or (word_shl (word(NUMERAL m):N word) n)
                  (word_ushr (word(NUMERAL m):N word) (dimindex (:N) - n)))
     (n MOD dimindex(:N))"
     (REWRITE_TAC [] THEN
      GEN_REWRITE_TAC LAND_CONV [WORD_ROL_MOD] THEN
      SIMP_TAC [WORD_ROL_SHIFTS, DIMINDEX_NONZERO, DIVISION, LT_IMP_LE])
    let sz ← D.word_SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      (RAND_CONV o RAND_CONV) sz THENC
      RAND_CONV NUM_MOD_CONV THENC NUM_REDUCE_CONV THENC
      binop2ConvIO WORD_SHL_CONV
                  ((RAND_CONV o LAND_CONV) sz THENC
                   RAND_CONV NUM_SUB_CONV THENC WORD_USHR_CONV) THENC
      WORD_OR_CONV)

  let WORD_ROR_CONV : ioconv ← do
    let pth ← prove
     r"word_ror (word(NUMERAL m):N word) n =
     (\n. word_or (word_ushr (word(NUMERAL m):N word) n)
                  (word_shl (word(NUMERAL m):N word) (dimindex (:N) - n)))
     (n MOD dimindex(:N))"
     (REWRITE_TAC [] THEN
      GEN_REWRITE_TAC LAND_CONV [WORD_ROR_MOD] THEN
      SIMP_TAC [WORD_ROR_SHIFTS, DIMINDEX_NONZERO, DIVISION, LT_IMP_LE])
    let sz ← D.word_SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      (RAND_CONV o RAND_CONV) sz THENC
      RAND_CONV NUM_MOD_CONV THENC NUM_REDUCE_CONV THENC
      binop2ConvIO WORD_USHR_CONV
                  ((RAND_CONV o LAND_CONV) sz THENC
                   RAND_CONV NUM_SUB_CONV THENC WORD_SHL_CONV) THENC
      WORD_OR_CONV)

  let WORD_ZX_CONV : ioconv ← do
    let pth ← prove
     r"(word_zx:M word->N word) (word (NUMERAL n)) =
     word (NUMERAL n MOD (2 EXP (MIN (dimindex(:M)) (dimindex(:N)))))"
     (REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_ZX_GEN, VAL_WORD] THEN
      MESON_TAC [MOD_MOD_EXP_MIN, MOD_MOD_REFL])
    let sz ← D.word_SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RAND_CONV
       (RAND_CONV
         (RAND_CONV (BINOP_CONV sz THENC
                     NUM_MIN_CONV) THENC
          NUM_EXP_CONV) THENC
        NUM_MOD_CONV))

  let WORD_SX_CONV : ioconv ← do
    let pth ← prove
     r"(word_sx:M word->N word) (word (NUMERAL n)) =
     iword(ival(word(NUMERAL n):M word))"
     (REWRITE_TAC [word_sx])
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RAND_CONV WORD_IVAL_CONV THENC
      WORD_IWORD_CONV)

  let WORD_SXFROM_CONV : ioconv ← do
    let pth ← prove
     r"word_sxfrom (NUMERAL n) (word(NUMERAL x):N word) =
      word_ishr (word_shl (word(NUMERAL x)) (dimindex (:N) - 1 - NUMERAL n))
                (dimindex (:N) - 1 - NUMERAL n)"
     (REWRITE_TAC [word_sxfrom])
    let sz ← D.word_SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      LAND_CONV (RAND_CONV
       (LAND_CONV (LAND_CONV sz THENC NUM_SUB_CONV) THENC
                  NUM_SUB_CONV) THENC
        WORD_SHL_CONV) THENC
      RAND_CONV
       (LAND_CONV (LAND_CONV sz THENC NUM_SUB_CONV) THENC
                  NUM_SUB_CONV) THENC
      WORD_ISHR_CONV)

  let WORD_CAND_CONV : ioconv ← do
    let pth ← prove
     r"word_cand (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
    if word(NUMERAL m):N word = word 0 \/
       word(NUMERAL n):N word = word 0
    then word 0 else word 1"
     (REWRITE_TAC [WORD_CAND])
    let c1 ← GEN_REWRITE_CONV_NET id [pth]
    let c2 ← GEN_REWRITE_CONV_NET id [OR_CLAUSES]
    let c3 ← GEN_REWRITE_CONV_NET id [COND_CLAUSES]
    pure (c1 THENC
      RATOR_CONV (LAND_CONV
       (BINOP_CONV WORD_EQ_CONV THENC c2)) THENC
      c3)

  let WORD_COR_CONV : ioconv ← do
    let pth ← prove
     r"word_cor (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
    if word(NUMERAL m):N word = word 0 /\
       word(NUMERAL n):N word = word 0
    then word 0 else word 1"
     (REWRITE_TAC [WORD_COR])
    let c1 ← GEN_REWRITE_CONV_NET id [pth]
    let c2 ← GEN_REWRITE_CONV_NET id [AND_CLAUSES]
    let c3 ← GEN_REWRITE_CONV_NET id [COND_CLAUSES]
    pure (c1 THENC
      RATOR_CONV (LAND_CONV
       (BINOP_CONV WORD_EQ_CONV THENC c2)) THENC
      c3)

  let WORD_JOIN_CONV : ioconv ← do
    let pth ← prove
     r"(word_join:(M)word->(N)word->(P)word)
     (word(NUMERAL m)) (word(NUMERAL n)) =
     word((2 EXP dimindex(:N) * NUMERAL m MOD 2 EXP dimindex(:M) +
           NUMERAL n MOD 2 EXP dimindex(:N)) MOD
          2 EXP dimindex(:P))"
     (REWRITE_TAC [← GSYM VAL_EQ, VAL_WORD_JOIN, VAL_WORD, MOD_MOD_REFL])
    let p2 ← D.word_POW2SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RAND_CONV
       (binop2ConvIO
          (binop2ConvIO
             (binop2ConvIO
               p2
               (RAND_CONV p2 THENC NUM_MOD_CONV) THENC
              NUM_MULT_CONV)
             (RAND_CONV p2 THENC NUM_MOD_CONV) THENC
           NUM_ADD_CONV)
          p2 THENC
        NUM_MOD_CONV))

  let WORD_SUBWORD_CONV : ioconv ← do
    let pth ← prove
     r"word_subword (word(NUMERAL m):M word) (NUMERAL p,NUMERAL q):N word =
     word((val(word(NUMERAL m):M word) DIV 2 EXP NUMERAL p) MOD
           2 EXP MIN (NUMERAL q) (dimindex (:N)))"
     (REWRITE_TAC [word_subword, ← GSYM MOD_MOD_EXP_MIN] THEN
      REWRITE_TAC [WORD_EQ, CONG, MOD_MOD_REFL])
    let sz ← D.word_SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RAND_CONV
       (binop2ConvIO
         (binop2ConvIO WORD_VAL_CONV NUM_EXP_CONV THENC NUM_DIV_CONV)
         (RAND_CONV (RAND_CONV sz THENC NUM_MIN_CONV) THENC
          NUM_EXP_CONV) THENC
        NUM_MOD_CONV))

  let WORD_INSERT_CONV : ioconv ← do
    let pth ← prove
     r"(word_insert:(M)word->num#num->(N)word->(P)word)
     (word(NUMERAL m)) (NUMERAL pos,NUMERAL len) (word(NUMERAL n)) =
     word((2 EXP (NUMERAL pos + NUMERAL len) *
           val(word(NUMERAL m):M word) DIV 2 EXP (NUMERAL pos + NUMERAL len) +
           2 EXP NUMERAL pos *
           val(word(NUMERAL n):N word) MOD 2 EXP NUMERAL len +
           val(word(NUMERAL m):M word) MOD 2 EXP NUMERAL pos) MOD
          2 EXP dimindex(:P))"
     (REWRITE_TAC [WORD_MOD_SIZE, word_insert])
    let sz ← D.word_SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RAND_CONV
       (binop2ConvIO
         (binop2ConvIO
           (binop2ConvIO (RAND_CONV NUM_ADD_CONV THENC NUM_EXP_CONV)
                        (binop2ConvIO WORD_VAL_CONV
                                 (RAND_CONV NUM_ADD_CONV THENC NUM_EXP_CONV) THENC
                         NUM_DIV_CONV) THENC
            NUM_MULT_CONV)
           (binop2ConvIO
              (binop2ConvIO NUM_EXP_CONV
                 (binop2ConvIO WORD_VAL_CONV NUM_EXP_CONV THENC NUM_MOD_CONV) THENC
                  NUM_MULT_CONV)
              (binop2ConvIO WORD_VAL_CONV NUM_EXP_CONV THENC NUM_MOD_CONV) THENC
            NUM_ADD_CONV) THENC
           NUM_ADD_CONV)
         (RAND_CONV sz THENC NUM_EXP_CONV) THENC
        NUM_MOD_CONV))

  let WORD_DUPLICATE_CONV : ioconv ← do
    let m_ty ← qty "M"
    let n_ty ← qty "N"
    let m_tm ← q "m:num"
    let k_tm ← q "k:num"
    let pth ← prove
     r"dimindex(:N) <= k * dimindex(:M)
           ==> (word_duplicate:M word->N word)(word m) =
               (\t. word((t EXP k - 1) DIV (t - 1) * m MOD t))
               (2 EXP dimindex(:M))"
     (SIMP_TAC [WORD_DUPLICATE, EXP_EXP, MULT_SYM])
    pure (fun tm => ExceptT.run do
      match tm with
      | .Comb (.Const "word_duplicate" (.Tyapp "fun" [mty, nty]))
              (.Comb (.Const "word" _) mtm@(.Comb (.Const "NUMERAL" _) _)) =>
        -- `let m = dest_word_ty mty and n = dest_word_ty nty`: left to right.
        let m ← liftExcept (dest_word_ty mty)
        let n ← liftExcept (dest_word_ty nty)
        let k := ((n + m - 1) / m).floor
        let sz ← D.word_SIZE_CONV.get
        -- `INST [..] (INST_TYPE [mk_finty m,m_ty; mk_finty n,n_ty] pth)`:
        -- the list literals are built right to left.
        let kn ← liftExcept (mk_small_numeral k)
        let fn ← ExceptT.mk (mk_finty n)
        let fm ← ExceptT.mk (mk_finty m)
        let th1 ← INST [(mtm, m_tm), (kn, k_tm)]
                    (← HolLight.INST_TYPE [(fm, m_ty), (fn, n_ty)] pth)
        let th2 ← ExceptT.mk ((binop2ConvIO
                    sz
                    (RAND_CONV sz THENC NUM_MULT_CONV) THENC
                   NUM_LE_CONV)
                  (← liftExcept (lhand (concl th1))))
        let th3 ← MP th1 (← EQT_ELIM th2)
        let th4 ← CONV_RULE (RAND_CONV
          (RAND_CONV (RAND_CONV sz THENC NUM_EXP_CONV))) th3
        let th5 ← CONV_RULE (RAND_CONV BETA_CONV) th4
        let th6 ← CONV_RULE (RAND_CONV (RAND_CONV NUM_REDUCE_CONV)) th5
        CONV_RULE (RAND_CONV WORD_WORD_CONV) th6
      | _ => throw "WORD_DUPLICATE_CONV")

  let WORD_BITS_OF_WORD_CONV : ioconv ← do
    let rf ← pgrfe
     r"?f. !i n. f i n =
                  if n = 0 then {}
             else if n MOD 2 = 1 then i INSERT f (i + 1) (n DIV 2)
             else f (i + 1) (n DIV 2)"
    let pth ← prove
     r"?f. (!i. f i _0 = {} /\
              (!n. f i (BIT0 n) = f (i + 1) n) /\
              (!n. f i (BIT1 n) = i INSERT f (i + 1) n)) /\
         (!w:N word. bits_of_word w = f 0 (val w))"
     (MP_TAC rf THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q "f:num->num->num->bool") THEN
      DISCH_TAC THEN
      GEN_REWRITE_TAC
       (LAND_CONV o BINDER_CONV o LAND_CONV o LAND_CONV o RAND_CONV)
       [← GSYM NUMERAL] THEN
      GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o RAND_CONV o BINOP_CONV o
                       BINDER_CONV o LAND_CONV o RAND_CONV)
       [BIT0, BIT1] THEN
      REWRITE_TAC [ADD1, ← GSYM MULT_2] THEN MATCH_MP_TAC (← TAUT
       (← q r"p /\ (p ==> q) ==> p /\ q")) THEN
      CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN FIRST_ASSUM (fun th =>
          GEN_REWRITE_TAC LAND_CONV [th]) THEN
        REWRITE_TAC [ADD_EQ_0, MULT_EQ_0, ARITH_EQ, ← ARITH_RULE
         (← q r"(2 * n + 1) DIV 2 = n /\ (2 * n) DIV 2 = n")] THEN
        REWRITE_TAC [MOD_MULT] THEN
        ONCE_REWRITE_TAC [MULT_SYM] THEN REWRITE_TAC [MOD_MULT_ADD] THEN
        CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC [],
        POP_ASSUM (fun _ => ALL_TAC) THEN
        REWRITE_TAC [FORALL_AND_THM] THEN STRIP_TAC] THEN
      X_GEN_TAC (← q "w:N word") THEN REWRITE_TAC [EXTENSION] THEN
      SUBGOAL_THEN
       (← q r"!k i. i IN f k (val w) <=> k <= i /\ (i - k) IN bits_of_word(w:N word)")
      MP_TAC THENL [ALL_TAC, MESON_TAC [SUB_0, LE_0]] THEN
      REWRITE_TAC [bits_of_word, BIT_VAL] THEN
      SPEC_TAC (← q r"val(w:N word)", ← q "n:num") THEN
      MATCH_MP_TAC BINARY_INDUCT THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN
      REWRITE_TAC [DIV_0, NOT_IN_EMPTY, ARITH] THEN
      X_GEN_TAC (← q "n:num") THEN DISCH_TAC THEN
      ASM_REWRITE_TAC [IN_INSERT, AND_FORALL_THM] THEN
      MAP_EVERY X_GEN_TAC [← q "k:num", ← q "i:num"] THEN
      ASM_CASES_TAC (← q "i:num = k") THEN
      ASM_REWRITE_TAC [LE_REFL, SUB_REFL, ← ARITH_RULE (← q r"~(k + 1 <= k)")] THEN
      REWRITE_TAC [EXP, DIV_1, ODD_ADD, ODD_MULT, ARITH] THEN
      ASM_CASES_TAC (← q "k:num <= i") THEN ASM_REWRITE_TAC [] THENL
       [ALL_TAC, ASM_ARITH_TAC] THEN
      ASM_CASES_TAC (← q "k + 1 <= i") THEN ASM_REWRITE_TAC [] THENL
       [ALL_TAC, ASM_ARITH_TAC] THEN
      SUBGOAL_THEN (← q r"i - k = SUC(i - (k + 1))") SUBST1_TAC THENL
       [ASM_ARITH_TAC, REWRITE_TAC [EXP, ← GSYM DIV_DIV]] THEN
      REWRITE_TAC [← ARITH_RULE (← q r"(2 * n + 1) DIV 2 = n /\ (2 * n) DIV 2 = n")])
    let nty ← qty "N"
    pure (fun tm => ExceptT.run do
      match tm with
      | .Comb (.Const "bits_of_word" _) (.Comb (.Const "word" _) n) =>
        if isNum n then
          let ty ← liftExcept (do pure (type_of (← rand tm)))
          let a ← match (ty : hol_type) with
            | .Tyapp _ (a :: _) => pure a
            | _ => throw "hd"
          let th1 ← HolLight.INST_TYPE [(a, nty)] pth
          let (f, bod) ← liftExcept (dest_exists (concl th1))
          let (pth_clauses, th2) ← CONJ_PAIR (← ASSUME bod)
          let (pth_z, pth_o) ← CONJ_PAIR (← SPEC_ALL pth_clauses)
          let (pth_0, pth_1) ← CONJ_PAIR pth_o
          let conv_z := GEN_REWRITE_CONV id [pth_z]
          let conv_0 := GEN_REWRITE_CONV id [pth_0]
          let conv_1 := GEN_REWRITE_CONV id [pth_1]
          let conv := bitsOfWordDigitConv conv_z conv_0 conv_1 NUM_ADD_CONV
          let th3 ← ExceptT.mk (REWR_CONV th2 tm)
          let th4 ← CONV_RULE (RAND_CONV (RAND_CONV WORD_VAL_CONV)) th3
          let th5 ← GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [NUMERAL] th4
          let th6 ← CONV_RULE (RAND_CONV conv) th5
          PROVE_HYP th1 (← SIMPLE_CHOOSE f th6)
        else throw "WORD_BITS_OF_WORD_CONV"
      | _ => throw "WORD_BITS_OF_WORD_CONV")

  let WORD_POPCOUNT_CONV : ioconv ← do
    let rf ← pgrfe
     r"?f. !n. f n =
                  if n = 0 then 0
             else if n MOD 2 = 1 then SUC(f (n DIV 2))
             else f (n DIV 2)"
    let pth ← prove
     r"?f. (f _0 = 0 /\
          (!n. f (BIT0 n) = f n) /\
          (!n. f (BIT1 n) = SUC(f n))) /\
         (!w:N word. word_popcount w = f (val w))"
     (MP_TAC rf THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q "f:num->num") THEN
      DISCH_TAC THEN
      GEN_REWRITE_TAC
       (LAND_CONV o LAND_CONV o LAND_CONV o RAND_CONV)
       [← GSYM NUMERAL] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o BINOP_CONV o
                       BINDER_CONV o LAND_CONV o RAND_CONV)
       [BIT0, BIT1] THEN
      REWRITE_TAC [ADD1, ← GSYM MULT_2] THEN MATCH_MP_TAC (← TAUT
       (← q r"p /\ (p ==> q) ==> p /\ q")) THEN
      CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN FIRST_ASSUM (fun th =>
          GEN_REWRITE_TAC LAND_CONV [th]) THEN
        REWRITE_TAC [ADD_EQ_0, MULT_EQ_0, ARITH_EQ, ← ARITH_RULE
         (← q r"(2 * n + 1) DIV 2 = n /\ (2 * n) DIV 2 = n")] THEN
        REWRITE_TAC [MOD_MULT] THEN
        ONCE_REWRITE_TAC [MULT_SYM] THEN REWRITE_TAC [MOD_MULT_ADD] THEN
        CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC [ADD1],
        POP_ASSUM (fun _ => ALL_TAC) THEN
        REWRITE_TAC [FORALL_AND_THM] THEN STRIP_TAC] THEN
      X_GEN_TAC (← q "w:N word") THEN REWRITE_TAC [word_popcount] THEN
      REWRITE_TAC [bits_of_word, BIT_VAL] THEN
      SUBGOAL_THEN (← q r"!n. {i | ODD(n DIV 2 EXP i)} HAS_SIZE f n") MP_TAC THENL
       [ALL_TAC, SIMP_TAC [HAS_SIZE]] THEN
      MATCH_MP_TAC BINARY_INDUCT THEN
      ASM_REWRITE_TAC [HAS_SIZE, DIV_0, ODD, EMPTY_GSPEC,
                       FINITE_EMPTY, CARD_CLAUSES] THEN
      X_GEN_TAC (← q "n:num") THEN STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"!P. {i | P i} = {i | i = 0 /\ P 0} UNION IMAGE SUC {i | P(SUC i)}")
       (fun th => ONCE_REWRITE_TAC [th])
      THENL
       [REWRITE_TAC [EXTENSION, IN_UNION, IN_ELIM_THM, IN_IMAGE] THEN
        MESON_TAC [num_CASES],
        REWRITE_TAC [EXP, DIV_1, ODD_ADD, ODD_MULT, ARITH]] THEN
      REWRITE_TAC [EMPTY_GSPEC, SING_GSPEC, ← GSYM DIV_DIV] THEN
      REWRITE_TAC [← ARITH_RULE (← q r"(2 * n + 1) DIV 2 = n /\ (2 * n) DIV 2 = n")] THEN
      REWRITE_TAC [UNION_EMPTY, INSERT_UNION_EQ] THEN
      ASM_SIMP_TAC [FINITE_INSERT, FINITE_IMAGE, CARD_CLAUSES] THEN
      REWRITE_TAC [IN_IMAGE, NOT_SUC, ADD1, EQ_ADD_RCANCEL] THEN
      ASM_SIMP_TAC [CARD_IMAGE_INJ, SUC_INJ])
    let nty ← qty "N"
    pure (fun tm => ExceptT.run do
      match tm with
      | .Comb (.Const "word_popcount" _) (.Comb (.Const "word" _) n) =>
        if isNum n then
          let ty ← liftExcept (do pure (type_of (← rand tm)))
          let a ← match (ty : hol_type) with
            | .Tyapp _ (a :: _) => pure a
            | _ => throw "hd"
          let th1 ← HolLight.INST_TYPE [(a, nty)] pth
          let (f, bod) ← liftExcept (dest_exists (concl th1))
          let (pth_clauses, th2) ← CONJ_PAIR (← ASSUME bod)
          let (pth_z, pth_o) ← CONJ_PAIR (← SPEC_ALL pth_clauses)
          let (pth_0, pth_1) ← CONJ_PAIR pth_o
          let conv_z := GEN_REWRITE_CONV id [pth_z]
          let conv_0 := GEN_REWRITE_CONV id [pth_0]
          let conv_1 := GEN_REWRITE_CONV id [pth_1]
          let conv := popcountDigitConv conv_z conv_0 conv_1 NUM_SUC_CONV
          let th3 ← ExceptT.mk (REWR_CONV th2 tm)
          let th4 ← CONV_RULE (RAND_CONV (RAND_CONV WORD_VAL_CONV)) th3
          let th5 ← GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [NUMERAL] th4
          let th6 ← CONV_RULE (RAND_CONV conv) th5
          PROVE_HYP th1 (← SIMPLE_CHOOSE f th6)
        else throw "WORD_POPCOUNT_CONV"
      | _ => throw "WORD_POPCOUNT_CONV")

  -- @@RETURN BEGIN
  return { WORD_AND_CONV, WORD_OR_CONV, WORD_XOR_CONV, WORD_ROL_CONV, WORD_ROR_CONV,
           WORD_ZX_CONV, WORD_SX_CONV, WORD_SXFROM_CONV, WORD_CAND_CONV, WORD_COR_CONV,
           WORD_JOIN_CONV, WORD_SUBWORD_CONV, WORD_INSERT_CONV, WORD_DUPLICATE_CONV,
           WORD_BITS_OF_WORD_CONV, WORD_POPCOUNT_CONV }
  -- @@RETURN END

/-- `ctza` of `WORD_CTZ_CONV` (words.ml 8123-8124), on a nonzero `n`. -/
partial def ctzA (a n : Int) : Int :=
  if n % 2 == 0 then ctzA (a + 1) (n / 2) else a

/-- `clza` of `WORD_CLZ_CONV` (words.ml 8156-8157), with `m = pow2 k`. -/
partial def clzA (m a n : Int) : Int :=
  if n < m then clzA m (a + 1) (2 * n) else a

/-- The local `let rec conv` of `WORD_PMUL_CONV` (words.ml 8241-8243): the
`try base_conv tm with Failure _ -> ...`. -/
partial def pmulGo [HolBase] (base_conv step_conv WORD_XOR_CONV : ioconv) : ioconv :=
  fun tm => do
    match ← base_conv tm with
    | .ok th => pure (.ok th)
    | .error _ =>
      (step_conv THENC RAND_CONV (pmulGo base_conv step_conv WORD_XOR_CONV) THENC
       WORD_XOR_CONV) tm

structure Reduce3 where
  -- @@FIELDS
  WORD_EVENPARITY_CONV : ioconv
  WORD_ODDPARITY_CONV : ioconv
  WORD_CTZ_CONV : ioconv
  WORD_CLZ_CONV : ioconv
  WORD_BYTEREVERSE_CONV : ioconv
  WORD_REVERSEFIELDS_CONV : ioconv
  WORD_PMUL_CONV : ioconv
  WORD_JSHL_CONV : ioconv
  WORD_JSHR_CONV : ioconv
  WORD_JUSHR_CONV : ioconv
  WORD_JROL_CONV : ioconv
  WORD_JROR_CONV : ioconv
  WORD_JDIV_CONV : ioconv
  WORD_JREM_CONV : ioconv
  word_red_conv_list : List (term × ioconv)
  WORD_RED_CONV : ioconv
  WORD_REDUCE_CONV : ioconv
  word_compute_add_convs : HolMath.Compute.compset → ExceptT String IO Unit
  WORD_COMPUTE_CONV : ioconv
  deriving Inhabited

@[nospecialize]
def setupReduce3 [HolBase] (D : WordsDeps) (BDigitsum : Digitsum) (BBitval : Bitval) (BWordType : WordType) (BVal : Val) (BPopcount : Popcount) (BGeneralOps : GeneralOps) (BClzCtz : ClzCtz) (BReverse : Reverse) (BAlign : Align) (BBitWordConv : BitWordConv) (BReduce1 : Reduce1) (BReduce2 : Reduce2) :
    ExceptT String IO Reduce3 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, EXPAND_NSUM_CONV, INT_ABS_CONV,
        INT_DIV_CONV, INT_MUL_CONV, INT_SGN_CONV, NUM_EVEN_CONV, NUM_MOD_CONV,
        NUM_MULT_CONV, NUM_ODD_CONV, NUM_REDUCE_CONV, NUM_RED_CONV, NUM_SUB_CONV,
        WEAK_CBV_CONV, add_conv, bool_compset, mk_small_numeral, set_skip, .. } := D
  let { ADD1, COND_CLAUSES, DIMINDEX_TYBIT0, EXP, .. } := D.core1
  let { FINITE_NUMSEG, IMP_CONJ, INT_MUL_ASSOC, IN_NUMSEG, .. } := D.core2
  let { LDIV_LT_EQ, LE_0, LT, MOD_LT_EQ, MULT_CLAUSES, ODD_MOD, .. } := D.core3
  let { DIGITSUM_DIV_MOD, .. } := BDigitsum
  let { BITVAL_BOUND_ALT, BITVAL_CLAUSES, BITVAL_EQ_1, .. } := BBitval
  let { WORD_EQ_BITS_ALT, .. } := BWordType
  let { BIT_WORD, VAL_EQ_0, .. } := BVal
  let { word_evenparity, word_oddparity, .. } := BPopcount
  let { imodular, .. } := BGeneralOps
  let { WORD_CLZ_0, WORD_CLZ_UNIQUE_VAL, WORD_CTZ_0, WORD_CTZ_UNIQUE_VAL, .. } := BClzCtz
  let { BIT_WORD_BYTEREVERSE, BIT_WORD_REVERSEFIELDS, WORD_PMUL_0, WORD_PMUL_STEP,
        WORD_PMUL_ZX, .. } := BReverse
  let { word_jdiv, word_jrem, word_jrol, word_jror, word_jshl, word_jshr, word_jushr, .. } := BAlign
  let { BIT_WORD_CONV, .. } := BBitWordConv
  let { IWORD_SATURATE_CONV, WORD_ADD_CONV, WORD_BIT_CONV, WORD_EQ_CONV, WORD_IGE_CONV,
        WORD_IGT_CONV, WORD_ILE_CONV, WORD_ILT_CONV, WORD_IMAX_CONV, WORD_IMIN_CONV,
        WORD_ISHR_CONV, WORD_IVAL_CONV, WORD_IWORD_CONV, WORD_MUL_CONV, WORD_NEG_CONV,
        WORD_NOT_CONV, WORD_SATURATE_CONV, WORD_SHL_CONV, WORD_SUB_CONV,
        WORD_UDIV_CONV, WORD_UGE_CONV, WORD_UGT_CONV, WORD_ULE_CONV, WORD_ULT_CONV,
        WORD_UMAX_CONV, WORD_UMIN_CONV, WORD_UMOD_CONV, WORD_USHR_CONV, WORD_VAL_CONV,
        WORD_WORD_CONV, .. } := BReduce1
  let { WORD_AND_CONV, WORD_BITS_OF_WORD_CONV, WORD_CAND_CONV, WORD_COR_CONV,
        WORD_DUPLICATE_CONV, WORD_INSERT_CONV, WORD_JOIN_CONV, WORD_OR_CONV,
        WORD_POPCOUNT_CONV, WORD_ROL_CONV, WORD_ROR_CONV, WORD_SUBWORD_CONV,
        WORD_SXFROM_CONV, WORD_SX_CONV, WORD_XOR_CONV, WORD_ZX_CONV, .. } := BReduce2
  -- @@SCOPE END
  let isNum := HolMath.Nums.is_numeral

  let WORD_EVENPARITY_CONV : ioconv ← do
    let conv :=
      (← GEN_REWRITE_CONV_NET id [word_evenparity]) THENC
      RAND_CONV WORD_POPCOUNT_CONV THENC
      NUM_EVEN_CONV
    pure (fun tm => do
      match tm with
      | .Comb (.Const "word_evenparity" _) (.Comb (.Const "word" _) n) =>
        if isNum n then conv tm else pure (.error "WORD_EVENPARITY_CONV")
      | _ => pure (.error "WORD_EVENPARITY_CONV"))

  let WORD_ODDPARITY_CONV : ioconv ← do
    let conv :=
      (← GEN_REWRITE_CONV_NET id [word_oddparity]) THENC
      RAND_CONV WORD_POPCOUNT_CONV THENC
      NUM_ODD_CONV
    pure (fun tm => do
      match tm with
      | .Comb (.Const "word_oddparity" _) (.Comb (.Const "word" _) n) =>
        if isNum n then conv tm else pure (.error "WORD_ODDPARITY_CONV")
      | _ => pure (.error "WORD_ODDPARITY_CONV"))

  let WORD_CTZ_CONV : ioconv ← do
    let pth_0 ← prove
     r"!(a:N word). val a = 0 ==> word_ctz a = dimindex(:N)"
     (SIMP_TAC [VAL_EQ_0, WORD_CTZ_0])
    let pth ← prove
     r"!(a:N word) v.
        val a = v
        ==> !n e. 2 EXP n = e /\ v MOD (2 * e) = e ==> word_ctz a = n"
     (REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REPEAT GEN_TAC THEN
      REWRITE_TAC [IMP_CONJ] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      REWRITE_TAC [← GSYM (← CONJUNCT2 EXP), ADD1] THEN
      REWRITE_TAC [WORD_CTZ_UNIQUE_VAL])
    pure (fun tm => ExceptT.run do
      match tm with
      | .Comb (.Const "word_ctz" _) (.Comb (.Const "word" _) t) =>
        if isNum t then
          let th1 ← ISPEC (← liftExcept (rand tm)) pth
          let (_, body) ← liftExcept (dest_forall (concl th1))
          let th2 ← ExceptT.mk (WORD_VAL_CONV (← liftExcept (do lhand (← lhand body))))
          let mtm ← liftExcept (rand (concl th2))
          let m ← liftExcept (dest_numeral mtm)
          if m == 0 then
            let sz ← D.word_SIZE_CONV.get
            CONV_RULE (RAND_CONV sz) (← MATCH_MP pth_0 th2)
          else
            let th3 ← MP (← SPEC mtm th1) th2
            let n := ctzA 0 m.num
            let th4 ← SPECL [← liftExcept (mk_small_numeral n),
                             ← liftExcept (mk_small_numeral (2 ^ n.toNat))] th3
            MP th4 (← EQT_ELIM (← ExceptT.mk
              (NUM_REDUCE_CONV (← liftExcept (lhand (concl th4))))))
        else throw "WORD_CTZ_CONV"
      | _ => throw "WORD_CTZ_CONV")

  let WORD_CLZ_CONV : ioconv ← do
    let pth_0 ← prove
     r"!(a:N word). val a = 0 ==> word_clz a = dimindex(:N)"
     (SIMP_TAC [VAL_EQ_0, WORD_CLZ_0])
    let pth ← prove
     r"!(a:N word) v.
        val a = v
        ==> !n d. n + 1 + d = dimindex(:N) /\ v DIV (2 EXP d) = 1
                  ==> word_clz a = n"
     (REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC WORD_CLZ_UNIQUE_VAL THEN
      CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      ASM_MESON_TAC [← ARITH_RULE (← q r"n + 1 + d = N ==> N - n - 1 = d")])
    let clz (k n : Int) : Int :=
      if n == 0 then k else min k (clzA (2 ^ k.toNat) (-1) n)
    pure (fun tm => ExceptT.run do
      match tm with
      | .Comb (.Const "word_clz" _) (.Comb (.Const "word" _) t) =>
        if isNum t then
          let th1 ← ISPEC (← liftExcept (rand tm)) pth
          let (_, body) ← liftExcept (dest_forall (concl th1))
          let th2 ← ExceptT.mk (WORD_VAL_CONV (← liftExcept (do lhand (← lhand body))))
          let mtm ← liftExcept (rand (concl th2))
          let m ← liftExcept (dest_numeral mtm)
          let sz ← D.word_SIZE_CONV.get
          if m == 0 then
            CONV_RULE (RAND_CONV sz) (← MATCH_MP pth_0 th2)
          else
            let th3 ← MP (← SPEC mtm th1) th2
            let th4 ← CONV_RULE
             (BINDER_CONV (BINDER_CONV (LAND_CONV (LAND_CONV
                 (RAND_CONV sz))))) th3
            let btm ← liftExcept (do lhand (← lhand (strip_forall (concl th4)).2))
            let e ← liftExcept (do HolMath.Nums.dest_small_numeral (← rand btm))
            let n := clz e m.num
            let d := e - (n + 1)
            let th5 ← SPECL [← liftExcept (mk_small_numeral n),
                             ← liftExcept (mk_small_numeral d)] th4
            MP th5 (← EQT_ELIM (← ExceptT.mk
              (NUM_REDUCE_CONV (← liftExcept (lhand (concl th5))))))
        else throw "WORD_CLZ_CONV"
      | _ => throw "WORD_CLZ_CONV")

  -- `!word_SIZE_CONV` is read as each of the following is defined.
  let WORD_BYTEREVERSE_CONV : ioconv ← do
    let _a2 ← ARITH_RULE (← q r"i < n ==> i <= n - 1")
    let _t1 ← TAUT (← q r"p /\ (q <=> q') ==> (p /\ q <=> q')")
    let _a1 ← ARITH_RULE (← q r"2 * 2 * 2 * n = 8 * n")
    let pth ← prove
     r"!n. word_bytereverse(word (NUMERAL n):((((N)tybit0)tybit0)tybit0)word) =
         word(nsum (0..8*dimindex(:N)-1)
               (\i. 2 EXP i *
                    bitval(ODD(NUMERAL n DIV
                        2 EXP (8 * (dimindex(:N) - 1 - i DIV 8) + i MOD 8)))))"
     (GEN_TAC THEN GEN_REWRITE_TAC id [WORD_EQ_BITS_ALT] THEN
      REWRITE_TAC [BIT_WORD_BYTEREVERSE, BIT_WORD] THEN
      REWRITE_TAC [DIMINDEX_TYBIT0, _a1] THEN
      X_GEN_TAC (← q "i:num") THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC _t1 THEN
      CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [ODD_MOD] THEN
      SIMP_TAC [DIGITSUM_DIV_MOD, FINITE_NUMSEG, BITVAL_BOUND_ALT] THEN
      ASM_SIMP_TAC [IN_NUMSEG, LE_0, _a2] THEN
      REWRITE_TAC [BITVAL_EQ_1])
    let sz ← D.word_SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      DEPTH_CONV
       (sz ORELSEC NUM_MULT_CONV ORELSEC NUM_SUB_CONV) THENC
      RAND_CONV EXPAND_NSUM_CONV THENC
      DEPTH_CONV ((← GEN_REWRITE_CONV_NET id [BITVAL_CLAUSES]) ORELSEC NUM_RED_CONV))

  let WORD_REVERSEFIELDS_CONV : ioconv ← do
    let _a2 ← ARITH_RULE (← q r"i < n ==> i <= n - 1")
    let _a1 ← ARITH_RULE (← q r"b * (x + 1) <= n /\ m < b ==> b * x + m < n")
    let _t1 ← TAUT (← q r"p /\ (q <=> q') ==> (p /\ q <=> q')")
    let pth0 ← prove
     r"!b n.
        word_reversefields b (word n:N word) =
        word(nsum (0..dimindex(:N)-1)
          (\i. 2 EXP i *
               bitval(ODD(n DIV
               2 EXP (if i < b * dimindex(:N) DIV b
                      then b * (dimindex(:N) DIV b - 1 - i DIV b) + i MOD b
                      else i)))))"
     (REPEAT GEN_TAC THEN GEN_REWRITE_TAC id [WORD_EQ_BITS_ALT] THEN
      REWRITE_TAC [BIT_WORD_REVERSEFIELDS, BIT_WORD] THEN
      X_GEN_TAC (← q "i:num") THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC _t1 THEN
      CONJ_TAC THENL
       [ASM_CASES_TAC (← q "b = 0") THEN ASM_REWRITE_TAC [MULT_CLAUSES, LT] THEN
        ASM_CASES_TAC (← q r"dimindex (:N) DIV b = 0") THEN
        ASM_REWRITE_TAC [MULT_CLAUSES, LT] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC _a1 THEN
        ASM_SIMP_TAC [MOD_LT_EQ, ← GSYM LDIV_LT_EQ] THEN ASM_ARITH_TAC,
        GEN_REWRITE_TAC RAND_CONV [ODD_MOD] THEN
        SIMP_TAC [DIGITSUM_DIV_MOD, FINITE_NUMSEG, BITVAL_BOUND_ALT] THEN
        ASM_SIMP_TAC [IN_NUMSEG, LE_0, _a2] THEN
        REWRITE_TAC [BITVAL_EQ_1]])
    -- `[`NUMERAL b`; `NUMERAL n`]`: the list literal is built right to left.
    let nn ← q "NUMERAL n"
    let nb ← q "NUMERAL b"
    let pth ← SPECL [nb, nn] pth0
    let sz ← D.word_SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      DEPTH_CONV
       (sz ORELSEC NUM_MULT_CONV ORELSEC NUM_SUB_CONV) THENC
      RAND_CONV EXPAND_NSUM_CONV THENC
      DEPTH_CONV ((← GEN_REWRITE_CONV_NET id [BITVAL_CLAUSES]) ORELSEC NUM_RED_CONV))

  let WORD_PMUL_CONV : ioconv ← do
    let in_conv :=
      (← GEN_REWRITE_CONV_NET id [← GSYM (← CONJUNCT2 WORD_PMUL_ZX)]) THENC
      RAND_CONV WORD_ZX_CONV
    let base_conv ← GEN_REWRITE_CONV_NET id [← CONJUNCT2 WORD_PMUL_0]
    let step_conv :=
      (← GEN_REWRITE_CONV_NET id [WORD_PMUL_STEP]) THENC
      binop2ConvIO
       (RATOR_CONV (LAND_CONV BIT_WORD_CONV) THENC
        (← GEN_REWRITE_CONV_NET id [COND_CLAUSES]))
       (binop2ConvIO WORD_USHR_CONV WORD_SHL_CONV)
    let conv := pmulGo base_conv step_conv WORD_XOR_CONV
    let fullconv := in_conv THENC conv
    pure (fun tm => do
      match tm with
      | .Comb (.Comb (.Const "word_pmul" _) (.Comb (.Const "word" _) m))
              (.Comb (.Const "word" _) n) =>
        if isNum m && isNum n then fullconv tm else pure (.error "WORD_PMUL_CONV")
      | _ => pure (.error "WORD_PMUL_CONV"))

  let WORD_JSHL_CONV : ioconv ← do
    let pth ← prove
     r"word_jshl (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word_shl (word(NUMERAL m):N word)
              (val(word(NUMERAL n):N word) MOD dimindex (:N))"
     (REWRITE_TAC [word_jshl])
    let sz ← D.word_SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RAND_CONV (binop2ConvIO WORD_VAL_CONV sz THENC
                 NUM_MOD_CONV) THENC
      WORD_SHL_CONV)

  let WORD_JSHR_CONV : ioconv ← do
    let pth ← prove
     r"word_jshr (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word_ishr (word(NUMERAL m):N word)
               (val(word(NUMERAL n):N word) MOD dimindex (:N))"
     (REWRITE_TAC [word_jshr])
    let sz ← D.word_SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RAND_CONV (binop2ConvIO WORD_VAL_CONV sz THENC
                 NUM_MOD_CONV) THENC
      WORD_ISHR_CONV)

  let WORD_JUSHR_CONV : ioconv ← do
    let pth ← prove
     r"word_jushr (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word_ushr (word(NUMERAL m):N word)
               (val(word(NUMERAL n):N word) MOD dimindex (:N))"
     (REWRITE_TAC [word_jushr])
    let sz ← D.word_SIZE_CONV.get
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RAND_CONV (binop2ConvIO WORD_VAL_CONV sz THENC
                 NUM_MOD_CONV) THENC
      WORD_USHR_CONV)

  let WORD_JROL_CONV : ioconv ← do
    let pth ← prove
     r"word_jrol (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word_rol (word(NUMERAL m):N word) (val(word(NUMERAL n):N word))"
     (REWRITE_TAC [word_jrol])
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC RAND_CONV WORD_VAL_CONV THENC
      WORD_ROL_CONV)

  let WORD_JROR_CONV : ioconv ← do
    let pth ← prove
     r"word_jror (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word_ror (word(NUMERAL m):N word) (val(word(NUMERAL n):N word))"
     (REWRITE_TAC [word_jror])
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC RAND_CONV WORD_VAL_CONV THENC
      WORD_ROR_CONV)

  let WORD_JDIV_CONV : ioconv ← do
    let pth ← prove
     r"word_jdiv (word(NUMERAL m):N word) (word(NUMERAL n)) =
     (\a b. iword((int_sgn a * int_sgn b) * (abs a div abs b)))
     (ival(word(NUMERAL m):N word)) (ival(word(NUMERAL n):N word))"
     (REWRITE_TAC [word_jdiv, imodular, ← GSYM INT_MUL_ASSOC])
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RATOR_CONV (RAND_CONV WORD_IVAL_CONV THENC BETA_CONV) THENC
      RAND_CONV WORD_IVAL_CONV THENC BETA_CONV THENC
      RAND_CONV (COMB2_CONV
                 (RAND_CONV (BINOP_CONV INT_SGN_CONV THENC INT_MUL_CONV))
                 (BINOP_CONV INT_ABS_CONV THENC INT_DIV_CONV) THENC
                INT_MUL_CONV) THENC
      WORD_IWORD_CONV)

  let WORD_JREM_CONV : ioconv ← do
    let pth ← prove
     r"word_jrem (word(NUMERAL m):N word) (word(NUMERAL n):N word) =
     word_sub (word (NUMERAL m))
              (word_mul (word_jdiv (word (NUMERAL m)) (word (NUMERAL n)))
                        (word (NUMERAL n)))"
     (REWRITE_TAC [word_jrem])
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC
      RAND_CONV (LAND_CONV WORD_JDIV_CONV THENC WORD_MUL_CONV) THENC
      WORD_SUB_CONV)

  -- The list literal is built right to left, so the patterns are parsed
  -- from the last to the first.
  let word_red_conv_list : List (term × ioconv) ← do
    let pairs : List (String × ioconv) :=
     [(r"word(NUMERAL n):N word", CHANGED_CONV WORD_WORD_CONV),
      (r"word_saturate(NUMERAL n):N word", WORD_SATURATE_CONV),
      (r"iword i:N word", WORD_IWORD_CONV),
      (r"iword_saturate(n):N word", IWORD_SATURATE_CONV),
      (r"val(w:N word)", WORD_VAL_CONV),
      (r"ival(w:N word)", WORD_IVAL_CONV),
      (r"bit (NUMERAL k) (word(NUMERAL n):N word)", WORD_BIT_CONV),
      (r"word(NUMERAL m):N word = word(NUMERAL n)", WORD_EQ_CONV),
      (r"word_ult (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_ULT_CONV),
      (r"word_ule (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_ULE_CONV),
      (r"word_ugt (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_UGT_CONV),
      (r"word_uge (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_UGE_CONV),
      (r"word_ilt (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_ILT_CONV),
      (r"word_ile (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_ILE_CONV),
      (r"word_igt (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_IGT_CONV),
      (r"word_ige (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_IGE_CONV),
      (r"word_neg (word(NUMERAL n):N word)", WORD_NEG_CONV),
      (r"word_add (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_ADD_CONV),
      (r"word_mul (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_MUL_CONV),
      (r"word_sub (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_SUB_CONV),
      (r"word_udiv (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_UDIV_CONV),
      (r"word_umod (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_UMOD_CONV),
      (r"word_umax (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_UMAX_CONV),
      (r"word_umin (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_UMIN_CONV),
      (r"word_imax (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_IMAX_CONV),
      (r"word_imin (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_IMIN_CONV),
      (r"word_shl (word(NUMERAL m):N word) (NUMERAL n)", WORD_SHL_CONV),
      (r"word_ushr (word(NUMERAL m):N word) (NUMERAL n)", WORD_USHR_CONV),
      (r"word_ishr (word(NUMERAL m):N word) (NUMERAL n)", WORD_ISHR_CONV),
      (r"word_not (word(NUMERAL n):N word)", WORD_NOT_CONV),
      (r"word_and (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_AND_CONV),
      (r"word_or (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_OR_CONV),
      (r"word_xor (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_XOR_CONV),
      (r"word_rol (word(NUMERAL m):N word) (NUMERAL n)", WORD_ROL_CONV),
      (r"word_ror (word(NUMERAL m):N word) (NUMERAL n)", WORD_ROR_CONV),
      (r"word_zx (word(NUMERAL n):N word)", WORD_ZX_CONV),
      (r"word_sx (word(NUMERAL n):N word)", WORD_SX_CONV),
      (r"word_sxfrom (NUMERAL m) (word(NUMERAL n):N word)", WORD_SXFROM_CONV),
      (r"word_cand (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_CAND_CONV),
      (r"word_cor (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_COR_CONV),
      (r"word_join (word(NUMERAL m):M word) (word(NUMERAL n):N word)",
                  WORD_JOIN_CONV),
      (r"word_subword (word(NUMERAL m):M word) (NUMERAL p,NUMERAL q):N word",
                  WORD_SUBWORD_CONV),
      (r"word_insert (word(NUMERAL m):M word) (NUMERAL p,NUMERAL q)
               (word(NUMERAL n):N word):P word",
                  WORD_INSERT_CONV),
      (r"word_duplicate (word(NUMERAL m):M word):N word", WORD_DUPLICATE_CONV),
      (r"bits_of_word (word(NUMERAL n):N word)", WORD_BITS_OF_WORD_CONV),
      (r"word_popcount (word(NUMERAL n):N word)", WORD_POPCOUNT_CONV),
      (r"word_evenparity (word(NUMERAL n):N word)", WORD_EVENPARITY_CONV),
      (r"word_oddparity (word(NUMERAL n):N word)", WORD_ODDPARITY_CONV),
      (r"word_ctz (word(NUMERAL n):N word)", WORD_CTZ_CONV),
      (r"word_clz (word(NUMERAL n):N word)", WORD_CLZ_CONV),
      (r"word_bytereverse (word(NUMERAL n):((((N)tybit0)tybit0)tybit0)word)",
                  WORD_BYTEREVERSE_CONV),
      (r"word_reversefields (NUMERAL b) (word(NUMERAL n):N word)",
                  WORD_REVERSEFIELDS_CONV),
      (r"(word_pmul:M word->N word->P word) (word(NUMERAL m)) (word(NUMERAL n))",
                  WORD_PMUL_CONV),
      (r"word_jshl (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_JSHL_CONV),
      (r"word_jshr (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_JSHR_CONV),
      (r"word_jushr (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_JUSHR_CONV),
      (r"word_jrol (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_JROL_CONV),
      (r"word_jror (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_JROR_CONV),
      (r"word_jdiv (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_JDIV_CONV),
      (r"word_jrem (word(NUMERAL m):N word) (word(NUMERAL n))", WORD_JREM_CONV)]
    let rev ← pairs.reverse.mapM (fun (s, c) => do pure ((← q s), c))
    pure rev.reverse

  let WORD_RED_CONV : ioconv ← do
    -- `itlist (uncurry net_of_conv) word_red_conv_list (basic_net())`: the
    -- last pair is entered first.
    let mut gconv_net ← (HolCore.Simp.basic_net : IO _)
    for (pat, c) in word_red_conv_list.reverse do
      gconv_net ← ExceptT.mk (HolCore.Simp.net_of_conv pat c gconv_net)
    let n := gconv_net
    pure (fun tm => HolCore.Simp.REWRITES_CONV n tm)

  let WORD_REDUCE_CONV : ioconv ← pure (DEPTH_CONV WORD_RED_CONV)

  let word_compute_add_convs : HolMath.Compute.compset → ExceptT String IO Unit ← do
    let convlist := word_red_conv_list.map (fun (pat, the_conv) =>
      let (c, args) := strip_comb pat
      (c, (args.length : Int), the_conv))
    -- `itlist (fun newc () -> Compute.add_conv newc compset) convlist ()`:
    -- the last entry is added first.
    pure (fun cs => do
      for (c, n, cv) in convlist.reverse do
        ExceptT.mk (add_conv c n cv cs))

  let WORD_COMPUTE_CONV : ioconv ← do
    let cs ← ExceptT.mk bool_compset
    ExceptT.mk (set_skip cs (← q "COND: bool -> A -> A -> A") (some 1))
    word_compute_add_convs cs
    pure (WEAK_CBV_CONV cs)

  -- @@RETURN BEGIN
  return { WORD_EVENPARITY_CONV, WORD_ODDPARITY_CONV, WORD_CTZ_CONV, WORD_CLZ_CONV,
           WORD_BYTEREVERSE_CONV, WORD_REVERSEFIELDS_CONV, WORD_PMUL_CONV,
           WORD_JSHL_CONV, WORD_JSHR_CONV, WORD_JUSHR_CONV, WORD_JROL_CONV,
           WORD_JROR_CONV, WORD_JDIV_CONV, WORD_JREM_CONV, word_red_conv_list,
           WORD_RED_CONV, WORD_REDUCE_CONV, word_compute_add_convs, WORD_COMPUTE_CONV }
  -- @@RETURN END

/-- `balance` of `EXPAND_NSUM_BALANCE_CONV` (words.ml 8462-8467). -/
partial def nsumBalance (op tm : term) : Except String term := do
  let tms := striplist (dest_binop op) tm
  let n := tms.length
  if n <= 3 then return tm
  let (tms1, tms2) ← chop_list (n / 2) tms
  -- `mk (balance(lmk tms1)) (balance(lmk tms2))`: right argument first.
  let b2 ← nsumBalance op (← list_mk_binop op tms2)
  let b1 ← nsumBalance op (← list_mk_binop op tms1)
  (← mk_binop op b1) b2

/-- `log2` of `WORDIFY_CONV` and `IWORDIFY_CONV`: the least `i` with
`n < 2^i`, starting from `m = 2^i`. -/
partial def wordifyLog2 (n m : Rat) (i : Int) : Int :=
  if n < m then i else wordifyLog2 n (2 * m) (i + 1)

/-- `ilog2` of `IWORDIFY_CONV` (words.ml 8834-8838). -/
partial def wordifyIlog2 (n m : Rat) (i : Int) : Int :=
  if -m <= n && n < m then i else wordifyIlog2 n (2 * m) (i + 1)

/-- equal.ml's `PAT_CONV` on `ioconv`s. -/
partial def patConvIO [HolBase] (pat : term) (c : ioconv) : ioconv :=
  let rec PCONV (xs : List term) (pat : term) : ioconv :=
    if mem pat xs then c
    else if !(exists' (fun x => free_in x pat) xs) then ALL_CONV
    else match pat with
      | .Comb l r => COMB2_CONV (PCONV xs l) (PCONV xs r)
      | .Abs _ b => ABS_CONV (PCONV xs b)
      | _ => ALL_CONV
  let (xs, pbod) := strip_abs pat
  PCONV xs pbod

/-- What the recursive `conv` of `WORDIFY_CONV` uses (words.ml 8558-8613). -/
structure WordifyCtx where
  pth_bitval : thm
  pth_add : thm
  pth_mul : thm
  and_th : thm
  m_ty : hol_type
  n_ty : hol_type
  p_ty : hol_type
  VAL_WORD_EQ : thm
  DIMINDEX_CONV : ioconv
  NUM_EXP_CONV : ioconv
  NUM_LT_CONV : ioconv
  NUM_ADD_CONV : ioconv
  NUM_LE_CONV : ioconv

/-- The recursive `conv` of `WORDIFY_CONV` (words.ml 8558-8613). -/
partial def wordifyGo [HolBase] (K : WordifyCtx) : ioconv := fun tm => ExceptT.run do
  let conv := wordifyGo K
  -- `[mk_finty mty,m_ty; mk_finty nty,n_ty; mk_finty pty,p_ty]`: the list
  -- literal is built right to left.
  let tyin3 (mty nty pty : Rat) : ExceptT String IO (List (hol_type × hol_type)) := do
    let fp ← ExceptT.mk (mk_finty pty)
    let fn ← ExceptT.mk (mk_finty nty)
    let fm ← ExceptT.mk (mk_finty mty)
    pure [(fm, K.m_ty), (fn, K.n_ty), (fp, K.p_ty)]
  match tm with
  | .Comb (.Const "bitval" _) _ =>
    ExceptT.mk (GEN_REWRITE_CONV id [K.pth_bitval] tm)
  | .Comb (.Const "val" _) (.Comb (.Const "word" _) _) =>
    ExceptT.mk (TRY_CONV (RAND_CONV (RAND_CONV conv)) tm)
  | .Comb (.Const "val" _) _ => pure (REFL tm)
  | .Comb (.Const "NUMERAL" _) _ =>
    let x ← liftExcept (dest_numeral tm)
    let n := max 1 (wordifyLog2 (if x < 0 then -x else x) 1 0)
    let th1 ← SPEC tm (← HolLight.INST_TYPE [(← ExceptT.mk (mk_finty n), K.n_ty)] K.VAL_WORD_EQ)
    let th2 ← ExceptT.mk ((RAND_CONV (RAND_CONV K.DIMINDEX_CONV THENC K.NUM_EXP_CONV) THENC
                           K.NUM_LT_CONV) (← liftExcept (lhand (concl th1))))
    SYM (← MP th1 (← EQT_ELIM th2))
  | .Comb (.Comb (.Const "+" _) _) _ =>
    let eth ← ExceptT.mk (BINOP_CONV conv tm)
    let r ← liftExcept (rand (concl eth))
    let mtm ← liftExcept (do rand (← lhand r))
    let ntm ← liftExcept (do rand (← rand r))
    let mty ← liftExcept (dest_word_ty (type_of mtm))
    let nty ← liftExcept (dest_word_ty (type_of ntm))
    let pty := max mty nty + 1
    let th ← HolLight.INST_TYPE (← tyin3 mty nty pty) K.pth_add
    let ath ← ExceptT.mk ((BINOP_CONV (BINOP_CONV K.DIMINDEX_CONV THENC K.NUM_LT_CONV))
                (← liftExcept (lhand (concl th))))
    TRANS eth (← SPECL [mtm, ntm] (← MP th (← EQT_ELIM (← TRANS ath K.and_th))))
  | .Comb (.Comb (.Const "*" _) _) _ =>
    let eth ← ExceptT.mk (BINOP_CONV conv tm)
    let r ← liftExcept (rand (concl eth))
    let mtm ← liftExcept (do rand (← lhand r))
    let ntm ← liftExcept (do rand (← rand r))
    let mty ← liftExcept (dest_word_ty (type_of mtm))
    let nty ← liftExcept (dest_word_ty (type_of ntm))
    let pty := mty + nty
    let th ← HolLight.INST_TYPE (← tyin3 mty nty pty) K.pth_mul
    let ath ← ExceptT.mk ((binop2ConvIO (BINOP_CONV K.DIMINDEX_CONV THENC K.NUM_ADD_CONV)
                                       K.DIMINDEX_CONV THENC
                           K.NUM_LE_CONV) (← liftExcept (lhand (concl th))))
    TRANS eth (← SPECL [mtm, ntm] (← MP th (← EQT_ELIM ath)))
  | _ => throw "WORDIFY_CONV"

/-- What the recursive `conv` of `IWORDIFY_CONV` uses (words.ml 8839-8920). -/
structure IWordifyCtx where
  pth_bitval : thm
  pth_val : thm
  pth_add : thm
  pth_sub : thm
  pth_neg : thm
  pth_mul : thm
  and_th : thm
  m_ty : hol_type
  n_ty : hol_type
  p_ty : hol_type
  WORD_IVAL_CONV : ioconv
  DIMINDEX_CONV : ioconv
  NUM_LT_CONV : ioconv
  NUM_ADD_CONV : ioconv
  NUM_LE_CONV : ioconv
  mk_small_numeral : Int → Except String term

/-- The recursive `conv` of `IWORDIFY_CONV` (words.ml 8839-8920). -/
partial def iwordifyGo [HolBase] (K : IWordifyCtx) : ioconv := fun tm => ExceptT.run do
  let conv := iwordifyGo K
  let tyin3 (mty nty pty : Rat) : ExceptT String IO (List (hol_type × hol_type)) := do
    let fp ← ExceptT.mk (mk_finty pty)
    let fn ← ExceptT.mk (mk_finty nty)
    let fm ← ExceptT.mk (mk_finty mty)
    pure [(fm, K.m_ty), (fn, K.n_ty), (fp, K.p_ty)]
  let tyin2 (nty pty : Rat) : ExceptT String IO (List (hol_type × hol_type)) := do
    let fp ← ExceptT.mk (mk_finty pty)
    let fn ← ExceptT.mk (mk_finty nty)
    pure [(fn, K.n_ty), (fp, K.p_ty)]
  -- The `int_add` and `int_sub` cases.
  let addsub (pth : thm) : ExceptT String IO thm := do
    let eth ← ExceptT.mk (BINOP_CONV conv tm)
    let r ← liftExcept (rand (concl eth))
    let mtm ← liftExcept (do rand (← lhand r))
    let ntm ← liftExcept (do rand (← rand r))
    let mty ← liftExcept (dest_word_ty (type_of mtm))
    let nty ← liftExcept (dest_word_ty (type_of ntm))
    let pty := max mty nty + 1
    let th ← HolLight.INST_TYPE (← tyin3 mty nty pty) pth
    let ath ← ExceptT.mk ((BINOP_CONV (BINOP_CONV K.DIMINDEX_CONV THENC K.NUM_LT_CONV))
                (← liftExcept (lhand (concl th))))
    TRANS eth (← SPECL [mtm, ntm] (← MP th (← EQT_ELIM (← TRANS ath K.and_th))))
  if HolMath.Int.is_intconst tm then
    let x ← liftExcept (HolMath.Int.dest_intconst tm)
    let n := wordifyIlog2 x 1 1
    let x' : Int := x.num % (2 ^ n.toNat)
    let tyin := [(← ExceptT.mk (mk_finty n), K.n_ty)]
    let ivalc ← ExceptT.mk (mk_const "ival" tyin)
    let wordc ← ExceptT.mk (mk_const "word" tyin)
    let t ← liftExcept (do mk_comb ivalc (← mk_comb wordc (← K.mk_small_numeral x')))
    SYM (← ExceptT.mk (K.WORD_IVAL_CONV t))
  else match tm with
  | .Comb (.Const "int_of_num" _) (.Comb (.Const "bitval" _) _) =>
    ExceptT.mk (GEN_REWRITE_CONV id [K.pth_bitval] tm)
  | .Comb (.Const "ival" _) _ => pure (REFL tm)
  | .Comb (.Const "int_of_num" _) (.Comb (.Const "val" _) ntm) =>
    let nty ← liftExcept (dest_word_ty (type_of ntm))
    let pty := nty + 1
    let th ← HolLight.INST_TYPE (← tyin2 nty pty) K.pth_val
    let ath ← ExceptT.mk ((BINOP_CONV K.DIMINDEX_CONV THENC K.NUM_LT_CONV)
                (← liftExcept (lhand (concl th))))
    SPEC ntm (← MP th (← EQT_ELIM ath))
  | .Comb (.Const "int_neg" _) _ =>
    let eth ← ExceptT.mk (RAND_CONV conv tm)
    let ntm ← liftExcept (do rand (← rand (← rand (concl eth))))
    let nty ← liftExcept (dest_word_ty (type_of ntm))
    let pty := nty + 1
    let th ← HolLight.INST_TYPE (← tyin2 nty pty) K.pth_neg
    let ath ← ExceptT.mk ((BINOP_CONV K.DIMINDEX_CONV THENC K.NUM_LT_CONV)
                (← liftExcept (lhand (concl th))))
    TRANS eth (← SPEC ntm (← MP th (← EQT_ELIM ath)))
  | .Comb (.Comb (.Const "int_add" _) _) _ => addsub K.pth_add
  | .Comb (.Comb (.Const "int_sub" _) _) _ => addsub K.pth_sub
  | .Comb (.Comb (.Const "int_mul" _) _) _ =>
    let eth ← ExceptT.mk (BINOP_CONV conv tm)
    let r ← liftExcept (rand (concl eth))
    let mtm ← liftExcept (do rand (← lhand r))
    let ntm ← liftExcept (do rand (← rand r))
    let mty ← liftExcept (dest_word_ty (type_of mtm))
    let nty ← liftExcept (dest_word_ty (type_of ntm))
    let pty := mty + nty
    let th ← HolLight.INST_TYPE (← tyin3 mty nty pty) K.pth_mul
    let ath ← ExceptT.mk ((binop2ConvIO (BINOP_CONV K.DIMINDEX_CONV THENC K.NUM_ADD_CONV)
                                       K.DIMINDEX_CONV THENC
                           K.NUM_LE_CONV) (← liftExcept (lhand (concl th))))
    TRANS eth (← SPECL [mtm, ntm] (← MP th (← EQT_ELIM ath)))
  | _ => throw "IWORDIFY_CONV"

/- ------------------------------------------------------------------------- -/
/- Alternative returning signed words.                                       -/
/- Expanding a natural number sum in a more "balanced" way.                  -/
/- Comparison predicates expressed via the top bit.                          -/
/- Convert a natural number expression to the form "val(some_word)".         -/
/- Adjust the word size in val(...) to be possibly larger.                   -/
/- Convert a natural number atom m = n, m < n etc. to word form.             -/
/- Completely analogous functions for integer terms and comparison atoms.    -/
/- Convert a word(....) term with composite inside to word form.             -/
/- ------------------------------------------------------------------------- -/

structure Wordify where
  -- @@FIELDS
  WORD_TO_IWORD_CONV : ioconv
  WORD_IREDUCE_CONV : ioconv
  EXPAND_NSUM_BALANCE_CONV : ioconv
  WORD_COMPARISON_ULT : thm
  WORD_COMPARISON_ULE : thm
  WORD_COMPARISON_ILT : thm
  WORD_COMPARISON_ILE : thm
  WORD_COMPARISON_NE : thm
  WORD_COMPARISON_EQ : thm
  WORDIFY_CONV : ioconv
  VAL_WORD_ADJUST_CONV : Rat → ioconv
  VAL_WORD_ADJUST_BINOP_CONV : ioconv
  WORDIFY_ATOM_CONV : ioconv
  IWORDIFY_CONV : ioconv
  IVAL_WORD_ADJUST_CONV : Rat → ioconv
  IVAL_WORD_ADJUST_BINOP_CONV : ioconv
  IWORDIFY_ATOM_CONV : ioconv
  WORDIFY_WORD_CONV : ioconv
  deriving Inhabited

@[nospecialize]
def setupWordify [HolBase] (D : WordsDeps) (BBitval : Bitval) (BWordType : WordType) (BVal : Val) (BIval : Ival) (BWordOps1 : WordOps1) (BWordOps2 : WordOps2) (BWordArith : WordArith) (BZxSx : ZxSx) (BMisc1 : Misc1) (BReduce1 : Reduce1) (BReduce3 : Reduce3) :
    ExceptT String IO Wordify := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, DIMINDEX_CONV, EXPAND_NSUM_CONV, INTEGER_RULE,
        INT_ARITH, INT_ARITH_TAC, MESON_TAC, MOD_DOWN_CONV, NUM_ADD_CONV, NUM_EXP_CONV,
        NUM_LE_CONV, NUM_LT_CONV, NUM_SUB_CONV, mk_small_numeral, .. } := D
  let { ADD_AC, ARITH_EQ, DIMINDEX_NONZERO, EQ_TRANS, EXP, EXP_ADD, .. } := D.core1
  let { FORALL_BOOL_THM, GE, GT, INT_ABS_MUL, INT_ABS_POS, INT_CONG_IMP_EQ, INT_GE,
        INT_GT, INT_LE_MUL2, INT_LE_REFL, INT_LE_TRANS, INT_NOT_LT, INT_POS, INT_POW,
        INT_POW_ADD, INT_POW_MONO, .. } := D.core2
  let { LE_ADD2, LE_EXP, LE_TRANS, LTE_TRANS, LT_ADD2, LT_IMP_LE, LT_MULT2, LT_REFL,
        MOD_LT, MULT_2, NOT_LE, NOT_LT, .. } := D.core3
  let { BITVAL_CLAUSES, .. } := BBitval
  let { BIT_TRIVIAL, WORD_EQ_BITS_ALT, .. } := BWordType
  let { VAL_BOUND, VAL_EQ, VAL_WORD_BITVAL, VAL_WORD_EQ, WORD_VAL, .. } := BVal
  let { IVAL_BOUND, IVAL_EQ, IVAL_VAL, IWORD_IVAL, .. } := BIval
  let { BIT_WORD_NOT, BIT_WORD_XOR, ICONG_WORD_ADD, ICONG_WORD_NEG, ICONG_WORD_SUB,
        VAL_WORD_ADD, .. } := BWordOps1
  let { ICONG_WORD_MUL, VAL_WORD_MUL, .. } := BWordOps2
  let { WORD_ARITH, .. } := BWordArith
  let { BIT_WORD_ZX, IVAL_WORD_SX, VAL_WORD_ZX, VAL_WORD_ZX_GEN, WORD_SX_TRIVIAL,
        WORD_ZX_TRIVIAL, word_zx, .. } := BZxSx
  let { BIT_WORD_OR_NEG, .. } := BMisc1
  let { WORD_IVAL_CONV, .. } := BReduce1
  let { WORD_REDUCE_CONV, .. } := BReduce3
  -- @@SCOPE END
  let WA : tactic := CONV_TAC (fun t => (WORD_ARITH t).run)
  let isNum := HolMath.Nums.is_numeral

  let WORD_TO_IWORD_CONV : ioconv ← do
    let pth ← prove
     r"word(NUMERAL n):N word = iword(ival(word(NUMERAL n):N word))"
     (REWRITE_TAC [IWORD_IVAL])
    pure ((← GEN_REWRITE_CONV_NET id [pth]) THENC RAND_CONV WORD_IVAL_CONV)

  let WORD_IREDUCE_CONV : ioconv ← pure
    (WORD_REDUCE_CONV THENC ONCE_DEPTH_CONV WORD_TO_IWORD_CONV)

  let EXPAND_NSUM_BALANCE_CONV : ioconv ← do
    let op ← q r"(+):num->num->num"
    let mkEq ← ExceptT.mk (mk_eq : IO _)
    pure (fun tm => ExceptT.run do
      let th ← ExceptT.mk (EXPAND_NSUM_CONV tm)
      let tm' ← liftExcept (rand (concl th))
      let th' ← AC ADD_AC (← liftExcept (do mkEq (tm', ← nsumBalance op tm')))
      TRANS th th')

  let WORD_COMPARISON_ULT ← prove
   r"!(x:N word) (y:N word).
        val x < val y <=>
        bit (dimindex(:N)-1)
            (word_or (word_and (word_not x) y)
                     (word_and (word_or (word_not x) y) (word_sub x y)))"
   WA

  let WORD_COMPARISON_ULE ← prove
   r"!(x:N word) (y:N word).
        val x <= val y <=>
        bit (dimindex(:N)-1)
            (word_and (word_or (word_not x) y)
                      (word_or (word_xor x y) (word_not(word_sub y x))))"
   WA

  let WORD_COMPARISON_ILT ← prove
   r"!(x:N word) (y:N word).
        ival x < ival y <=>
        bit (dimindex(:N)-1)
            (word_or (word_and x (word_not y))
                     (word_and (word_not(word_xor x y)) (word_sub x y)))"
   WA

  let WORD_COMPARISON_ILE ← prove
   r"!(x:N word) (y:N word).
        ival x <= ival y <=>
        bit (dimindex(:N)-1)
            (word_and (word_or x (word_not y))
                      (word_or (word_xor x y) (word_not(word_sub y x))))"
   WA

  let WORD_COMPARISON_NE ← prove
   r"!(x:N word) (y:N word).
        ~(x = y) <=>
        bit (dimindex(:N)-1)
            (word_or (word_xor x y) (word_neg(word_xor x y)))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [BIT_WORD_OR_NEG, ← GSYM NOT_LE] THEN
    SIMP_TAC [DIMINDEX_NONZERO, LT_REFL, ← ARITH_RULE
     (← q r"~(n = 0) ==> (x <= n - 1 <=> x < n)")] THEN
    REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_XOR] THEN MESON_TAC [])

  let WORD_COMPARISON_EQ ← prove
   r"!(x:N word) (y:N word).
        x = y <=>
        bit (dimindex(:N)-1)
            (word_not((word_or (word_xor x y) (word_neg(word_xor x y)))))"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [BIT_WORD_NOT, BIT_WORD_OR_NEG, ← GSYM NOT_LE] THEN
    SIMP_TAC [DIMINDEX_NONZERO, LT_REFL, ← ARITH_RULE
     (← q r"~(n = 0) ==> (x <= n - 1 <=> x < n)")] THEN
    REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_XOR] THEN MESON_TAC [])

  let WORDIFY_CONV : ioconv ← do
    -- `let ... and ...`: left to right.
    let m_ty ← qty "M"
    let n_ty ← qty "N"
    let p_ty ← qty "P"
    let num_ty ← qty "num"
    let and_th ← TAUT (← q r"T /\ T <=> T")
    let pth_bitval ← prove
     r"!b. bitval b = val(word(bitval b):1 word)"
     (REWRITE_TAC [VAL_WORD_BITVAL])
    let pth_add ← prove
     r"dimindex(:M) < dimindex(:P) /\ dimindex(:N) < dimindex(:P)
     ==> !x y. val(x:M word) + val(y:N word) =
               val(word_add (word_zx x) (word_zx y):P word)"
     (REPEAT STRIP_TAC THEN REWRITE_TAC [VAL_WORD_ADD, VAL_WORD_ZX_GEN] THEN
      CONV_TAC MOD_DOWN_CONV THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
      TRANS_TAC LTE_TRANS (← q r"2 EXP dimindex(:M) + 2 EXP dimindex(:N)") THEN
      SIMP_TAC [LT_ADD2, VAL_BOUND] THEN
      TRANS_TAC LE_TRANS (← q r"2 EXP SUC(MAX (dimindex(:M)) (dimindex(:N)))") THEN
      CONJ_TAC THENL
       [REWRITE_TAC [EXP, MULT_2] THEN MATCH_MP_TAC LE_ADD2 THEN CONJ_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [LE_EXP, ARITH_EQ] THEN ASM_ARITH_TAC)
    let pth_mul ← prove
     r"dimindex(:M) + dimindex(:N) <= dimindex(:P)
     ==> !x y. val(x:M word) * val(y:N word) =
               val(word_mul (word_zx x) (word_zx y):P word)"
     (REPEAT STRIP_TAC THEN REWRITE_TAC [VAL_WORD_MUL, VAL_WORD_ZX_GEN] THEN
      CONV_TAC MOD_DOWN_CONV THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
      TRANS_TAC LTE_TRANS (← q r"2 EXP (dimindex (:M) + dimindex (:N))") THEN
      ASM_REWRITE_TAC [LE_EXP, ARITH_EQ] THEN REWRITE_TAC [EXP_ADD] THEN
      MATCH_MP_TAC LT_MULT2 THEN REWRITE_TAC [VAL_BOUND])
    let K : WordifyCtx :=
      { pth_bitval, pth_add, pth_mul, and_th, m_ty, n_ty, p_ty, VAL_WORD_EQ,
        DIMINDEX_CONV, NUM_EXP_CONV, NUM_LT_CONV, NUM_ADD_CONV, NUM_LE_CONV }
    let fullconv := wordifyGo K THENC (← GEN_REWRITE_CONV_NET DEPTH_CONV [WORD_ZX_TRIVIAL])
    pure (fun tm => if type_of tm == num_ty then fullconv tm
                    else pure (.error "WORDIFY_CONV"))

  let VAL_WORD_ADJUST_CONV : Rat → ioconv ← do
    let m_ty ← qty "M"
    let n_ty ← qty "N"
    let pth ← prove
     r"dimindex(:M) <= dimindex(:N)
     ==> !x. val(x:M word) = val(word_zx x:N word)"
     (SIMP_TAC [VAL_WORD_ZX])
    pure (fun n tm => ExceptT.run do
      match tm with
      | .Comb (.Const "val" _) _ =>
        let m ← liftExcept (do dest_word_ty (type_of (← rand tm)))
        if m == n then pure (REFL tm)
        else if m > n then throw "VAL_WORD_ADJUST_CONV: too small"
        else
          let fn ← ExceptT.mk (mk_finty n)
          let fm ← ExceptT.mk (mk_finty m)
          let th ← HolLight.INST_TYPE [(fm, m_ty), (fn, n_ty)] pth
          let cth ← ExceptT.mk ((BINOP_CONV DIMINDEX_CONV THENC NUM_LE_CONV)
                      (← liftExcept (lhand (concl th))))
          SPEC (← liftExcept (rand tm)) (← MP th (← EQT_ELIM cth))
      | _ => throw "VAL_WORD_ADJUST_CONV: wrong form of term")

  let VAL_WORD_ADJUST_BINOP_CONV : ioconv ← pure (fun tm => ExceptT.run do
    let tm1 ← liftExcept (lhand tm)
    let tm2 ← liftExcept (rand tm)
    -- `max_num a b`: the right argument first.
    let b ← liftExcept (do dest_word_ty (type_of (← rand tm2)))
    let a ← liftExcept (do dest_word_ty (type_of (← rand tm1)))
    ExceptT.mk (BINOP_CONV (VAL_WORD_ADJUST_CONV (max a b)) tm))

  let WORDIFY_ATOM_CONV : ioconv ← do
    let num_ty ← qty "num"
    let pth ← prove
     r"!(x:N word) (y:N word).
          val x < val y <=>
          (~bit (dimindex(:N)-1) x /\ bit (dimindex(:N)-1) y) \/
          (~bit (dimindex(:N)-1) x \/ bit (dimindex(:N)-1) y) /\
          bit (dimindex(:N)-1) (word_sub x y)"
     WA
    -- `mk_abs(`x:num`, subst[`x:num`,`dimindex(:N)-1`] (...))`: the tuple
    -- and the list are built right to left.
    let d1 ← q r"dimindex(:N)-1"
    let x1 ← q "x:num"
    let sb ← ExceptT.mk (subst [(x1, d1)])
    let body ← ExceptT.mk (sb (← liftExcept (rand (strip_forall (concl pth)).2)))
    let x0 ← q "x:num"
    let pat ← liftExcept (mk_abs x0 body)
    -- `GSYM NOT_LT` is rebuilt on each call in OCaml; it is a pure rule.
    let gNOT_LT ← GSYM NOT_LT
    let VAL_LT_CONV :=
       (← GEN_REWRITE_CONV_NET id [pth]) THENC
       patConvIO pat (LAND_CONV DIMINDEX_CONV THENC NUM_SUB_CONV)
    pure (fun tm => do
      let pre := BINOP_CONV WORDIFY_CONV THENC VAL_WORD_ADJUST_BINOP_CONV
      match tm with
      | .Comb (.Comb (.Const "=" _) _) t =>
        if type_of t == num_ty then
          (pre THENC GEN_REWRITE_CONV id [VAL_EQ]) tm
        else pure (.error "WORDIFY_ATOM_CONV")
      | .Comb (.Comb (.Const "<" _) _) _ =>
        (pre THENC VAL_LT_CONV) tm
      | .Comb (.Comb (.Const ">" _) _) _ =>
        (pre THENC GEN_REWRITE_CONV id [GT] THENC VAL_LT_CONV) tm
      | .Comb (.Comb (.Const "<=" _) _) _ =>
        (pre THENC GEN_REWRITE_CONV id [gNOT_LT] THENC
         RAND_CONV VAL_LT_CONV) tm
      | .Comb (.Comb (.Const ">=" _) _) _ =>
        (pre THENC GEN_REWRITE_CONV id [GE] THENC
         GEN_REWRITE_CONV id [gNOT_LT] THENC
         RAND_CONV VAL_LT_CONV) tm
      | _ => pure (.error "WORDIFY_ATOM_CONV"))

  let IWORDIFY_CONV : ioconv ← do
    let m_ty ← qty "M"
    let n_ty ← qty "N"
    let p_ty ← qty "P"
    let int_ty ← qty "int"
    let and_th ← TAUT (← q r"T /\ T <=> T")
    let pth_bitval ← prove
     r"!b. &(bitval b) = ival(word(bitval b):2 word)"
     (REWRITE_TAC [FORALL_BOOL_THM, BITVAL_CLAUSES] THEN
      CONV_TAC WORD_REDUCE_CONV)
    let pth_val ← prove
     r"dimindex(:N) < dimindex(:P)
     ==> !x. &(val(x:N word)) = ival(word_zx x:P word)"
     (REPEAT STRIP_TAC THEN REWRITE_TAC [IVAL_VAL, BIT_WORD_ZX] THEN
      ASM_SIMP_TAC [BIT_TRIVIAL, ← ARITH_RULE (← q r"n < p ==> n <= p - 1")] THEN
      ASM_SIMP_TAC [VAL_WORD_ZX, LT_IMP_LE, BITVAL_CLAUSES] THEN
      INT_ARITH_TAC)
    let ib (t : term) : tactic := tactic_of do pure (MP_TAC (← ISPEC t IVAL_BOUND))
    let pth_add ← prove
     r"dimindex(:M) < dimindex(:P) /\ dimindex(:N) < dimindex(:P)
     ==> !x y. ival(x:M word) + ival(y:N word) =
               ival(word_add (word_sx x) (word_sx y):P word)"
     (← do
      let ia ← INT_ARITH
       (← q r"&2 * a <= c /\ &2 * b <= c /\ &2 * c <= e
      ==> --a <= x /\ x < a ==> --b <= y /\ y < b ==> --c <= z /\ z < c
          ==> abs((x + y) - z):int < e")
      let ir ← INTEGER_RULE (← q r"(x:int == y) (mod p) <=> (y == x) (mod p)")
      pure (REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS
       (← q r"ival((word_sx:M word->P word) x) +
      ival((word_sx:N word->P word) y)") THEN
      CONJ_TAC THENL [ASM_SIMP_TAC [IVAL_WORD_SX, LT_IMP_LE], ALL_TAC] THEN
      MATCH_MP_TAC INT_CONG_IMP_EQ THEN
      EXISTS_TAC (← q r"(&2:int) pow dimindex(:P)") THEN
      ONCE_REWRITE_TAC [ir] THEN
      REWRITE_TAC [ICONG_WORD_ADD] THEN ASM_SIMP_TAC [IVAL_WORD_SX, LT_IMP_LE] THEN
      MAP_EVERY ib
       [← q r"word_add (word_sx(x:M word)) (word_sx(y:N word)):P word",
        ← q "y:N word", ← q "x:M word"] THEN
      MATCH_MP_TAC ia THEN
      REWRITE_TAC [← GSYM (← CONJUNCT2 INT_POW)] THEN
      SUBGOAL_THEN (← q r"~(dimindex(:M) = 0) /\ ~(dimindex(:N) = 0)")
      STRIP_ASSUME_TAC THENL [REWRITE_TAC [DIMINDEX_NONZERO], ALL_TAC] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_POW_MONO THEN ASM_ARITH_TAC))
    let pth_sub ← prove
     r"dimindex(:M) < dimindex(:P) /\ dimindex(:N) < dimindex(:P)
     ==> !x y. ival(x:M word) - ival(y:N word) =
               ival(word_sub (word_sx x) (word_sx y):P word)"
     (← do
      let ia ← INT_ARITH
       (← q r"&2 * a <= c /\ &2 * b <= c /\ &2 * c <= e
      ==> --a <= x /\ x < a ==> --b <= y /\ y < b ==> --c <= z /\ z < c
          ==> abs((x - y) - z):int < e")
      let ir ← INTEGER_RULE (← q r"(x:int == y) (mod p) <=> (y == x) (mod p)")
      pure (REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS
       (← q r"ival((word_sx:M word->P word) x) -
      ival((word_sx:N word->P word) y)") THEN
      CONJ_TAC THENL [ASM_SIMP_TAC [IVAL_WORD_SX, LT_IMP_LE], ALL_TAC] THEN
      MATCH_MP_TAC INT_CONG_IMP_EQ THEN
      EXISTS_TAC (← q r"(&2:int) pow dimindex(:P)") THEN
      ONCE_REWRITE_TAC [ir] THEN
      REWRITE_TAC [ICONG_WORD_SUB] THEN ASM_SIMP_TAC [IVAL_WORD_SX, LT_IMP_LE] THEN
      MAP_EVERY ib
       [← q r"word_sub (word_sx(x:M word)) (word_sx(y:N word)):P word",
        ← q "y:N word", ← q "x:M word"] THEN
      MATCH_MP_TAC ia THEN
      REWRITE_TAC [← GSYM (← CONJUNCT2 INT_POW)] THEN
      SUBGOAL_THEN (← q r"~(dimindex(:M) = 0) /\ ~(dimindex(:N) = 0)")
      STRIP_ASSUME_TAC THENL [REWRITE_TAC [DIMINDEX_NONZERO], ALL_TAC] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_POW_MONO THEN ASM_ARITH_TAC))
    let pth_neg ← prove
     r"dimindex(:N) < dimindex(:P)
     ==> !x. --(ival(x:N word)) = ival(word_neg(word_sx x:P word))"
     (← do
      let ia ← INT_ARITH
       (← q r"&2 * a <= c /\ &2 * c <= e
      ==> --a <= x /\ x < a ==> --c <= z /\ z < c
          ==> abs(--x - z):int < e")
      let ir ← INTEGER_RULE (← q r"(x:int == y) (mod p) <=> (y == x) (mod p)")
      pure (REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS
       (← q r"--ival((word_sx:N word->P word) x)") THEN
      CONJ_TAC THENL [ASM_SIMP_TAC [IVAL_WORD_SX, LT_IMP_LE], ALL_TAC] THEN
      MATCH_MP_TAC INT_CONG_IMP_EQ THEN
      EXISTS_TAC (← q r"(&2:int) pow dimindex(:P)") THEN
      ONCE_REWRITE_TAC [ir] THEN
      REWRITE_TAC [ICONG_WORD_NEG] THEN ASM_SIMP_TAC [IVAL_WORD_SX, LT_IMP_LE] THEN
      MAP_EVERY ib
       [← q r"word_neg (word_sx(x:N word)):P word", ← q "x:N word"] THEN
      MATCH_MP_TAC ia THEN
      REWRITE_TAC [← GSYM (← CONJUNCT2 INT_POW)] THEN
      SUBGOAL_THEN (← q r"~(dimindex(:M) = 0) /\ ~(dimindex(:N) = 0)")
      STRIP_ASSUME_TAC THENL [REWRITE_TAC [DIMINDEX_NONZERO], ALL_TAC] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_POW_MONO THEN ASM_ARITH_TAC))
    let pth_mul ← prove
     r"dimindex(:M) + dimindex(:N) <= dimindex(:P)
     ==> !x y. ival(x:M word) * ival(y:N word) =
               ival(word_mul (word_sx x) (word_sx y):P word)"
     (← do
      let ia3 ← INT_ARITH (← q r"--e:int <= x /\ x < e ==> abs(x) <= e")
      let ia2 ← INT_ARITH
       (← q r"&2 * c <= e /\ &2 * abs(xy) <= c
      ==> --c <= z /\ z < c
          ==> abs(xy - z):int < e")
      let ir ← INTEGER_RULE (← q r"(x:int == y) (mod p) <=> (y == x) (mod p)")
      pure (REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"~(dimindex(:M) = 0) /\ ~(dimindex(:N) = 0)")
      STRIP_ASSUME_TAC THENL [REWRITE_TAC [DIMINDEX_NONZERO], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"dimindex(:M) < dimindex(:P) /\ dimindex(:N) < dimindex(:P)")
      STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      TRANS_TAC EQ_TRANS
       (← q r"ival((word_sx:M word->P word) x) *
      ival((word_sx:N word->P word) y)") THEN
      CONJ_TAC THENL [ASM_SIMP_TAC [IVAL_WORD_SX, LT_IMP_LE], ALL_TAC] THEN
      MATCH_MP_TAC INT_CONG_IMP_EQ THEN
      EXISTS_TAC (← q r"(&2:int) pow dimindex(:P)") THEN
      ONCE_REWRITE_TAC [ir] THEN
      REWRITE_TAC [ICONG_WORD_MUL] THEN ASM_SIMP_TAC [IVAL_WORD_SX, LT_IMP_LE] THEN
      MP_TAC (← ISPEC (← q r"word_mul (word_sx(x:M word)) (word_sx(y:N word)):P word")
          IVAL_BOUND) THEN
      MATCH_MP_TAC ia2 THEN
      CONJ_TAC THENL
       [ALL_TAC,
        MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC
         (← q r"(&2:int) * &2 pow (dimindex(:M) - 1) * &2 pow (dimindex(:N) - 1)") THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC INT_LE_MUL2 THEN
          REWRITE_TAC [INT_ABS_POS, INT_LE_REFL, INT_POS, INT_ABS_MUL] THEN
          MATCH_MP_TAC INT_LE_MUL2 THEN
          REWRITE_TAC [INT_ABS_POS, INT_LE_REFL, INT_POS, INT_ABS_MUL] THEN
          CONJ_TAC THEN MATCH_MP_TAC ia3 THEN
          REWRITE_TAC [IVAL_BOUND],
          ALL_TAC]] THEN
      REWRITE_TAC [← GSYM INT_POW, ← GSYM INT_POW_ADD] THEN
      MATCH_MP_TAC INT_POW_MONO THEN ASM_ARITH_TAC))
    let K : IWordifyCtx :=
      { pth_bitval, pth_val, pth_add, pth_sub, pth_neg, pth_mul, and_th, m_ty, n_ty,
        p_ty, WORD_IVAL_CONV, DIMINDEX_CONV, NUM_LT_CONV, NUM_ADD_CONV, NUM_LE_CONV,
        mk_small_numeral }
    let fullconv := iwordifyGo K THENC (← GEN_REWRITE_CONV_NET DEPTH_CONV [WORD_SX_TRIVIAL])
    pure (fun tm => if type_of tm == int_ty then fullconv tm
                    else pure (.error "IWORDIFY_CONV"))

  let IVAL_WORD_ADJUST_CONV : Rat → ioconv ← do
    let m_ty ← qty "M"
    let n_ty ← qty "N"
    let pth ← prove
     r"dimindex(:M) <= dimindex(:N)
     ==> !x. ival(x:M word) = ival(word_sx x:N word)"
     (SIMP_TAC [IVAL_WORD_SX])
    pure (fun n tm => ExceptT.run do
      match tm with
      | .Comb (.Const "ival" _) _ =>
        let m ← liftExcept (do dest_word_ty (type_of (← rand tm)))
        if m == n then pure (REFL tm)
        else if m > n then throw "IVAL_WORD_ADJUST_CONV: too small"
        else
          let fn ← ExceptT.mk (mk_finty n)
          let fm ← ExceptT.mk (mk_finty m)
          let th ← HolLight.INST_TYPE [(fm, m_ty), (fn, n_ty)] pth
          let cth ← ExceptT.mk ((BINOP_CONV DIMINDEX_CONV THENC NUM_LE_CONV)
                      (← liftExcept (lhand (concl th))))
          SPEC (← liftExcept (rand tm)) (← MP th (← EQT_ELIM cth))
      | _ => throw "IVAL_WORD_ADJUST_CONV: wrong form of term")

  let IVAL_WORD_ADJUST_BINOP_CONV : ioconv ← pure (fun tm => ExceptT.run do
    let tm1 ← liftExcept (lhand tm)
    let tm2 ← liftExcept (rand tm)
    let b ← liftExcept (do dest_word_ty (type_of (← rand tm2)))
    let a ← liftExcept (do dest_word_ty (type_of (← rand tm1)))
    ExceptT.mk (BINOP_CONV (IVAL_WORD_ADJUST_CONV (max a b)) tm))

  let IWORDIFY_ATOM_CONV : ioconv ← do
    let int_ty ← qty "int"
    let pth ← prove
     r"!(x:N word) (y:N word).
          ival x < ival y <=>
          (bit (dimindex(:N)-1) x /\ ~bit (dimindex(:N)-1) y) \/
           (bit (dimindex(:N)-1) x \/ ~bit (dimindex(:N)-1) y) /\
          bit (dimindex(:N)-1) (word_sub x y)"
     WA
    let d1 ← q r"dimindex(:N)-1"
    let x1 ← q "x:num"
    let sb ← ExceptT.mk (subst [(x1, d1)])
    let body ← ExceptT.mk (sb (← liftExcept (rand (strip_forall (concl pth)).2)))
    let x0 ← q "x:num"
    let pat ← liftExcept (mk_abs x0 body)
    let gINT_NOT_LT ← GSYM INT_NOT_LT
    let IVAL_LT_CONV :=
       (← GEN_REWRITE_CONV_NET id [pth]) THENC
       patConvIO pat (LAND_CONV DIMINDEX_CONV THENC NUM_SUB_CONV)
    pure (fun tm => do
      let pre := BINOP_CONV IWORDIFY_CONV THENC IVAL_WORD_ADJUST_BINOP_CONV
      match tm with
      | .Comb (.Comb (.Const "=" _) _) t =>
        if type_of t == int_ty then
          (pre THENC GEN_REWRITE_CONV id [IVAL_EQ]) tm
        else pure (.error "IWORDIFY_ATOM_CONV")
      | .Comb (.Comb (.Const "int_lt" _) _) _ =>
        (pre THENC IVAL_LT_CONV) tm
      | .Comb (.Comb (.Const "int_gt" _) _) _ =>
        (pre THENC GEN_REWRITE_CONV id [INT_GT] THENC IVAL_LT_CONV) tm
      | .Comb (.Comb (.Const "int_le" _) _) _ =>
        (pre THENC GEN_REWRITE_CONV id [gINT_NOT_LT] THENC
         RAND_CONV IVAL_LT_CONV) tm
      | .Comb (.Comb (.Const "int_ge" _) _) _ =>
        (pre THENC GEN_REWRITE_CONV id [INT_GE] THENC
         GEN_REWRITE_CONV id [gINT_NOT_LT] THENC
         RAND_CONV IVAL_LT_CONV) tm
      | _ => pure (.error "IWORDIFY_ATOM_CONV"))

  let WORDIFY_WORD_CONV : ioconv ← do
    let conv :=
      RAND_CONV WORDIFY_CONV THENC
      ((← GEN_REWRITE_CONV_NET id [WORD_VAL]) ORELSEC
       (← GEN_REWRITE_CONV_NET id [← GSYM word_zx]))
    pure (fun tm => do
      match tm with
      | .Comb (.Const "word" _) t =>
        if !(isNum t) then conv tm else pure (.error "WORDIFY_WORD_CONV")
      | _ => pure (.error "WORDIFY_WORD_CONV"))

  -- @@RETURN BEGIN
  return { WORD_TO_IWORD_CONV, WORD_IREDUCE_CONV, EXPAND_NSUM_BALANCE_CONV,
           WORD_COMPARISON_ULT, WORD_COMPARISON_ULE, WORD_COMPARISON_ILT,
           WORD_COMPARISON_ILE, WORD_COMPARISON_NE, WORD_COMPARISON_EQ, WORDIFY_CONV,
           VAL_WORD_ADJUST_CONV, VAL_WORD_ADJUST_BINOP_CONV, WORDIFY_ATOM_CONV,
           IWORDIFY_CONV, IVAL_WORD_ADJUST_CONV, IVAL_WORD_ADJUST_BINOP_CONV,
           IWORDIFY_ATOM_CONV, WORDIFY_WORD_CONV }
  -- @@RETURN END

/-- `carrying` of `BITBLAST_THEN` (words.ml 9038-9046). -/
def bitblastCarrying : term → Bool
  | .Comb (.Comb (.Const "word_add" _) _) _ => true
  | .Comb (.Comb (.Const "word_sub" _) _) _ => true
  | .Comb (.Const "word_neg" _) (.Comb (.Const "word" _) (.Comb (.Const "bitval" _) _)) => false
  | .Comb (.Const "word_neg" _) _ => true
  | _ => false

/-- `interleave` of `BITBLAST_THEN` (words.ml 9071-9075). -/
partial def bitblastInterleave : List (List term) → List term
  | [] => []
  | [] :: rst => bitblastInterleave rst
  | (h :: t) :: rst => h :: bitblastInterleave (rst ++ [t])

/-- lib.ml's `end_itlist` for a rule that can fail: `f h (end_itlist f t)`. -/
def endItlistM {α : Type} (f : α → α → ExceptT String IO α) : List α → ExceptT String IO α
  | [] => throw "end_itlist"
  | [x] => pure x
  | h :: t => do f h (← endItlistM f t)

/-- lib.ml's `time` for a function that can fail: the same report as
`HolCore.Lib.time`, and on failure `Failed after ...: Failure("msg")`. -/
def timeE {α β : Type} (f : α → ExceptT String IO β) (x : α) : ExceptT String IO β :=
  ExceptT.mk do
    if !(← HolCore.Lib.report_timing.get) then return ← (f x).run
    let startTime ← IO.monoNanosNow
    let r ← (f x).run
    let finishTime ← IO.monoNanosNow
    match r with
    | .ok _ => HolCore.Lib.report s!"CPU time (user): {finishTime - startTime}ns"
    | .error e =>
      HolCore.Lib.report
        s!"Failed after (user) CPU time of {finishTime - startTime}ns: Failure({e.quote})"
    return r

/- ------------------------------------------------------------------------- -/
/- Expanding multiplication, popcount and unsigned word ordering relations.  -/
/- Basic bit-blasting tactic.                                                -/
/- ------------------------------------------------------------------------- -/

structure Bitblast where
  -- @@FIELDS
  WORD_MUL_EXPAND_CONV : ioconv
  WORD_POPCOUNT_EXPAND_CONV : ioconv
  WORD_INEQ_RELATION_EXPAND_CONV : ioconv
  VAL_MOD_OR_DIV_CONV : ioconv
  BITBLAST_THEN : (List term → tactic) → tactic
  BITBLAST_TAC : tactic
  BITBLAST_RULE : term → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupBitblast [HolBase] (D : WordsDeps) (BBitval : Bitval) (BWordType : WordType) (BVal : Val) (BLimits : Limits) (BPopcount : Popcount) (BGeneralOps : GeneralOps) (BWordOps1 : WordOps1) (BWordOps3 : WordOps3) (BValExpand : ValExpand) (BMisc1 : Misc1) (BMasks : Masks) (BClzCtz : ClzCtz) (BReverse : Reverse) (BBitWordConv : BitWordConv) (BBlast : Blast) (BReduce3 : Reduce3) (BWordify : Wordify) :
    ExceptT String IO Bitblast := do
  -- @@SCOPE BEGIN
  let { BDD_DEFTAUT, DIMINDEX_CONV, EXPAND_CASES_CONV, NUM_EXP_CONV, NUM_RED_CONV,
        NUM_SUB_CONV, let_CONV, mk_small_numeral, .. } := D
  let { ADD_CLAUSES, .. } := D.core1
  let { MULT_CLAUSES, NUMSEG_LT_DIMINDEX, .. } := D.core3
  let { BITVAL_CLAUSES, .. } := BBitval
  let { WORD_EQ_BITS_ALT, .. } := BWordType
  let { WORD_VAL, .. } := BVal
  let { WORD_INT_MAX, WORD_INT_MIN, word_UINT_MAX, .. } := BLimits
  let { WORD_POPCOUNT_NSUM, .. } := BPopcount
  let { irelational2, relational2, .. } := BGeneralOps
  let { WORD_ADD, .. } := BWordOps1
  let { VAL_WORD_USHR, WORD_MUL_EXPAND, word_ige, word_igt, word_ile, word_ilt,
        word_uge, word_ugt, word_ule, word_ult, .. } := BWordOps3
  let { EMPOWER_CONV, .. } := BValExpand
  let { WORD_MUL_SYM, .. } := BMisc1
  let { VAL_WORD_AND_MASK_WORD, WORD_AND_MASK, .. } := BMasks
  let { WORD_CTZ_EMULATION_POPCOUNT, .. } := BClzCtz
  let { WORD_CTZ_REVERSEFIELDS, .. } := BReverse
  let { BIT_WORD_CONV, .. } := BBitWordConv
  let { WORD_EVENPARITY_POPCOUNT, WORD_ODDPARITY_POPCOUNT, .. } := BBlast
  let { WORD_RED_CONV, .. } := BReduce3
  let { EXPAND_NSUM_BALANCE_CONV, IWORDIFY_ATOM_CONV, WORDIFY_ATOM_CONV,
        WORDIFY_WORD_CONV, .. } := BWordify
  -- @@SCOPE END
  let isNum := HolMath.Nums.is_numeral

  let WORD_MUL_EXPAND_CONV : ioconv ← do
    let pth ← prove
     r"!b x:N word.
          word(bitval b * val x) =
          word_and (word_neg(word(bitval b))) x"
     (REPEAT GEN_TAC THEN REWRITE_TAC [WORD_AND_MASK] THEN
      COND_CASES_TAC THEN
      ASM_REWRITE_TAC [BITVAL_CLAUSES, MULT_CLAUSES, WORD_VAL])
    -- `let conv = ... and swap = ...`: left to right; each THENC chain is
    -- built right to left.
    let c6 ← GEN_REWRITE_CONV_NET ONCE_DEPTH_CONV [WORD_VAL, pth]
    let c5 ← GEN_REWRITE_CONV_NET TOP_SWEEP_CONV [WORD_ADD]
    let c4 ← GEN_REWRITE_CONV_NET DEPTH_CONV [BITVAL_CLAUSES, MULT_CLAUSES, ADD_CLAUSES]
    let c1 ← GEN_REWRITE_CONV_NET id [← REWRITE_RULE [NUMSEG_LT_DIMINDEX] WORD_MUL_EXPAND]
    let conv :=
      c1 THENC
      RAND_CONV
       (LAND_CONV (RAND_CONV (LAND_CONV DIMINDEX_CONV THENC NUM_SUB_CONV)) THENC
        EXPAND_NSUM_BALANCE_CONV) THENC
      ONCE_DEPTH_CONV BIT_WORD_CONV THENC
      c4 THENC c5 THENC c6
    let swap ← GEN_REWRITE_CONV_NET id [WORD_MUL_SYM]
    pure (fun tm => do
      match tm with
      | .Comb (.Comb (.Const "word_mul" _) x) y =>
        match x, y with
        | _, .Comb (.Const "word" _) n =>
          if isNum n then (swap THENC conv) tm
          else conv tm
        | _, _ => conv tm
      | _ => pure (.error "WORD_MUL_EXPAND_CONV"))

  let WORD_POPCOUNT_EXPAND_CONV : ioconv ← do
    pure ((← GEN_REWRITE_CONV_NET id
       [← REWRITE_RULE [NUMSEG_LT_DIMINDEX] WORD_POPCOUNT_NSUM]) THENC
      LAND_CONV (RAND_CONV (LAND_CONV DIMINDEX_CONV THENC NUM_SUB_CONV)) THENC
      EXPAND_NSUM_BALANCE_CONV)

  let WORD_INEQ_RELATION_EXPAND_CONV : ioconv ← do
    -- The list literal is parsed right to left; `map` runs left to right.
    let srcs :=
      [r"word_ule (x:N word) y", r"word_ult (x:N word) y",
       r"word_uge (x:N word) y", r"word_ugt (x:N word) y",
       r"word_ile (x:N word) y", r"word_ilt (x:N word) y",
       r"word_ige (x:N word) y", r"word_igt (x:N word) y"]
    let tms := (← srcs.reverse.mapM q).reverse
    let rc := REWRITE_CONV [relational2, word_ule, word_ult, word_uge, word_ugt,
                            irelational2, word_ile, word_ilt, word_ige, word_igt]
    let ths ← tms.mapM (fun t => ExceptT.mk (rc t))
    GEN_REWRITE_CONV_NET id ths

  let VAL_MOD_OR_DIV_CONV : ioconv ← do
    let conv_div ← GEN_REWRITE_CONV_NET id [← GSYM VAL_WORD_USHR]
    let conv_mod :=
      RAND_CONV EMPOWER_CONV THENC
      (← GEN_REWRITE_CONV_NET id [← GSYM VAL_WORD_AND_MASK_WORD]) THENC
      funpow 3 RAND_CONV (LAND_CONV NUM_EXP_CONV THENC NUM_SUB_CONV)
    pure (fun tm => do
      match tm with
      | .Comb (.Comb (.Const "DIV" _) (.Comb (.Const "val" _) _)) _ => conv_div tm
      | .Comb (.Comb (.Const "MOD" _) (.Comb (.Const "val" _) _)) _ => conv_mod tm
      | _ => pure (.error "VAL_MOD_OR_DIV_CONV"))

  let BITBLAST_THEN : (List term → tactic) → tactic ← do
    -- `!word_SIZE_CONV` is read here, when BITWISE_EXPAND_CONV is built.
    let sz ← D.word_SIZE_CONV.get
    let BITWISE_EXPAND_CONV : ioconv :=
      (← GEN_REWRITE_CONV_NET id [WORD_EQ_BITS_ALT]) THENC
      BINDER_CONV (LAND_CONV (RAND_CONV sz)) THENC
      EXPAND_CASES_CONV
    -- `BIT_WORD_CONV o check (not o carrying o rand)`.
    let nocarry : ioconv := fun t => ExceptT.run do
      let r ← liftExcept (rand t)
      if !(bitblastCarrying r) then ExceptT.mk (BIT_WORD_CONV t) else throw "check"
    let BITBLAST_EQUATION (th : thm) : ExceptT String IO thm := do
      let ths := CONJUNCTS (← CONV_RULE BITWISE_EXPAND_CONV th)
      let c :=
        LAND_CONV
         (BIT_WORD_CONV THENC SUBS_CONV [th] THENC
          TOP_DEPTH_CONV nocarry) THENC
        SYM_CONV THENC
        RAND_CONV (REWRITE_CONV [])
      endItlistM CONJ (← ths.mapM (CONV_RULE c))
    let bit_tm ← q r"bit:num->(N)word->bool"
    let n_ty ← qty "N"
    let wordbits_var (tm : term) : IO (List term) := do
      -- `try ... with Failure _ -> []`
      match ← (do
          let n ← liftExcept (dest_word_ty (type_of tm))
          let btm := inst [(← ExceptT.mk (mk_finty n), n_ty)] bit_tm
          (List.range n.floor.toNat).mapM (fun (i : Nat) =>
            liftExcept (do mk_comb (← mk_comb btm (← mk_small_numeral (i : Int))) tm))
        : ExceptT String IO (List term)).run with
      | .ok l => pure l
      | .error _ => pure []
    let wordbits (tm : term) : IO (List term) := do
      pure (bitblastInterleave (← (frees tm).mapM wordbits_var))
    let mkEq ← ExceptT.mk (mk_eq : IO _)
    pure (fun tac =>
      REPEAT (GEN_TAC ORELSE CONJ_TAC) THEN
      REPEAT ((COND_CASES_TAC THEN POP_ASSUM MP_TAC) ORELSE
              (CHANGED_TAC (CONV_TAC (ONCE_DEPTH_CONV let_CONV)))) THEN
      (fun gl => ExceptT.run do
        let vars ← (wordbits gl.2 : IO _)
        let t1 : tactic :=
          CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
          REWRITE_TAC [word_UINT_MAX, WORD_INT_MIN, WORD_INT_MAX] THEN
          CONV_TAC (DEPTH_CONV
           (WORD_RED_CONV ORELSEC NUM_RED_CONV ORELSEC DIMINDEX_CONV)) THEN
          CONV_TAC (ONCE_DEPTH_CONV WORD_INEQ_RELATION_EXPAND_CONV) THEN
          GEN_REWRITE_TAC TOP_DEPTH_CONV
           [WORD_ODDPARITY_POPCOUNT, WORD_EVENPARITY_POPCOUNT,
            WORD_CTZ_EMULATION_POPCOUNT, ← GSYM WORD_CTZ_REVERSEFIELDS] THEN
          CONV_TAC (ONCE_DEPTH_CONV WORD_POPCOUNT_EXPAND_CONV) THEN
          CONV_TAC (ONCE_DEPTH_CONV WORDIFY_WORD_CONV) THEN
          CONV_TAC (DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV)) THEN
          CONV_TAC (ONCE_DEPTH_CONV VAL_MOD_OR_DIV_CONV) THEN
          CONV_TAC (DEPTH_CONV
           (WORDIFY_ATOM_CONV ORELSEC IWORDIFY_ATOM_CONV)) THEN
          CONV_TAC (DEPTH_CONV WORD_MUL_EXPAND_CONV) THEN
          REPEAT (fun gl' => ExceptT.run do
            let some t := (sort free_in (find_terms bitblastCarrying gl'.2)).head?
              | throw "hd"
            let v ← (genvar (type_of t) : IO term)
            ExceptT.mk (ABBREV_TAC (← liftExcept (mkEq (v, t))) gl')) THEN
          CONV_TAC (ONCE_DEPTH_CONV
           (BITWISE_EXPAND_CONV THENC TOP_DEPTH_CONV BIT_WORD_CONV)) THEN
          CONV_TAC (TOP_DEPTH_CONV nocarry) THEN
          TRY (POP_ASSUM_LIST (fun asl => tactic_of do
            pure (MP_TAC (← endItlistM CONJ (← asl.reverse.mapM BITBLAST_EQUATION))))) THEN
          REWRITE_TAC [] THEN tac vars
        ExceptT.mk (t1 gl)))

  let BITBLAST_TAC : tactic ← pure (BITBLAST_THEN (fun vars => CONV_TAC (BDD_DEFTAUT vars)))

  let BITBLAST_RULE : term → ExceptT String IO thm ← pure (fun tm =>
    timeE (fun (tm, tac) => ExceptT.mk (HolCore.Tactics.prove HolBase.B tm tac))
      (tm, BITBLAST_TAC))

  -- @@RETURN BEGIN
  return { WORD_MUL_EXPAND_CONV, WORD_POPCOUNT_EXPAND_CONV,
           WORD_INEQ_RELATION_EXPAND_CONV, VAL_MOD_OR_DIV_CONV, BITBLAST_THEN,
           BITBLAST_TAC, BITBLAST_RULE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- SIMD repetition of a unary (usimd) or binary (simd) function.             -/
/- ------------------------------------------------------------------------- -/

structure Simd where
  -- @@FIELDS
  usimd2 : thm
  simd2 : thm
  usimd4 : thm
  simd4 : thm
  usimd8 : thm
  simd8 : thm
  usimd16 : thm
  simd16 : thm
  USIMD2 : thm
  SIMD2 : thm
  deriving Inhabited

@[nospecialize]
def setupSimd [HolBase] (D : WordsDeps) (BWordType : WordType) (BJoinSubword : JoinSubword) :
    ExceptT String IO Simd := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, new_definition, .. } := D
  let { ADD_CLAUSES, ADD_SUB2, DIMINDEX_TYBIT0, .. } := D.core1
  let { WORD_EQ_BITS_ALT, .. } := BWordType
  let { BIT_WORD_JOIN, BIT_WORD_SUBWORD, .. } := BJoinSubword
  -- @@SCOPE END
  let usimd2 ← new_definition
   r"(usimd2:(N word->M word)->((N)tybit0)word->((M)tybit0) word) f x =
    word_join (f (word_subword x (dimindex(:N),dimindex(:N))))
              (f (word_subword x (0,dimindex(:N))))"

  let simd2 ← new_definition
   r"(simd2:(N word->N word->N word)->
        ((N)tybit0)word->((N)tybit0) word->((N)tybit0) word) f x y =
    word_join (f (word_subword x (dimindex(:N),dimindex(:N)))
                 (word_subword y (dimindex(:N),dimindex(:N))))
              (f (word_subword x (0,dimindex(:N)))
                 (word_subword y (0,dimindex(:N))))"

  let usimd4 ← new_definition
   r"usimd4 (f:N word->M word) = usimd2 (usimd2 f)"

  let simd4 ← new_definition
   r"simd4 (f:N word->N word->N word) = simd2 (simd2 f)"

  let usimd8 ← new_definition
   r"usimd8 (f:N word->M word) = usimd2 (usimd4 f)"

  let simd8 ← new_definition
   r"simd8 (f:N word->N word->N word) = simd2 (simd4 f)"

  let usimd16 ← new_definition
   r"usimd16 (f:N word->M word) = usimd2 (usimd8 f)"

  let simd16 ← new_definition
   r"simd16 (f:N word->N word->N word) = simd2 (simd8 f)"

  let USIMD2 ← prove
   r"!(f:N word->M word) xhi xlo.
        usimd2 f (word_join xhi xlo) = word_join (f xhi) (f xlo)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [usimd2] THEN BINOP_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_SUBWORD, BIT_WORD_JOIN] THEN
    SIMP_TAC [ADD_CLAUSES, DIMINDEX_TYBIT0, ← ARITH_RULE (← q r"MIN x x = x"),
              ADD_SUB2, ← ARITH_RULE (← q r"i < n ==> i < 2 * n"),
              ← ARITH_RULE (← q r"n + i < 2 * n <=> i < n"),
              ← ARITH_RULE (← q r"~(n + i:num < n)")])

  let SIMD2 ← prove
   r"!(f:N word->N word->N word) xhi xlo yhi ylo.
        simd2 f (word_join xhi xlo) (word_join yhi ylo) =
        word_join (f xhi yhi) (f xlo ylo)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [simd2] THEN BINOP_TAC THEN BINOP_TAC THEN
    REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_SUBWORD, BIT_WORD_JOIN] THEN
    SIMP_TAC [ADD_CLAUSES, DIMINDEX_TYBIT0, ← ARITH_RULE (← q r"MIN x x = x"),
              ADD_SUB2, ← ARITH_RULE (← q r"i < n ==> i < 2 * n"),
              ← ARITH_RULE (← q r"n + i < 2 * n <=> i < n"),
              ← ARITH_RULE (← q r"~(n + i:num < n)")])

  -- @@RETURN BEGIN
  return { usimd2, simd2, usimd4, simd4, usimd8, simd8, usimd16, simd16, USIMD2, SIMD2 }
  -- @@RETURN END

end HolLibrary.Words
