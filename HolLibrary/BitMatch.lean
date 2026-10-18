/- ========================================================================= -/
/-           Parsing and printing for bitmatch expressions.                  -/
/- ========================================================================= -/
/- File: HolLibrary/BitMatch.lean

  Lean4 translation by Chris Walton 2026
  Original (c) Copyright, Mario Carneiro 2020

  A translation of HOL Light's `Library/bitmatch.ml`, by hand, in file
  order, in the style of HolLibrary/Card.lean (see there and
  HolMath/Base.lean for the conventions).  bitmatch.ml begins with
  `needs "Library/words.ml"`; the words.ml names it uses come through
  `BitMatchDeps` (CoreThms2 and the conversions).

  bitmatch.ml installs a quotation parser (`bitmatch e with ...` and
  `BITPAT [...]`) and term printers.  HolCore's user-parser and
  user-printer hooks are IO-valued (HolCore/Parser.lean, Printer.lean), as
  OCaml's read the live parser and printer tables.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left; where a proof applies two or more rules that
  print or use counters they are bound first, in OCaml's order.
-/

import HolMath

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB BETA ABS INST_TYPE EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolCore.Preterm (preterm pretype dpty)
open HolCore.Parser (lexcode PErr Ctx ParserM)
open HolLight HolLight.Syntax

namespace HolLibrary.BitMatch

/- ------------------------------------------------------------------------- -/
/- What bitmatch.ml uses from the core library and words.ml.                 -/
/- ------------------------------------------------------------------------- -/

/-- Theorems bitmatch.ml uses from the core library. -/
structure CoreThms1 where
  (ADD ADD_0 ADD_SYM ARITH_ZERO BIT0_0 BIT1_0 CONG DIMINDEX_CLAUSES DIVISION
   DIV_1 DIV_DIV DIV_LT DIV_MOD DIV_MULT_ADD EVEN_ADD EVEN_DOUBLE EVEN_MOD
   EXISTS_DEF EXP EXP_1 EXP_2_NE_0 EXP_ADD LE_MULT_LCANCEL LE_SUC_LT
   LTE_TRANS LT_ADD_RCANCEL MOD_ADD_MOD MOD_MOD MOD_MOD_REFL MOD_MULT
   MOD_MULT_ADD MULT_AC MULT_SUC MULT_SYM NOT_EVEN NOT_EXISTS_THM NOT_ODD
   NUMERAL ODD_MOD ONE RDIV_LT_EQ SND _MATCH _SEQPATTERN _UNGUARDED_PATTERN
   o_DEF : thm)
  deriving Inhabited

/-- Theorems bitmatch.ml uses from words.ml. -/
structure CoreThms2 where
  (BITVAL_CLAUSES BIT_LSB NUMBIT_VAL VAL_BOUND VAL_WORD VAL_WORD_BITVAL
   VAL_WORD_EQ WORD_EQ WORD_VAL WORD_VAL_GALOIS bitval num_shift_add
   num_shift_add_0 num_shift_add_SUC numbit : thm)
  deriving Inhabited

/-- What bitmatch.ml uses from Session besides theorems. -/
structure BitMatchDeps where
  -- definitions and parser state
  new_definition : String → ExceptT String IO thm
  new_type_definition : String → String × String → thm → ExceptT String IO thm
  prioritize_num : IO Unit
  mk_numeral : Rat → Except String term
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  DIMINDEX_TAC : tactic
  IMP_REWRITE_TAC : List thm → tactic
  MESON : List thm → term → ExceptT String IO thm
  METIS : List thm → term → ExceptT String IO thm
  METIS_TAC : List thm → tactic
  NUM_REDUCE_TAC : tactic
  -- conversions and rules
  DIMINDEX_CONV : ioconv
  ETA_CONV : ioconv
  let_CONV : ioconv
  NUM_ADD_CONV : ioconv
  NUM_LT_CONV : ioconv
  NUM_REDUCE_CONV : ioconv
  NUMBIT_CONV : ioconv
  WORD_RED_CONV : ioconv
  NUM_SHIFT_ADD_CORE : term → term → term → ExceptT String IO thm
  core1 : CoreThms1
  core2 : CoreThms2

/-- OCaml's `Invalid_argument`, kept apart from `Failure`: a `Failure`
    handler does not catch it. -/
def invalidArgPrefix : String := "Invalid_argument "

/-- `failwith "..."` from an error that may be an `Invalid_argument`. -/
def isInvalidArg (e : String) : Bool := e.startsWith invalidArgPrefix

/-- A `Rat` (from `dest_finty` / `dest_numeral`) as a `Nat`. -/
def ratNat (r : Rat) : Nat := r.floor.toNat

/- ------------------------------------------------------------------------- -/
/- TRIV_CHOOSE, WITH_GOAL; the bitpat type, NILPAT, CONSPAT, word1.          -/
/- (bitmatch.ml 19-111)                                                      -/
/- ------------------------------------------------------------------------- -/

structure Defs where
  -- @@FIELDS
  TRIV_CHOOSE : thm → thm → ExceptT String IO thm
  WITH_GOAL : (term → tactic) → tactic
  _BITMATCH : thm
  _ELSEPATTERN : thm
  bitpat : thm
  pat_size : thm
  pat_set : thm
  pat_set_lt : thm
  pat_thm : thm
  NILPAT : thm
  NILPAT_pat_size : thm
  NILPAT_pat_set : thm
  CONSPAT : thm
  CONSPAT_pat_size : thm
  CONSPAT_pat_set : thm
  word1 : thm
  BIT0_WORD1 : thm
  VAL_WORD1 : thm
  WORD1_ODD : thm
  deriving Inhabited

@[nospecialize]
def setupDefs [HolBase] (D : BitMatchDeps) :
    ExceptT String IO Defs := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, DIMINDEX_TAC, NUM_REDUCE_CONV, let_CONV, new_definition,
        new_type_definition, prioritize_num, .. } := D
  let { CONG, DIMINDEX_CLAUSES, EVEN_MOD, EXISTS_DEF, EXP_1, EXP_ADD, LE_MULT_LCANCEL,
        LE_SUC_LT, LTE_TRANS, LT_ADD_RCANCEL, MULT_SUC, NOT_ODD, ODD_MOD, SND, .. } := D.core1
  let { BITVAL_CLAUSES, BIT_LSB, VAL_BOUND, VAL_WORD, VAL_WORD_BITVAL, WORD_EQ, bitval, .. } := D.core2
  -- @@SCOPE END

  prioritize_num

  -- Like CHOOSE, but the variable is the same as the one in the existential

  let TRIV_CHOOSE : thm → thm → ExceptT String IO thm ← do
    -- `let P = ... and Q = ... and an = ...`, left to right.
    let P ← q r"P:A->bool"
    let Q ← q "Q:bool"
    let an ← q r"(/\)"
    let pth ← do  -- `(\x:A. Q /\ P x) = P, (?) P |- Q`
      let th1 ← AP_THM (← ASSUME (← q r"(\x:A. Q /\ P x) = P")) (← q "x:A")
      let th1 ← TRANS (← SYM th1) (← liftExcept (HolCore.Kernel.BETA (← q r"(\x:A. Q /\ P x) x")))
      let th1 ← CONJUNCT1 (← EQ_MP th1 (← ASSUME (← q r"(P:A->bool) x")))
      let th1 ← GEN (← q "x:A") (← DISCH (← q r"(P:A->bool) x") th1)
      let th2 ← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM EXISTS_DEF P)
      MP (← SPEC (← q "Q:bool") (← EQ_MP th2 (← ASSUME (← q r"(?) (P:A->bool)")))) th1
    let aty := mk_vartype "A"
    pure (fun th1 th2 => tryCatch (do
      let P' ← liftExcept (rand (concl th1))
      let (v, bod) ← liftExcept (dest_abs P')
      let Q' := concl th2
      let anQ ← liftExcept (mk_comb an Q')
      let th3 := HolCore.Kernel.DEDUCT_ANTISYM_RULE (← CONJ th2 (← ASSUME bod))
        (← CONJUNCT2 (← ASSUME (← liftExcept (mk_comb anQ bod))))
      let th4 ← AP_TERM anQ (← liftExcept (HolCore.Kernel.BETA (← liftExcept (mk_comb P' v))))
      let th5 ← PINST [((← liftExcept (dest_var v)).2, aty)] [(P', P), (Q', Q)] pth
      PROVE_HYP th1 (← PROVE_HYP (← liftExcept (HolCore.Kernel.ABS v (← TRANS th4 th3))) th5))
      (fun e => throw (if isInvalidArg e || e == "Match_failure" then e else "TRIV_CHOOSE")))

  let WITH_GOAL : (term → tactic) → tactic ← pure (fun tac st => tac st.2 st)

  let _BITMATCH ← new_definition r"_BITMATCH (s:N word) c = _MATCH (val s) c"
  let _ELSEPATTERN ← new_definition r"_ELSEPATTERN (e:B) (a:A) = \x. e = x"

  let bitpat ← do
    let th ← prove
      r"?x:num#(num->bool). !a. SND x a ==> a < 2 EXP FST x"
      (EXISTS_TAC (← q r"0, \i:num. F") THEN REWRITE_TAC [SND])
    new_type_definition "bitpat" ("mk_bitpat", "dest_bitpat") th

  let pat_size ← new_definition r"pat_size p = FST (dest_bitpat p)"
  let pat_set ← new_definition r"pat_set p = SND (dest_bitpat p)"

  let pat_set_lt ← prove r"!p s. pat_set p s ==> s < 2 EXP pat_size p"
    (REWRITE_TAC [pat_set, pat_size, bitpat])

  let pat_thm ← prove r"p = mk_bitpat (n, f) /\ (!a. f a ==> a < 2 EXP n) ==>
  pat_size p = n /\ !s. pat_set p s = f s"
    (REPEAT DISCH_TAC THEN
     SUBGOAL_THEN (← q "dest_bitpat (mk_bitpat (n,f)) = (n,f)")
       (fun th => ASM_REWRITE_TAC [pat_size, pat_set, th]) THEN
     ASM_REWRITE_TAC [← GSYM (← CONJUNCT2 bitpat)] THEN
     FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP pat_set_lt))

  let NILPAT ← new_definition r"NILPAT = mk_bitpat(0,\s:num. s = 0)"

  let (NILPAT_pat_size, NILPAT_pat_set) ← CONJ_PAIR (← prove
   r"pat_size NILPAT = 0 /\ !s. pat_set NILPAT s <=> s = 0"
   (MATCH_MP_TAC pat_thm THEN REWRITE_TAC [NILPAT] THEN
    STRIP_TAC THEN DISCH_THEN SUBST1_TAC THEN ARITH_TAC))

  let CONSPAT ← new_definition r"CONSPAT p (a:N word) =
  let n = dimindex(:N) in
  mk_bitpat(n + pat_size p,
    \s:num. (?t. pat_set p t /\ s = val a + 2 EXP n * t))"

  let (CONSPAT_pat_size, CONSPAT_pat_set) ← CONJ_PAIR (← prove
   r"pat_size (CONSPAT p (a:N word)) = dimindex(:N) + pat_size p /\
   !s. pat_set (CONSPAT p (a:N word)) s <=>
     ?t. pat_set p t /\ s = val a + 2 EXP dimindex(:N) * t"
   (MATCH_MP_TAC pat_thm THEN
    REWRITE_TAC [← CONV_RULE (ONCE_DEPTH_CONV let_CONV) CONSPAT] THEN
    REPEAT STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC (← q "2 EXP dimindex (:N) * SUC t") THEN
    POP_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [EXP_ADD, LE_MULT_LCANCEL, LE_SUC_LT,
      ← MATCH_MP pat_set_lt th])) THEN
    REWRITE_TAC [MULT_SUC, LT_ADD_RCANCEL, VAL_BOUND]))

  HolCore.Printer.reserve_words ["BITPAT", "bitmatch"]

  let word1 ← new_definition r"word1 p = (word (bitval p)):1 word"

  let BIT0_WORD1 ← prove r"bit 0 (word1 b) = b"
    (REWRITE_TAC [word1, BIT_LSB, bitval, VAL_WORD] THEN DIMINDEX_TAC THEN
     BOOL_CASES_TAC (← q "b:bool") THEN REWRITE_TAC [] THEN ARITH_TAC)

  let VAL_WORD1 ← prove r"val (word1 b) = bitval b"
    (REWRITE_TAC [word1, VAL_WORD_BITVAL])

  let WORD1_ODD ← prove r"word1 (ODD n) = word n"
    (CONV_TAC SYM_CONV THEN REWRITE_TAC [word1, WORD_EQ, DIMINDEX_CLAUSES] THEN
     ASM_CASES_TAC (← q "ODD n") THEN
     ASM_REWRITE_TAC [ODD_MOD, BITVAL_CLAUSES, EXP_1, CONG] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     ASM_REWRITE_TAC [← GSYM EVEN_MOD, ← GSYM ODD_MOD, ← GSYM NOT_ODD])

  -- @@RETURN BEGIN
  return { TRIV_CHOOSE, WITH_GOAL, _BITMATCH, _ELSEPATTERN, bitpat, pat_size, pat_set,
           pat_set_lt, pat_thm, NILPAT, NILPAT_pat_size, NILPAT_pat_set, CONSPAT,
           CONSPAT_pat_size, CONSPAT_pat_set, word1, BIT0_WORD1, VAL_WORD1, WORD1_ODD }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- The parser for `BITPAT [...]` and `bitmatch e with ...`, and the          -/
/- printers.  (bitmatch.ml 113-286)                                          -/
/- ------------------------------------------------------------------------- -/

open HolCore.Parser (parse_preterm mkCtx pmapM pmapMIO pseqM porM paM ppossiblyM plistofM)
open HolCore.System (Fmt)

/-- A bitmatch printer (`formatter -> term -> unit` in OCaml): the term's
    output, or a failure if the term is not of the printer's form. -/
abbrev TermPrinter := term → IO (Except String (Fmt Unit))

/-- `to_bitpat p e`: the CONS/NIL list preterm `e` as a CONSPAT chain onto
    `p`; `Noparse` (backtrack) if `e` is not a list. -/
partial def toBitpat (p e : preterm) : Except PErr preterm :=
  let CONSPAT_ptm := preterm.Varp "CONSPAT" dpty
  let word_ptm := preterm.Varp "word" dpty
  let word1_ptm := preterm.Varp "word1" dpty
  match e with
  | .Varp "NIL" _ => .ok p
  | .Combp (.Combp (.Varp "CONS" _) a) e =>
    let e2 := match a with
      | .Typing a i =>
          let a := match a with
            | .Varp s _ => if (num_of_string s).toOption.isSome then preterm.Combp word_ptm a else a
            | _ => a
          preterm.Typing a (.Ptycon "word" [i])
      | a => preterm.Combp word1_ptm a
    toBitpat (.Combp (.Combp CONSPAT_ptm p) e2) e
  | _ => .error .noparse

/-- `pfrees ptm`: the free variables of a pattern preterm (names that are not
    constants, numerals or interface names), in OCaml's `union` order. -/
partial def pfrees (c : Ctx) (ptm : preterm) : List preterm :=
  match ptm with
  | .Varp v pty =>
      if v == "" && pty == dpty then []
      else if c.can_get_const_type v || (num_of_string v).toOption.isSome
              || c.interfaceTbl.any (fun (w, _) => v == w) then []
      else [ptm]
  | .Constp _ _ => []
  | .Combp p1 p2 => union (pfrees c p1) (pfrees c p2)
  | .Absp p1 p2 => subtract (pfrees c p2) (pfrees c p1)
  | .Typing p _ => pfrees c p

/-- `pmk_clauses` (with `pmk_clauses_opt` unfolded): the `_SEQPATTERN` chain
    of the clauses, ending in `_ELSEPATTERN` of the `_` clause's result, or
    of `ARB`. -/
def pmkClauses (c : Ctx) (x y : preterm) : List (Option preterm × preterm) → preterm
  | [] => .Combp (.Varp "_ELSEPATTERN" dpty) (.Varp "ARB" dpty)
  | (none, res) :: _ => .Combp (.Varp "_ELSEPATTERN" dpty) res
  | (some pat, res) :: cs =>
    let pmk_exists (v ptm : preterm) : preterm := .Combp (.Varp "?" dpty) (.Absp v ptm)
    let tx := preterm.Combp (.Combp (.Varp "pat_set" dpty) pat) x
    let ty := preterm.Combp (.Combp (.Varp "=" dpty) res) y
    let t := itlist pmk_exists (pfrees c pat) (.Combp (.Combp (.Varp "_UNGUARDED_PATTERN" dpty) tx) ty)
    .Combp (.Combp (.Varp "_SEQPATTERN" dpty) (.Absp x (.Absp y t))) (pmkClauses c x y cs)

structure Syntax where
  -- @@FIELDS
  preparse_bitpat : HolCore.Parser.UserParser
  preparse_bitmatch : HolCore.Parser.UserParser
  pp_print_bitpat : TermPrinter
  pp_print_colored_bitpat : TermPrinter
  pp_print_bitmatch : TermPrinter
  pp_print_colored_bitmatch : TermPrinter
  print_bitpat : term → IO Unit
  string_of_bitpat : term → ExceptT String IO String
  print_bitmatch : term → IO Unit
  string_of_bitmatch : term → ExceptT String IO String
  deriving Inhabited

@[nospecialize]
def setupSyntax [HolBase] (D : BitMatchDeps) :
    ExceptT String IO Syntax := do
  -- @@SCOPE BEGIN
  let _ := D
  -- @@SCOPE END

  let (preparse_bitpat, preparse_bitmatch) : HolCore.Parser.UserParser × HolCore.Parser.UserParser ← do
    let bitmatch_ptm := preterm.Varp "_BITMATCH" dpty
    let NILPAT_ptm := preterm.Varp "NILPAT" dpty
    let gcounter ← (IO.mkRef 0 : IO (IO.Ref Nat))
    let pgenvar : IO preterm := do
      let count ← gcounter.get
      gcounter.set (count + 1)
      pure (.Varp ("BM%PVAR%" ++ toString count) dpty)
    let pmk_bitmatch (c : Ctx) (x : ((lexcode × preterm) × lexcode) × List (Option preterm × preterm)) :
        IO preterm := do
      let (((_, e), _), cs) := x
      -- `let x = pgenvar() and y = pgenvar()`, left to right.
      let x ← pgenvar
      let y ← pgenvar
      pure (.Combp (.Combp bitmatch_ptm e) (pmkClauses c x y cs))
    let bitpatP : ParserM preterm := fun c inp => do
      match ← parse_preterm c inp with
      | .error e => pure (.error e)
      | .ok (e, rest) =>
        match toBitpat NILPAT_ptm e with
        | .ok p => pure (.ok (p, rest))
        | .error err => pure (.error err)
    let patternP : ParserM (Option preterm) :=
      porM (pmapM (paM (.Ident "_")) (fun _ => none)) (pmapM bitpatP some)
    let clauseP : ParserM (Option preterm × preterm) :=
      pseqM patternP (pmapM (pseqM (paM (.Resword "->")) parse_preterm) Prod.snd)
    let clausesP : ParserM (List (Option preterm × preterm)) :=
      pmapM (pseqM (ppossiblyM (paM (.Resword "|")))
        (plistofM clauseP (paM (.Resword "|")) "pattern-match clause")) Prod.snd
    let pb : HolCore.Parser.UserParser := fun inp => do
      (pmapM (pseqM (paM (.Resword "BITPAT")) bitpatP) Prod.snd) (← mkCtx) inp
    let pm : HolCore.Parser.UserParser := fun inp => do
      let c ← mkCtx
      (pmapMIO (pseqM (pseqM (pseqM (paM (.Resword "bitmatch")) parse_preterm)
          (paM (.Resword "with"))) clausesP) (pmk_bitmatch c)) c inp
    pure (pb, pm)

  HolCore.Parser.install_parser ("bitpat", preparse_bitpat)
  HolCore.Parser.install_parser ("bitmatch", preparse_bitmatch)

  let (pp_print_bitpat, pp_print_colored_bitpat, pp_print_bitmatch, pp_print_colored_bitmatch) : TermPrinter × TermPrinter × TermPrinter × TermPrinter ← do
    let switch_color (use_color : Bool) : TermPrinter × TermPrinter :=
      -- color printer setting
      let pp_term : term → IO (Fmt Unit) :=
        if use_color then HolCore.Printer.pp_print_colored_term else HolCore.Printer.pp_print_term
      let pp_type : hol_type → IO (Fmt Unit) :=
        if use_color then HolCore.Printer.pp_print_colored_type
        else fun ty => pure (HolCore.Printer.pp_print_type ty)
      let pp_resword : String → IO (Fmt Unit) :=
        if use_color then HolCore.Printer.pp_print_colored_resword
        else fun s => pure (Fmt.printString s)
      let rec dest_pat_rev (tm : term) : Except String (List term) :=
        match tm with
        | .Comb (.Comb (.Const "CONSPAT" _) p) a => do return a :: (← dest_pat_rev p)
        | .Const "NILPAT" _ => .ok []
        | _ => failwith "dest_pat"
      let dest_pat (tm : term) : Except String (List term) := do return rev (← dest_pat_rev tm)
      let dest_clause (tm : term) : Except String (List term × term) := do
        match (strip_exists (← body (← body tm))).2 with
        | .Comb (.Comb (.Const "_UNGUARDED_PATTERN" _) lhs)
            (.Comb (.Comb (.Const "=" _) res) _) =>
          match lhs with
          | .Comb (.Comb (.Const "pat_set" _) pat) _ => return (← dest_pat pat, res)
          | _ => failwith "dest_clause"
        | _ => failwith "dest_clause"
      let rec dest_clauses (tm : term) : Except String (List (List term × term) × term) :=
        match tm with
        | .Comb (.Comb (.Const "_SEQPATTERN" _) c) cs => do
            let c ← dest_clause c
            let (l, r) ← dest_clauses cs
            return (c :: l, r)
        | .Comb (.Const "_ELSEPATTERN" _) res => .ok ([], res)
        | _ => failwith "dest_clauses"
      let unword (i : hol_type) (a : term) : Except String term :=
        match a with
        | .Comb (.Const "word" _) a' =>
          if HolMath.Nums.is_numeral a' then do
            if (← dest_numeral a') < (2 : Rat) ^ (ratNat (← dest_finty i)) then return a'
            else failwith "numeral out of range"
          else .ok a
        | _ => .ok a
      let print_pat (a : term) : IO (Except String (Fmt Unit)) := do
        match a with
        | .Comb (.Const "word1" _) a' => return .ok (← pp_term a')
        | _ =>
          match type_of a with
          | .Tyapp "word" [i] =>
            match unword i a with
            | .error e => return .error e
            | .ok a' =>
              let t ← pp_term a'
              let ty ← pp_type i
              return .ok (do t; Fmt.printString ":"; ty)
          | _ => return failwith "print_pat"
      let print_opat (op : Option (List term)) : IO (Except String (Fmt Unit)) := do
        match op with
        | none => return .ok (Fmt.printString "_")
        | some [] => return .ok (Fmt.printString "[]")
        | some (x :: xs) =>
          match ← print_pat x with
          | .error e => return .error e
          | .ok px =>
            let mut acc : Fmt Unit := do Fmt.printString "["; px
            for x in xs do
              match ← print_pat x with
              | .error e => return .error e
              | .ok p => acc := do acc; Fmt.printString "; "; p
            return .ok (do acc; Fmt.printString "]")
      let print_clause (p : Option (List term)) (r : term) : IO (Except String (Fmt Unit)) := do
        match ← print_opat p with
        | .error e => return .error e
        | .ok po =>
          let rt ← pp_term r
          return .ok (do po; Fmt.printString " -> "; rt)
      let rec print_clauses (cls : List (List term × term)) (r : term) :
          IO (Except String (Fmt Unit)) := do
        match cls, r with
        | [(p, res)], .Const "ARB" _ => print_clause (some p) res
        | (p, res) :: cs, _ =>
          match ← print_clause (some p) res with
          | .error e => return .error e
          | .ok pc =>
            match ← print_clauses cs r with
            | .error e => return .error e
            | .ok rest => return .ok (do pc; Fmt.printBreak 1 0; Fmt.printString "| "; rest)
        | [], r => print_clause none r
      let pp_print_bitpat : TermPrinter := fun tm => do
        match dest_pat tm with
        | .error e => return .error e
        | .ok pat =>
          match ← print_opat (some pat) with
          | .error e => return .error e
          | .ok po => return .ok (do
              Fmt.openHvBox 0
              Fmt.printString "(BITPAT"
              Fmt.printSpace
              po
              Fmt.printString ")"
              Fmt.closeBox)
      let pp_print_bitmatch : TermPrinter := fun tm => do
        match tm with
        | .Comb (.Comb (.Const "_BITMATCH" _) e) c =>
          match dest_clauses c with
          | .error e => return .error e
          | .ok (cls, r) =>
            let bm ← pp_resword "bitmatch "
            let et ← pp_term e
            let wi ← pp_resword " with"
            match ← print_clauses cls r with
            | .error e => return .error e
            | .ok pcs => return .ok (do
                Fmt.openHvBox 0
                Fmt.printString "("
                bm
                et
                wi
                Fmt.printBreak 1 2
                pcs
                Fmt.closeBox
                Fmt.printString ")")
        | _ => return failwith "print_bitmatch"
      (pp_print_bitpat, pp_print_bitmatch)
    -- `let ppbitpat,ppbitmatch = switch_color false and ... = switch_color true`
    let (ppbitpat, ppbitmatch) := switch_color false
    let (ppbitpatcol, ppbitmatchcol) := switch_color true
    pure (ppbitpat, ppbitpatcol, ppbitmatch, ppbitmatchcol)

  let print_bitpat : term → IO Unit ← pure (fun tm => do
    match ← pp_print_bitpat tm with
    | .ok f => IO.print (Fmt.run (← HolCore.Printer.get_margin) f)
    | .error e => throw (IO.userError e))
  let string_of_bitpat : term → ExceptT String IO String ← pure (fun tm => do
    let f ← ExceptT.mk (pp_print_bitpat tm)
    pure (Fmt.run (← HolCore.Printer.get_margin) f))

  let print_bitmatch : term → IO Unit ← pure (fun tm => do
    match ← pp_print_bitmatch tm with
    | .ok f => IO.print (Fmt.run (← HolCore.Printer.get_margin) f)
    | .error e => throw (IO.userError e))
  let string_of_bitmatch : term → ExceptT String IO String ← pure (fun tm => do
    let f ← ExceptT.mk (pp_print_bitmatch tm)
    pure (Fmt.run (← HolCore.Printer.get_margin) f))

  HolCore.Printer.install_user_printer ("bitpat", pp_print_bitpat)
  HolCore.Printer.install_user_printer ("bitmatch", pp_print_bitmatch)
  HolCore.Printer.install_user_color_printer ("bitpat", pp_print_colored_bitpat)
  HolCore.Printer.install_user_color_printer ("bitmatch", pp_print_colored_bitmatch)

  -- @@RETURN BEGIN
  return { preparse_bitpat, preparse_bitmatch, pp_print_bitpat, pp_print_colored_bitpat,
           pp_print_bitmatch, pp_print_colored_bitmatch, print_bitpat, string_of_bitpat,
           print_bitmatch, string_of_bitmatch }
  -- @@RETURN END

/-- `bm_analyze_pat`'s `go` (bitmatch.ml 437-470) on a functional array.
    OCaml's `Invalid_argument` (from the length check, `A.(i) <- ...` out of
    bounds, or `Array.fill`) is an error with `invalidArgPrefix`. -/
partial def bmAnalyzeGo (sz : Nat) (i : Nat) (tm : term) (A : Array (Option Bool)) :
    Except String (Array (Option Bool)) := do
  let setA (A : Array (Option Bool)) (k : Nat) (v : Option Bool) : Except String (Array (Option Bool)) :=
    if k < A.size then .ok (A.set! k v) else .error (invalidArgPrefix ++ "index out of bounds")
  let fillA (A : Array (Option Bool)) (k : Nat) (len : Int) (v : Option Bool) :
      Except String (Array (Option Bool)) :=
    if len < 0 || k + len.toNat > A.size then .error (invalidArgPrefix ++ "Array.fill")
    else .ok ((List.range len.toNat).foldl (fun A j => A.set! (k + j) v) A)
  match tm with
  | .Comb (.Comb (.Const "CONSPAT" _) p) a =>
    let n := ratNat (← dest_finty (← (match type_of a with
      | .Tyapp "word" [i] => .ok i | _ => failwith "dest_word_ty")))
    if i + n > sz then throw (invalidArgPrefix ++ "incorrect bit length")
    let A ← match a with
      | .Comb (.Const "word1" _) a =>
        match a with
        | .Const "T" _ => setA A i (some true)
        | .Const "F" _ => setA A i (some false)
        | .Var _ _ => setA A i none
        | _ => failwith "bm_analyze_pat"
      | .Comb (.Const "word" _) (.Comb (.Const "NUMERAL" _) a) =>
        let rec analyze_num (n : Nat) (a : term) (A : Array (Option Bool)) :
            Except String (Array (Option Bool)) :=
          match a with
          | .Comb (.Const "BIT0" _) a => do analyze_num (n + 1) a (← setA A n (some false))
          | .Comb (.Const "BIT1" _) a => do analyze_num (n + 1) a (← setA A n (some true))
          | .Const "_0" _ => fillA A n ((sz : Int) - n) (some false)
          | _ => failwith "bm_analyze_pat"
        analyze_num i a A
      | .Var _ _ => fillA A i n none
      | _ => failwith "bm_analyze_pat"
    bmAnalyzeGo sz (i + n) p A
  | .Const "NILPAT" _ =>
    if i == sz then .ok A else throw (invalidArgPrefix ++ "incorrect bit length")
  | .Abs _ c => bmAnalyzeGo sz i c A
  | .Comb (.Const "?" _) c => bmAnalyzeGo sz i c A
  | .Comb (.Comb (.Const "_UNGUARDED_PATTERN" _) c) _ => bmAnalyzeGo sz i c A
  | .Comb (.Comb (.Const "pat_set" _) c) _ => bmAnalyzeGo sz i c A
  | _ => failwith "bm_analyze_pat"

/-- The constants and rules `PAT_EXTRACT_THM`'s `go` closes over. -/
structure PatExtractCtx where
  (word1_eq word_lt word_skip : thm)
  N : hol_type
  (n m i p b di nb pl lt : term)
  (DIMINDEX_CONV NUMBIT_CONV NUM_LT_CONV NUM_ADD_CONV : ioconv)
  mk_numeral : Rat → Except String term

/-- `PAT_EXTRACT_THM`'s `go` (bitmatch.ml 379-406). -/
partial def patExtractGo [HolBase] (C : PatExtractCtx) (x : term × term) :
    ExceptT String IO thm := do
  let { word1_eq, word_lt, word_skip, N, n, m, i, p, b, di, nb, pl, lt,
        DIMINDEX_CONV, NUMBIT_CONV, NUM_LT_CONV, NUM_ADD_CONV, mk_numeral } := C
  match x with
  | (.Comb (.Comb (.Const "CONSPAT" _) p') a', i') =>
    let i'' ← liftExcept (dest_numeral i')
    let aty := type_of a'
    let N' ← match aty with
      | .Tyapp _ [N'] => pure N'
      | _ => throw "Match_failure"
    let n'' ← liftExcept (dest_finty N')
    if i'' < n'' then
      match a' with
      | .Comb (.Const "word1" _) b' => INST [(p', p), (b', b)] word1_eq
      | .Comb (.Const "word" _) m' =>
        if HolMath.Nums.is_numeral m' then do
          let th ← INST_TYPE [(N', N)] word_lt
          let th1 ← ExceptT.mk (DIMINDEX_CONV (inst [(N', N)] di))
          let n' ← liftExcept (rhs (concl th1))
          let th2 ← ExceptT.mk (NUMBIT_CONV (← liftExcept (mk_comb (← liftExcept (mk_comb nb i')) m')))
          let b' ← liftExcept (rhs (concl th2))
          let th3 ← ExceptT.mk (NUM_LT_CONV (← liftExcept (mk_comb (← liftExcept (mk_comb lt i')) n')))
          let t ← INST [(i', i), (m', m), (n', n), (p', p), (b', b)] th
          PROVE_HYP th3 (← PROVE_HYP th2 (← PROVE_HYP th1 t))
        else throw "PAT_EXTRACT_THM: not a constant at this position"
      | _ => throw "PAT_EXTRACT_THM: not a constant at this position"
    else do
      let th ← INST_TYPE [(N', N)] word_skip
      let th1 ← ExceptT.mk (DIMINDEX_CONV (inst [(N', N)] di))
      let n' ← liftExcept (rhs (concl th1))
      let m' ← liftExcept (mk_numeral (i'' - n''))
      let th2 ← ExceptT.mk (NUM_ADD_CONV (← liftExcept (mk_comb (← liftExcept (mk_comb pl m')) n')))
      let th3 ← patExtractGo C (p', m')
      let b' ← liftExcept (rand (concl th3))
      let t ← INST [(i', i), (m', m), (n', n), (p', p), (b', b), (a', mk_var "a" aty)] th
      PROVE_HYP th3 (← PROVE_HYP th2 (← PROVE_HYP th1 t))
  | _ => throw "PAT_EXTRACT_THM: out of range"

/- ------------------------------------------------------------------------- -/
/- Some tactics for dealing with bitmatch: SPLIT_IF, the SEQPATTERN and      -/
/- ELSEPATTERN lemmas, pat_extract, pat_to_bit, pattern analysis, skipping   -/
/- a clause.  (bitmatch.ml 288-526)                                          -/
/- ------------------------------------------------------------------------- -/

structure Analyze where
  -- @@FIELDS
  dest_word_ty : hol_type → ExceptT String IO hol_type
  SPLIT_IF : term → thm → thm → ExceptT String IO thm
  MATCH_SEQPATTERN : thm
  BITMATCH_SEQPATTERN : thm
  BITMATCH_SEQPATTERN2 : thm
  MATCH_ELSEPATTERN : thm
  BITMATCH_ELSEPATTERN : thm
  pat_extract : thm
  PAT_EXTRACT_THM : term × term → ExceptT String IO thm
  pat_to_bit : Bool → term → term → ExceptT String IO thm
  bm_analyze_pat : Nat → term → ExceptT String IO (Array (Option Bool))
  bm_analyze_clauses : Nat → term → ExceptT String IO (List (Array (Option Bool)))
  bm_skip_clause : (term → ExceptT String IO thm) → term → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupAnalyze [HolBase] (D : BitMatchDeps) (BDefs : Defs) :
    ExceptT String IO Analyze := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, DIMINDEX_CONV, DIMINDEX_TAC, ETA_CONV, IMP_REWRITE_TAC,
        METIS_TAC, NUMBIT_CONV, NUM_ADD_CONV, NUM_LT_CONV, NUM_REDUCE_TAC, mk_numeral,
        new_definition, .. } := D
  let { ADD, ADD_0, ADD_SYM, DIV_1, DIV_DIV, DIV_LT, DIV_MOD, DIV_MULT_ADD, EVEN_ADD,
        EVEN_DOUBLE, EXP, EXP_2_NE_0, EXP_ADD, LE_SUC_LT, MOD_ADD_MOD, MOD_MOD,
        MOD_MOD_REFL, MOD_MULT, MULT_AC, MULT_SYM, NOT_EVEN, ODD_MOD, _MATCH,
        _SEQPATTERN, _UNGUARDED_PATTERN, .. } := D.core1
  let { NUMBIT_VAL, VAL_BOUND, VAL_WORD, bitval, numbit, .. } := D.core2
  let { CONSPAT_pat_set, _BITMATCH, _ELSEPATTERN, word1, .. } := BDefs
  -- @@SCOPE END

  let dest_word_ty : hol_type → ExceptT String IO hol_type ← pure (fun ty =>
    match ty with
    | .Tyapp "word" [i] => pure i
    | _ => throw "dest_word_ty")

  let SPLIT_IF : term → thm → thm → ExceptT String IO thm ← do
    let th ← UNDISCH_ALL (← TAUT
      (← q r"(p ==> a:A = t1) ==> (~p ==> a = t2) ==> a = if p then t1 else t2"))
    let (a, A, p, t1, t2) ← match frees (concl th) with
      | (.Var n A) :: p :: t1 :: t2 :: [] => pure (term.Var n A, A, p, t1, t2)
      | _ => throw "Match_failure"
    let tnot ← q "~"
    pure (fun p' th1 th2 => do
      let (a', t1') ← liftExcept (dest_eq (concl th1))
      let t2' := (← liftExcept (dest_eq (concl th2))).2
      let th' ← PINST [(type_of a', A)] [(p', p), (a', a), (t1', t1), (t2', t2)] th
      let th' ← PROVE_HYP (← DISCH (← liftExcept (mk_comb tnot p')) th2) th'
      PROVE_HYP (← DISCH p' th1) th')

  let MATCH_SEQPATTERN ← prove
   r"_MATCH (e:A) (_SEQPATTERN c cs) =
   if ?y:B. c e y then _MATCH e c else _MATCH e cs"
   (COND_CASES_TAC THEN ASM_REWRITE_TAC [_MATCH, _SEQPATTERN])

  let BITMATCH_SEQPATTERN ← prove
   r"_BITMATCH (e:N word) (_SEQPATTERN c cs) =
   if ?y:B. c (val e) y then _BITMATCH e c else _BITMATCH e cs"
   (REWRITE_TAC [_BITMATCH, MATCH_SEQPATTERN])

  let BITMATCH_SEQPATTERN2 ← prove
   r"_BITMATCH (e:N word) (_SEQPATTERN c cs) =
   if ?y:B. c (val e) y then
     _BITMATCH e (_SEQPATTERN c (_ELSEPATTERN ARB))
   else _BITMATCH e cs"
   (REWRITE_TAC [BITMATCH_SEQPATTERN] THEN COND_CASES_TAC THEN REWRITE_TAC [])

  let MATCH_ELSEPATTERN ← prove
   r"_MATCH (e:B) (_ELSEPATTERN (a:A)) = a"
   (REWRITE_TAC [_MATCH, _ELSEPATTERN] THEN METIS_TAC [])

  let BITMATCH_ELSEPATTERN ← prove
   r"_BITMATCH (e:N word) (_ELSEPATTERN (a:A)) = a"
   (REWRITE_TAC [_BITMATCH, MATCH_ELSEPATTERN])

  let pat_extract ← new_definition r"pat_extract p i b <=>
  (!n. pat_set p n ==> numbit i n = b)"

  let PAT_EXTRACT_THM : term × term → ExceptT String IO thm ← do
    -- `let N,n,m,i,p,b = ... and a,lt,pl,nb,di = ...`: the tuples are built
    -- right to left.
    let b ← q "b:bool"
    let p ← q "p:bitpat"
    let i ← q "i:num"
    let m ← q "m:num"
    let n ← q "n:num"
    let N ← qty "N"
    let di ← q "dimindex(:N)"
    let nb ← q "numbit"
    let pl ← q "(+)"
    let lt ← q "(<)"
    let _a ← q "a:N word"  -- bound but unused in bitmatch.ml too
    let word1_eq ← prove
     r"pat_extract (CONSPAT p (word1 b)) 0 b"
     (REWRITE_TAC [pat_extract, numbit, CONSPAT_pat_set, word1, VAL_WORD] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
      DIMINDEX_TAC THEN NUM_REDUCE_TAC THEN
      REWRITE_TAC [DIV_1, EVEN_ADD, ← GSYM NOT_EVEN, EVEN_DOUBLE] THEN
      BOOL_CASES_TAC (← q "b:bool") THEN REWRITE_TAC [bitval] THEN ARITH_TAC)
    let word_lt ← UNDISCH_ALL (← prove
     r"dimindex(:N) = n ==> numbit i m = b ==> (i < n <=> T) ==>
     pat_extract (CONSPAT p (word m:N word)) i b"
     (← do
      let ar ← ARITH_RULE (← q r"m <= n ==> (m + (n - m) = n:num)")
      pure (REWRITE_TAC [] THEN REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN
        REWRITE_TAC [pat_extract, CONSPAT_pat_set, numbit] THEN
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
        REWRITE_TAC [VAL_WORD, ODD_MOD, DIV_MOD] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        ONCE_REWRITE_TAC [MULT_SYM] THEN
        REWRITE_TAC [← GSYM (← CONJUNCT2 EXP)] THEN
        ONCE_REWRITE_TAC [← GSYM MOD_ADD_MOD] THEN
        FIRST_X_ASSUM (SUBST1_TAC o GSYM o
          MATCH_MP ar o
          REWRITE_RULE [← GSYM LE_SUC_LT]) THEN
        REWRITE_TAC [EXP_ADD, MOD_MOD] THEN ONCE_REWRITE_TAC [MULT_AC] THEN
        REWRITE_TAC [MOD_MULT, ADD_0, MOD_MOD_REFL])))
    let word_skip ← UNDISCH_ALL (← prove
     r"dimindex(:N) = n ==> m + n = i ==> pat_extract p m b ==>
     pat_extract (CONSPAT p (a:N word)) i b"
     (REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN
      REWRITE_TAC [pat_extract, CONSPAT_pat_set, numbit] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
      POP_ASSUM (fun th => POP_ASSUM (fun f => tactic_of do
        pure (REWRITE_TAC [← GSYM (← MATCH_MP f th)]))) THEN
      REWRITE_TAC [← SPECL [m, ← q "dimindex(:N)"] ADD_SYM] THEN
      REWRITE_TAC [EXP_ADD, ← GSYM DIV_DIV] THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      IMP_REWRITE_TAC [DIV_MULT_ADD, DIV_LT, ADD, VAL_BOUND, EXP_2_NE_0]))
    pure (patExtractGo ⟨word1_eq, word_lt, word_skip, N, n, m, i, p, b, di, nb, pl, lt,
      DIMINDEX_CONV, NUMBIT_CONV, NUM_LT_CONV, NUM_ADD_CONV, mk_numeral⟩)

  -- (pat_to_bit false `i` `pat_set p (val e)`) proves
  --  `bit i e |- ~pat_set p (val e)` or `~bit i e |- ~pat_set p (val e)`;
  -- (pat_to_bit true `i` `pat_set p (val e)`) proves
  --  `pat_set p (val e) |- ~bit i e` or `pat_set p (val e) |- bit i e`
  let pat_to_bit : Bool → term → term → ExceptT String IO thm ← do
    -- thT := ~bit i e, pat_extract p i T |- ~pat_set p (val e)
    -- thF := bit i e, pat_extract p i F |- ~pat_set p (val e)
    let (thT_pos, thF_pos) ← do
      let a ← PURE_REWRITE_RULE [pat_extract] (← ASSUME (← q "pat_extract p i b"))
      let a ← UNDISCH (← SPEC (← q "val (e:N word)") a)
      let th ← TRANS (← SYM NUMBIT_VAL) a
      -- the pair is built right to left
      let f ← EQF_ELIM (← INST [(← q "F", ← q "b:bool")] th)
      let t ← EQT_ELIM (← INST [(← q "T", ← q "b:bool")] th)
      pure (t, f)
    let (thT_neg, thF_neg) ← do
      let f (x y : thm) : ExceptT String IO thm := do
        NOT_INTRO (← DISCH (← q "pat_set p (val (e:N word))") (← MP (← NOT_ELIM x) y))
      let fn ← f thF_pos (← ASSUME (← q "bit i (e:N word)"))
      let tn ← f (← ASSUME (← q "~bit i (e:N word)")) thT_pos
      pure (tn, fn)
    let p ← q "p:bitpat"
    let e ← q "e:N word"
    let i ← q "i:num"
    let N ← qty "N"
    pure (fun pos i' tm => do
      match tm with
      | .Comb (.Comb (.Const "pat_set" _) p')
          (.Comb (.Const "val" (.Tyapp _ [.Tyapp _ [N'], _])) e') =>
        let thp ← PAT_EXTRACT_THM (p', i')
        let th ← match ← liftExcept (rand (concl thp)) with
          | .Const "T" _ => pure (if pos then thT_pos else thT_neg)
          | .Const "F" _ => pure (if pos then thF_pos else thF_neg)
          | _ => throw "pat_to_bit"
        PROVE_HYP thp (← PINST [(N', N)] [(i', i), (e', e), (p', p)] th)
      | _ => throw "pat_to_bit")

  let bm_analyze_pat : Nat → term → ExceptT String IO (Array (Option Bool)) ← pure (fun sz pat => do
    match bmAnalyzeGo sz 0 pat (Array.replicate sz none) with
    | .ok A => pure A
    | .error e =>
      if isInvalidArg e then
        throw s!"bm_analyze_pat: pattern {← HolCore.Printer.string_of_term pat} has incorrect bit length"
      else throw e)

  let bm_analyze_clauses : Nat → term → ExceptT String IO (List (Array (Option Bool))) ← do
    let rec goClauses (sz : Nat) (tm : term) : ExceptT String IO (List (Array (Option Bool))) := do
      match tm with
      | .Comb (.Comb (.Const "_SEQPATTERN" _) c) cs =>
        let pat ← liftExcept (do lhand (← lhand (strip_exists (← body (← body c))).2))
        -- `x :: xs`: OCaml evaluates the tail first.
        let rest ← goClauses sz cs
        pure ((← bm_analyze_pat sz pat) :: rest)
      | _ => pure []
    pure goClauses

  -- (bm_skip_clause f `_BITMATCH e (_SEQPATTERN r rs)`) returns
  -- `A |- _BITMATCH e (_SEQPATTERN r rs) = _BITMATCH e rs` if
  -- (f `pat_set p (val e)`) proves `A |- ~pat_set p (val e)`
  -- (probably via pat_to_bit false)
  let bm_skip_clause : (term → ExceptT String IO thm) → term → ExceptT String IO thm ← do
    let th ← UNDISCH (← prove
      r"(?) (r (val e)) = F ==>
      (_BITMATCH e (_SEQPATTERN r rs):B) = _BITMATCH (e:N word) rs"
      (REPEAT DISCH_TAC THEN REWRITE_TAC [BITMATCH_SEQPATTERN] THEN
       CONV_TAC (ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC []))
    let rs ← q r"rs:num->B->bool"
    let r ← q r"r:num->B->bool"
    let e ← q "e:N word"
    let B ← qty "B"
    let N ← qty "N"
    -- (strip_ex `x` `A |- P[x] = F`) proves `A |- (?x. P[x]) = F`
    let strip_ex : term → thm → ExceptT String IO thm ← do
      let th1 ← UNDISCH (← prove
        r"(P = \x:A. F) ==> (?) P = F" (DISCH_TAC THEN ASM_REWRITE_TAC []))
      let A ← qty "A"
      let P ← q r"P:A->bool"
      pure (fun x th => do
        let th' ← liftExcept (HolCore.Kernel.ABS x th)
        PROVE_HYP th' (← PINST [(type_of x, A)] [(← liftExcept (lhs (concl th')), P)] th1))
    -- (skip_guard `A` `B`) proves `~A |- _UNGUARDED_PATTERN A B = F`
    let skip_guard : term → term → ExceptT String IO thm ← do
      let th ← UNDISCH (← prove
        r"~A ==> _UNGUARDED_PATTERN A B = F"
        (DISCH_TAC THEN ASM_REWRITE_TAC [_UNGUARDED_PATTERN]))
      let A ← q "A:bool"
      let B ← q "B:bool"
      pure (fun A' B' => INST [(A', A), (B', B)] th)
    pure (fun f tm => do
      match tm with
      | .Comb (.Comb (.Const "_BITMATCH" ty) e')
          (.Comb (.Comb (.Const "_SEQPATTERN" _) c) rs') =>
        let (N', B') ← match ← liftExcept (dest_fun_ty ty) with
          | (.Tyapp _ [N'], .Tyapp _ [_, B']) => pure (N', B')
          | _ => throw "Match_failure"
        let th ← PINST [(N', N), (B', B)] [(e', e), (c, r), (rs', rs)] th
        let (ex, h) ← liftExcept (do dest_comb (← lhs (← hd (hyp th))))
        let th2 ← BETA_CONV h
        let th3 ← AP_TERM ex th2
        let rec skip_exs (t : term) : ExceptT String IO thm := do
          match t with
          | .Comb (.Const "?" _) (.Abs y c) => strip_ex y (← skip_exs c)
          | .Comb (.Comb (.Const "_UNGUARDED_PATTERN" _) p) res =>
            -- right to left: the guard theorem first
            let g ← skip_guard p res
            PROVE_HYP (← f p) g
          | _ => throw "skip_exs"
        PROVE_HYP (← TRANS th3 (← skip_exs (← liftExcept (rhs (concl th3))))) th
      | _ => throw "bm_skip_clause")

  -- @@RETURN BEGIN
  return { dest_word_ty, SPLIT_IF, MATCH_SEQPATTERN, BITMATCH_SEQPATTERN,
           BITMATCH_SEQPATTERN2, MATCH_ELSEPATTERN, BITMATCH_ELSEPATTERN, pat_extract,
           PAT_EXTRACT_THM, pat_to_bit, bm_analyze_pat, bm_analyze_clauses,
           bm_skip_clause }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Discrimination trees: building one from the clauses, BM_IF_CONV; the      -/
/- bitpat_inverts lemmas and build_inverts.  (bitmatch.ml 527-693)           -/
/- ------------------------------------------------------------------------- -/

/-- `'a discrim_tree`. -/
inductive discrim_tree (α : Type) where
  | Leaf_dt : α → discrim_tree α
  | Split_dt : Nat → term → discrim_tree α → discrim_tree α → discrim_tree α
  deriving Inhabited

def map_dt {α β : Type} (f : α → β) : discrim_tree α → discrim_tree β
  | .Leaf_dt a => .Leaf_dt (f a)
  | .Split_dt i bit tr1 tr2 => .Split_dt i bit (map_dt f tr1) (map_dt f tr2)

/-- `aMerge` (bitmatch.ml 563-567). -/
def aMerge (a : Option (Nat × Nat)) (b : Option Bool) : Option (Nat × Nat) :=
  match a, b with
  | none, _ => a
  | _, none => none
  | some (a0, a1), some false => some (a0 + 1, a1)
  | some (a0, a1), some true => some (a0, a1 + 1)

/-- The bit of the clause analyses `build` splits on: the first position
    where both values occur with the least imbalance (bitmatch.ml 572-582). -/
def bmSplitBit (sz : Nat) (cls : List (Array (Option Bool))) : Option (Nat × Nat) := Id.run do
  let mut analysis : Array (Option (Nat × Nat)) := Array.replicate sz (some (0, 0))
  for cl in cls do
    for i in [0:cl.size] do
      analysis := analysis.set! i (aMerge analysis[i]! cl[i]!)
  let mut r : Option (Nat × Nat) := none
  for i in [0:analysis.size] do
    match analysis[i]! with
    | some (n1, n2) =>
      if n1 != 0 && n2 != 0 then
        let v := if n1 ≥ n2 then n1 - n2 else n2 - n1
        match r with
        | some (v', _) => if v' ≤ v then pure () else r := some (v, i)
        | none => r := some (v, i)
    | none => pure ()
  return r

/-- `cl.(i)` with `let Some(b) = ... in b`: Match_failure on `None`. -/
def clBit (cl : Array (Option Bool)) (i : Nat) : Except String Bool :=
  match cl[i]? with
  | some (some b) => .ok b
  | some none => .error "Match_failure"
  | none => .error (invalidArgPrefix ++ "index out of bounds")

/-- The functions `bm_build_tree'`'s `build` closes over. -/
structure BuildCtx where
  sz : Nat
  m : term
  e : term
  bit_tm : term → term → ExceptT String IO term
  seqp_rand : term → thm → ExceptT String IO thm
  bm_skip_clause : (term → ExceptT String IO thm) → term → ExceptT String IO thm
  pat_to_bit : Bool → term → term → ExceptT String IO thm
  mk_numeral : Rat → Except String term

/-- `split_ths` (bitmatch.ml 590-603). -/
partial def bmSplitThs [HolBase] (C : BuildCtx) (i : Nat)
    (skip_th : term → thm → ExceptT String IO thm) :
    List (Array (Option Bool)) × term →
      ExceptT String IO (List (Array (Option Bool)) × List (Array (Option Bool)) × thm × thm)
  | ([], cs) => do
    let th := REFL (← liftExcept (mk_comb C.m cs))
    pure ([], [], th, th)
  | (cl :: cls, .Comb (.Comb (.Const "_SEQPATTERN" ty) c) cs) => do
    let sc := term.Comb (.Const "_SEQPATTERN" ty) c
    let (cls1, cls2, th1, th2) ← bmSplitThs C i skip_th (cls, cs)
    if ← liftExcept (clBit cl i) then do
      -- the tuple is built right to left
      let t2 ← C.seqp_rand c th2
      let t1 ← skip_th sc th1
      pure (cls1, cl :: cls2, t1, t2)
    else do
      let t2 ← skip_th sc th2
      let t1 ← C.seqp_rand c th1
      pure (cl :: cls1, cls2, t1, t2)
  | (cl :: cls, cs) => do
    let (cls1, cls2, th1, th2) ← bmSplitThs C i skip_th (cls, cs)
    if ← liftExcept (clBit cl i) then pure (cls1, cl :: cls2, th1, th2)
    else pure (cl :: cls1, cls2, th1, th2)

/-- `bm_build_tree'`'s `build` (bitmatch.ml 569-607). -/
partial def bmBuild [HolBase] (C : BuildCtx) (eqth : thm) (cls : List (Array (Option Bool)))
    (cs : term) : ExceptT String IO (discrim_tree thm) := do
  match bmSplitBit C.sz cls with
  | none => pure (.Leaf_dt eqth)
  | some (_, i) =>
    let ii ← liftExcept (C.mk_numeral (i : Rat))
    let bit ← C.bit_tm ii C.e
    let skip_th (sc : term) (th : thm) : ExceptT String IO thm := do
      let (sm, rs') ← liftExcept (dest_comb (← lhs (concl th)))
      let tm ← liftExcept (mk_comb sm (← mk_comb sc rs'))
      TRANS (← C.bm_skip_clause (C.pat_to_bit false ii) tm) th
    let (cls1, cls2, th1, th2) ← bmSplitThs C i skip_th (cls, cs)
    -- `let tr1 = ... and tr2 = ...`, left to right
    let tr1 ← bmBuild C (← TRANS eqth th1) cls1 (← liftExcept (do rand (← rhs (concl th1))))
    let tr2 ← bmBuild C (← TRANS eqth th2) cls2 (← liftExcept (do rand (← rhs (concl th2))))
    pure (.Split_dt i bit tr1 tr2)

/-- `build_inverts`'s `go` (bitmatch.ml 670-689); `K` holds `N,A,p,a,f,x,b`,
    `th0`-free (the thunk carries it), `th1` and the two inverts lemmas. -/
structure InvertsCtx where
  (N A : hol_type)
  (p a f x b : term)
  (th1 CONSPAT_word_inverts CONSPAT_word1_inverts : thm)

partial def buildInvertsGo [HolBase] (K : InvertsCtx) :
    term × (Unit → ExceptT String IO thm) → ExceptT String IO (List (term × thm))
  | (.Const "NILPAT" _, _) => pure []
  | (cp@(.Comb (.Comb (.Const "CONSPAT" _) p') a'), thunk) => do
    let N' ← match type_of a' with
      | .Tyapp _ [N'] => pure N'
      | _ => throw "Match_failure"
    let next (th : thm) : ExceptT String IO thm := do
      let th' ← PINST [(N', K.N)] [(a', K.a)] K.th1
      match ← liftExcept (rator (concl th')) with
      | .Comb (.Comb _ p'') f' =>
        PROVE_HYP th' (← INST [(p'', K.p), (f', K.f)] th)
      | _ => throw "Match_failure"
    let var (v : term) (thv : thm) : ExceptT String IO (List (term × thm)) := do
      let th ← thunk ()
      let f' ← liftExcept (do rand (← rator (concl thv)))
      let th' ← PROVE_HYP thv (← PINST [(type_of v, K.A)] [(cp, K.p), (f', K.f), (v, K.x)] th)
      -- `(v,th') :: go ...`: the tail first, after th'
      let rest ← buildInvertsGo K (p', fun () => do next th)
      pure ((v, th') :: rest)
    match a' with
    | .Var _ _ => var a' (← PINST [(N', K.N)] [(p', K.p), (a', K.a)] K.CONSPAT_word_inverts)
    | .Comb (.Const "word1" _) b'@(.Var _ _) =>
      var b' (← INST [(p', K.p), (b', K.b)] K.CONSPAT_word1_inverts)
    | _ => buildInvertsGo K (p', fun () => do next (← thunk ()))
  | _ => throw "build_inverts"

structure Tree where
  -- @@FIELDS
  bm_build_tree' : Nat → List (Array (Option Bool)) → term → ExceptT String IO (discrim_tree thm)
  bm_build_tree : term → ExceptT String IO (List (Array (Option Bool)) × discrim_tree thm)
  BM_IF_CONV : term → ExceptT String IO thm
  MATCH_EQ : thm
  bitpat_inverts : thm
  bitpat_down : thm
  CONSPAT_down_inverts : thm
  CONSPAT_word_inverts : thm
  bitpat_inverts_comp : thm
  CONSPAT_word1_inverts : thm
  build_inverts : term → ExceptT String IO (List (term × thm))
  deriving Inhabited

@[nospecialize]
def setupTree [HolBase] (D : BitMatchDeps) (BDefs : Defs) (BAnalyze : Analyze) :
    ExceptT String IO Tree := do
  -- @@SCOPE BEGIN
  let { IMP_REWRITE_TAC, MESON, METIS_TAC, mk_numeral, new_definition, .. } := D
  let { ADD, DIV_LT, DIV_MULT_ADD, EXP_2_NE_0, MOD_MULT_ADD, _MATCH, o_DEF, .. } := D.core1
  let { VAL_BOUND, WORD_VAL, WORD_VAL_GALOIS, .. } := D.core2
  let { BIT0_WORD1, CONSPAT_pat_set, .. } := BDefs
  let { BITMATCH_SEQPATTERN, SPLIT_IF, bm_analyze_clauses, bm_skip_clause,
        dest_word_ty, pat_to_bit, .. } := BAnalyze
  -- @@SCOPE END

  let bm_build_tree' : Nat → List (Array (Option Bool)) → term → ExceptT String IO (discrim_tree thm) ← do
    let bit_tm : term → term → ExceptT String IO term ← do
      let N ← qty "N"
      pure (fun i e => do
        let N' ← match type_of e with
          | .Tyapp "word" [N'] => pure N'
          | _ => throw "Match_failure"
        let bit ← ExceptT.mk (mk_const "bit" [(N', N)])
        liftExcept (mk_comb (← mk_comb bit i) e))
    -- (seqp_rand `r` `A |- _BITMATCH e rs1 = _BITMATCH e rs2`) proves
    -- `A |- _BITMATCH e (_SEQPATTERN r rs1) = _BITMATCH e (_SEQPATTERN r rs2)`
    let seqp_rand : term → thm → ExceptT String IO thm ← do
      let th ← UNDISCH (← prove
        r"_BITMATCH (e:N word) (rs1:num->B->bool) = _BITMATCH e rs2 ==>
        _BITMATCH e (_SEQPATTERN r rs1) = _BITMATCH e (_SEQPATTERN r rs2)"
        (DISCH_TAC THEN ASM_REWRITE_TAC [BITMATCH_SEQPATTERN]))
      let (rs1, e, r, rs2) ← match frees (concl th) with
        | [rs1, e, r, rs2] => pure (rs1, e, r, rs2)
        | _ => throw "Match_failure"
      -- `N,B = ...`: right to left
      let B ← qty "B"
      let N ← qty "N"
      pure (fun r' th' => do
        match ← liftExcept (dest_eq (concl th')) with
        | (.Comb (.Comb (.Const _ ty) e') rs1', .Comb _ rs2') =>
          let (N', B') ← match ← liftExcept (dest_fun_ty ty) with
            | (.Tyapp _ [N'], .Tyapp _ [_, B']) => pure (N', B')
            | _ => throw "Match_failure"
          PROVE_HYP th' (← PINST [(N', N), (B', B)] [(e', e), (r', r), (rs1', rs1), (rs2', rs2)] th)
        | _ => throw "seqp_rand")
    pure (fun sz cls tm => do
      match tm with
      | .Comb m@(.Comb (.Const "_BITMATCH" _) e) cs =>
        bmBuild ⟨sz, m, e, bit_tm, seqp_rand, bm_skip_clause, pat_to_bit, mk_numeral⟩
          (REFL tm) cls cs
      | _ => throw "bm_build_tree'")

  let bm_build_tree : term → ExceptT String IO (List (Array (Option Bool)) × discrim_tree thm) ←
    pure (fun tm => do
      match tm with
      | .Comb (.Comb (.Const "_BITMATCH" _) e) cs =>
        let sz := ratNat (← liftExcept (dest_finty (← dest_word_ty (type_of e))))
        let cls ← bm_analyze_clauses sz cs
        pure (cls, ← bm_build_tree' sz cls tm)
      | _ => throw "bm_build_tree")

  let BM_IF_CONV : term → ExceptT String IO thm ← do
    let rec of_tree : discrim_tree thm → ExceptT String IO thm
      | .Leaf_dt th => pure th
      | .Split_dt _ bit tr1 tr2 => do
        -- arguments right to left
        let t1 ← of_tree tr1
        let t2 ← of_tree tr2
        SPLIT_IF bit t2 t1
    pure (fun tm => do of_tree (← bm_build_tree tm).2)

  let MATCH_EQ ← prove
   r"(r:A->B->bool) e = (\y. x = y) ==> _MATCH e r = x"
   (REWRITE_TAC [_MATCH] THEN DISCH_THEN SUBST1_TAC THEN METIS_TAC [])

  let bitpat_inverts ← new_definition
   r"bitpat_inverts p f (x:A) <=> (!y. pat_set p y ==> f y = x)"

  let bitpat_down ← new_definition
   r"bitpat_down(:N) (f:num->A) (n:num) = f (n DIV 2 EXP dimindex(:N))"

  let CONSPAT_down_inverts ← prove
   r"bitpat_inverts p f (x:A) ==>
   bitpat_inverts (CONSPAT p (a:N word)) (bitpat_down(:N) f) x"
   (REWRITE_TAC [bitpat_inverts, bitpat_down, CONSPAT_pat_set] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    IMP_REWRITE_TAC [DIV_MULT_ADD, DIV_LT, VAL_BOUND, EXP_2_NE_0] THEN
    ASM_REWRITE_TAC [ADD])

  let CONSPAT_word_inverts ← prove
   r"bitpat_inverts (CONSPAT p (a:N word)) word a"
   (REWRITE_TAC [bitpat_inverts, CONSPAT_pat_set] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
    REWRITE_TAC [WORD_VAL_GALOIS, MOD_MULT_ADD] THEN
    REWRITE_TAC [← GSYM WORD_VAL_GALOIS, WORD_VAL])

  let bitpat_inverts_comp ← MESON [bitpat_inverts, o_DEF]
   (← q r"bitpat_inverts p f (x:A) ==> bitpat_inverts p (g o f) (g x:B)")

  let CONSPAT_word1_inverts ←
    -- `bitpat_inverts (CONSPAT p (word1 b)) (bit 0 o word) b`
    REWRITE_RULE [BIT0_WORD1]
      (← PART_MATCH rand (← MATCH_MP bitpat_inverts_comp CONSPAT_word_inverts)
        (← liftExcept (lhs (concl BIT0_WORD1))))

  -- Given a pattern `p` and a target variable `z`,
  -- (build_inverts `p`) produces an association list mapping `z`
  -- to `|- bitpat_inverts p f z` for some term `f` not containing `z`.
  let build_inverts : term → ExceptT String IO (List (term × thm)) ← do
    -- `let N,A,p,a,f,x,b = ... and th0 = ... and th1 = ...`: the bindings
    -- left to right, each tuple right to left.
    let b ← q "b:bool"
    let x ← q "x:A"
    let f ← q r"f:num->A"
    let a ← q "a:N word"
    let p ← q "p:bitpat"
    let A ← qty "A"
    let N ← qty "N"
    let th0 ← ASSUME (← q "bitpat_inverts p f (x:A)")
    let th1 ← UNDISCH CONSPAT_down_inverts
    let K : InvertsCtx := ⟨N, A, p, a, f, x, b, th1, CONSPAT_word_inverts, CONSPAT_word1_inverts⟩
    pure (fun p' => buildInvertsGo K (p', fun () => pure th0))

  -- @@RETURN BEGIN
  return { bm_build_tree', bm_build_tree, BM_IF_CONV, MATCH_EQ, bitpat_inverts,
           bitpat_down, CONSPAT_down_inverts, CONSPAT_word_inverts, bitpat_inverts_comp,
           CONSPAT_word1_inverts, build_inverts }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- BM_FIRST_CASE_CONV, the positive tree, get_dt, BM_CASES, bitpat_matches.  -/
/- (bitmatch.ml 691-805)                                                     -/
/- ------------------------------------------------------------------------- -/

/-- `itlist` with an IO-valued function. -/
def itlistIO {α β : Type} (f : α → β → ExceptT String IO β) : List α → β → ExceptT String IO β
  | [], b => pure b
  | h :: t, b => do f h (← itlistIO f t b)

/-- `get_dt` (bitmatch.ml 776-783). -/
partial def get_dt {α : Type} [Inhabited α] (A : Array (Option Bool)) :
    discrim_tree α → Except String (List (Bool × term) × α)
  | .Leaf_dt a => .ok ([], a)
  | .Split_dt i bit tr1 tr2 =>
    match A[i]? with
    | none => .error (invalidArgPrefix ++ "index out of bounds")
    | some none => failwith ("get_dt splitting on " ++ toString i)
    | some (some b) => do
      let (stk, r) ← get_dt A (if b then tr2 else tr1)
      return ((b, bit) :: stk, r)

/-- `bitpat_matches p i` (bitmatch.ml 791-822): `none` if the pattern `p`
    would match `word i`, and `some j` where `j` is the smallest differing
    bit otherwise.  It fails if `i >= 2^pat_size p`. -/
partial def bitpat_matches (p : term) (i : Nat) : Except String (Option Nat) :=
  match p with
  | .Comb (.Comb (.Const "CONSPAT" _) p) a => do
    let N ← match type_of a with
      | .Tyapp "word" [N] => .ok N
      | _ => failwith "dest_word_ty"
    let n := ratNat (← dest_finty N)
    let m := 2 ^ n
    -- `let i' = ... and a' = ...`
    let i' := i / m
    let a' := i % m
    let r ← match a with
      | .Comb (.Const "word1" _) (.Const "T" _) => .ok (if a' == 1 then none else some 0)
      | .Comb (.Const "word1" _) (.Const "F" _) => .ok (if a' == 0 then none else some 0)
      | .Comb (.Const "word1" _) (.Var _ _) => .ok none
      | .Comb (.Const "word" _) n =>
        do
        let n' := ratNat (← dest_numeral n)
        if a' == n' then return none
        let rec f (i r : Nat) (fuel : Nat) : Nat :=
          match fuel with
          | 0 => r
          | fuel + 1 => if i &&& 1 != 0 then r else f (i >>> 1) (r + 1) fuel
        return some (f (a' ^^^ n') 0 (a' ^^^ n'))
      | .Var _ _ => .ok none
      | _ => failwith "bitpat_matches"
    match r with
    | some j => return some j
    | none =>
      match ← bitpat_matches p i' with
      | some j => return some (j + n)
      | none => return none
  | .Const "NILPAT" _ => if i == 0 then .ok none else failwith "bitpat_matches: out of range"
  | .Abs _ c => bitpat_matches c i
  | .Comb (.Const "?" _) c => bitpat_matches c i
  | .Comb (.Comb (.Const "_UNGUARDED_PATTERN" _) c) _ => bitpat_matches c i
  | .Comb (.Comb (.Const "pat_set" _) c) _ => bitpat_matches c i
  | _ => failwith "bitpat_matches"

/-- What `BM_FIRST_CASE_CONV`'s `prove_ex` closes over. -/
structure ProveExCtx where
  inverts : List (term × thm)
  p : term
  x : term
  (th4 thg1 thg2 : thm)
  instAB : thm → ExceptT String IO thm
  (ep ef ex : term)
  TRIV_CHOOSE : thm → thm → ExceptT String IO thm

/-- `prove_ex` (bitmatch.ml 724-735). -/
partial def bmProveEx [HolBase] (C : ProveExCtx) (c1 : term) (pr : thm → ExceptT String IO thm)
    (eqth : thm) : ExceptT String IO ((thm → ExceptT String IO thm) × thm) := do
  match c1 with
  | .Comb (.Const "?" _) (.Abs z c') =>
    let inv ← liftExcept (assoc z C.inverts)
    let f ← liftExcept (lhand (concl inv))
    let inv ← PROVE_HYP inv (← PINST [(type_of z, aty)]
      [(C.p, C.ep), (f, C.ef), (z, C.ex), (C.x, ← q "e:num")] C.th4)
    let abr ← liftExcept (mk_abs z (← lhs (concl eqth)))
    let eqth1 ← TRANS (← AP_TERM abr (← ASSUME (concl inv)))
      (← liftExcept (HolCore.Kernel.BETA (← mk_comb abr z)))
    let (pr', th) ← bmProveEx C c' (fun t => do PROVE_HYP inv (← pr t)) (← TRANS eqth1 eqth)
    pure (pr', ← TRANS (← SYM eqth1) (← C.TRIV_CHOOSE (← ASSUME c1) th))
  | _ =>
    -- the pair is built right to left
    let g2 ← C.instAB C.thg2
    pure (pr, ← TRANS (← PROVE_HYP (← C.instAB C.thg1) (← pr eqth)) g2)

structure Cases where
  -- @@FIELDS
  BM_FIRST_CASE_CONV : term → ExceptT String IO thm
  bm_add_pos : discrim_tree thm → term → ExceptT String IO (discrim_tree (thm × List thm))
  bm_build_pos_tree : term → ExceptT String IO (List (Array (Option Bool)) × discrim_tree (thm × List thm))
  BM_CASES : term → ExceptT String IO (List thm)
  deriving Inhabited

@[nospecialize]
def setupCases [HolBase] (D : BitMatchDeps) (BDefs : Defs) (BAnalyze : Analyze) (BTree : Tree) :
    ExceptT String IO Cases := do
  -- @@SCOPE BEGIN
  let { MESON, METIS, .. } := D
  let { _UNGUARDED_PATTERN, .. } := D.core1
  let { TRIV_CHOOSE, _BITMATCH, .. } := BDefs
  let { BITMATCH_ELSEPATTERN, BITMATCH_SEQPATTERN, dest_word_ty, pat_to_bit, .. } := BAnalyze
  let { MATCH_EQ, bitpat_inverts, bm_build_tree, build_inverts, .. } := BTree
  -- @@SCOPE END

  -- Given `bitmatch e with p -> res | ...` proves
  --  `bit_set p (val e) |- (bitmatch e with p -> res | ...) = res`,
  -- and given `bitmatch e with _ -> res` proves
  -- `(bitmatch e with _ -> res) = res`.
  let BM_FIRST_CASE_CONV : term → ExceptT String IO thm ← do
    let th1 ← UNDISCH (← prove
     r"r (val (e:N word)) = (\y:A. x = y) ==> _BITMATCH e (_SEQPATTERN r s) = x"
     (DISCH_TAC THEN
      ASM_REWRITE_TAC [BITMATCH_SEQPATTERN, _BITMATCH, ← MESON [] (← q "?y:A. x=y")] THEN
      POP_ASSUM (ACCEPT_TAC o MATCH_MP MATCH_EQ)))
    let th2 ← UNDISCH (← METIS [_UNGUARDED_PATTERN]
      (← q "A ==> (_UNGUARDED_PATTERN A B <=> B)"))
    let th3 ← EQ_MP (← SYM th2) (← ASSUME (← q "B:bool"))
    let th4 ← UNDISCH_ALL (← prove
     r"bitpat_inverts p f (x:A) ==> pat_set p e ==> f e = x"
     (DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [bitpat_inverts])))
    let (thg1, thg2) ← CONJ_PAIR (← UNDISCH (← METIS [_UNGUARDED_PATTERN]
      (← q r"_UNGUARDED_PATTERN A B ==> A /\ B")))
    let ex ← q "x:A"
    let ef ← q r"f:num->A"
    let ep ← q "p:bitpat"
    let eB ← q "B:bool"
    let eA ← q "A:bool"
    let nty ← qty "N"
    let es ← q r"s:num->A->bool"
    let er ← q r"r:num->A->bool"
    let ea ← q "a:A"
    let ee ← q "e:N word"
    pure (fun tm => do
      match tm with
      | .Comb (.Comb (.Const "_BITMATCH" _) e)
          (.Comb (.Comb (.Const "_SEQPATTERN" _) c@(.Abs x (.Abs y c'))) cs) =>
        let A' := type_of tm
        let N ← dest_word_ty (type_of e)
        let val_e ← liftExcept (mk_comb (← ExceptT.mk (mk_const "val" [(N, nty)])) e)
        let (zs, ps, mp, p, restm) ← match strip_exists c' with
          | (zs, .Comb (.Comb (.Const "_UNGUARDED_PATTERN" _)
              ps@(.Comb mp@(.Comb _ p) _)) restm) => pure (zs, ps, mp, p, restm)
          | _ => throw "Match_failure"
        let res ← liftExcept (lhand restm)
        let instAB (th : thm) : ExceptT String IO thm := INST [(ps, eA), (restm, eB)] th
        let _ps' ← liftExcept (mk_comb mp val_e)
        let th' ← if zs.isEmpty then instAB th2 else do
          let inverts ← build_inverts p
          let C : ProveExCtx := ⟨inverts, p, x, th4, thg1, thg2, instAB, ep, ef, ex, TRIV_CHOOSE⟩
          let (pr, thR) ← bmProveEx C c' (fun t => pure t) (REFL res)
          -- arguments right to left
          let r ← pr thR
          let l ← itlistIO SIMPLE_EXISTS zs (← instAB th3)
          pure (HolCore.Kernel.DEDUCT_ANTISYM_RULE l r)
        let th' ← INST [(val_e, x)] (← TRANS (← liftExcept (HolCore.Kernel.BETA (← mk_comb c x)))
          (← liftExcept (HolCore.Kernel.ABS y th')))
        PROVE_HYP th' (← PINST [(N, nty), (A', aty)] [(e, ee), (res, ex), (c, er), (cs, es)] th1)
      | .Comb (.Comb (.Const "_BITMATCH" _) e) (.Comb (.Const "_ELSEPATTERN" _) a) =>
        let A' := type_of a
        let N ← dest_word_ty (type_of e)
        PINST [(N, nty), (A', aty)] [(e, ee), (a, ea)] BITMATCH_ELSEPATTERN
      | _ => throw "BM_FIRST_CASE_CONV")

  let bm_add_pos : discrim_tree thm → term → ExceptT String IO (discrim_tree (thm × List thm)) ←
    pure (fun tr tm => do
      match tm with
      | .Comb (.Comb (.Const "_BITMATCH" _) e) _ =>
        let N ← dest_word_ty (type_of e)
        let val_e ← liftExcept (mk_comb (← ExceptT.mk (mk_const "val" [(N, ← qty "N")])) e)
        let rec build_cases (stk : List term) (mth : thm) (t : term) :
            ExceptT String IO (List thm) := do
          match t with
          | .Comb (.Comb (.Const "_SEQPATTERN" _) (.Abs _ (.Abs _ c'))) cs =>
            let ps' ← liftExcept (do mk_comb (← rator (← lhand (strip_exists c').2)) val_e)
            let th ← itlistIO (fun n acc => do
                match ← ExceptT.lift (pat_to_bit true n ps').run with
                | .ok t => PROVE_HYP t acc
                | .error e => if isInvalidArg e || e == "Match_failure" then throw e else pure acc)
              stk mth
            -- `x :: xs`: the tail first
            let rest ← build_cases stk mth cs
            pure ((← TRANS th (← BM_FIRST_CASE_CONV (← liftExcept (rhs (concl th))))) :: rest)
          | _ => pure []
        let rec build (stk : List term) : discrim_tree thm → ExceptT String IO (discrim_tree (thm × List thm))
          | .Leaf_dt mth => do
            pure (.Leaf_dt (mth, ← build_cases stk mth (← liftExcept (do rand (← rhs (concl mth))))))
          | .Split_dt i bit tr1 tr2 => do
            let stk' := (← liftExcept (lhand bit)) :: stk
            -- arguments right to left
            let t2 ← build stk' tr2
            let t1 ← build stk' tr1
            pure (.Split_dt i bit t1 t2)
        build [] tr
      | _ => throw "bm_build_pos_tree")

  let bm_build_pos_tree : term → ExceptT String IO (List (Array (Option Bool)) × discrim_tree (thm × List thm)) ←
    pure (fun tm => do
      let (A, tr) ← bm_build_tree tm
      pure (A, ← bm_add_pos tr tm))

  let BM_CASES : term → ExceptT String IO (List thm) ← pure (fun tm => do
    let (A, tr) ← bm_build_pos_tree tm
    A.mapM (fun cl => do liftExcept (hd (← liftExcept (get_dt cl tr)).2.2)))

  -- @@RETURN BEGIN
  return { BM_FIRST_CASE_CONV, bm_add_pos, bm_build_pos_tree, BM_CASES }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- inst_bitpat_numeral.  (bitmatch.ml 824-941)                               -/
/- ------------------------------------------------------------------------- -/

/-- What `inst_bitpat_numeral`'s `go` closes over. -/
structure InstNumCtx where
  (en ep ex ei ea T F : term)
  eN : hol_type
  dim : hol_type → ExceptT String IO thm
  (w0 wS w1T w1F w1F0 : thm)
  mk_numeral : Rat → Except String term
  NUM_SHIFT_ADD_CORE : term → term → term → ExceptT String IO thm

/-- `inst_bitpat_numeral`'s `go` (bitmatch.ml 879-914). -/
partial def instBitpatGo [HolBase] (C : InstNumCtx) (i : Nat) :
    term → ExceptT String IO (List (term × term) × thm)
  | .Comb (.Comb (.Const "CONSPAT" _) p) a => do
    let N ← match type_of a with
      | .Tyapp "word" [N] => pure N
      | _ => throw "dest_word_ty"
    let n := ratNat (← liftExcept (dest_finty N))
    let m := 2 ^ n
    let i' := i / m
    let a' := i % m
    let (ls, th') ← instBitpatGo C i' p
    let (p', x) ← liftExcept (dest_comb (concl th'))
    let p' ← liftExcept (rand p')
    match a with
    | .Comb (.Const "word1" _) a =>
      let (ls, b) ← match a with
        | .Const "T" _ => pure (ls, true)
        | .Const "F" _ => pure (ls, false)
        | .Var _ _ => let b := a' == 1; pure (((if b then C.T else C.F), a) :: ls, b)
        | _ => throw "inst_bitpat_numeral"
      pure (ls, ← PROVE_HYP th' (← (
        if b then INST [(x, C.ex), (p', C.ep)] C.w1T
        else if i == 0 then INST [(p', C.ep)] C.w1F0
        else INST [(x, C.ex), (p', C.ep)] C.w1F)))
    | _ =>
      let thd ← C.dim N
      let n' ← liftExcept (do rand (← rhs (concl thd)))
      let (ls, a) ← match a with
        | .Comb (.Const "word" _) (.Comb (.Const "NUMERAL" _) a) => pure (ls, a)
        | .Var _ _ =>
          let n ← liftExcept (C.mk_numeral (a' : Rat))
          let w ← liftExcept (mk_comb (← ExceptT.mk (mk_const "word" [(N, C.eN)])) n)
          pure ((w, a) :: ls, ← liftExcept (rand n))
        | _ => throw "inst_bitpat_numeral"
      let thn ← C.NUM_SHIFT_ADD_CORE a x n'
      let e ← liftExcept (rhs (concl thn))
      pure (ls, ← PROVE_HYP th' (← PROVE_HYP thn (← PROVE_HYP thd
        (← INST [(n', C.en), (a, C.ea), (x, C.ex), (e, C.ei), (p', C.ep)]
          (← INST_TYPE [(N, C.eN)] C.wS)))))
  | .Const "NILPAT" _ => pure ([], C.w0)
  | _ => throw "inst_bitpat_numeral"

structure Numeral where
  -- @@FIELDS
  inst_bitpat_numeral : term → ExceptT String IO (Nat → ExceptT String IO (List (term × term) × thm))
  deriving Inhabited

@[nospecialize]
def setupNumeral [HolBase] (D : BitMatchDeps) (BDefs : Defs) (BAnalyze : Analyze) :
    ExceptT String IO Numeral := do
  -- @@SCOPE BEGIN
  let { DIMINDEX_CONV, IMP_REWRITE_TAC, NUM_ADD_CONV, NUM_SHIFT_ADD_CORE, mk_numeral, .. } := D
  let { ARITH_ZERO, BIT0_0, BIT1_0, MULT_SYM, NUMERAL, ONE, .. } := D.core1
  let { VAL_WORD, VAL_WORD_EQ, bitval, num_shift_add, num_shift_add_0,
        num_shift_add_SUC, .. } := D.core2
  let { CONSPAT_pat_set, CONSPAT_pat_size, NILPAT_pat_set, NILPAT_pat_size, pat_set_lt,
        word1, .. } := BDefs
  let { dest_word_ty, .. } := BAnalyze
  -- @@SCOPE END

  -- (inst_bitpat_numeral `pat_set p (val e)` n) will produce an instantiation
  -- theta for p and e such that e[theta] = word n, and a proof of
  --  `|- (pat_set p (val e))[theta]`.
  --
  -- (inst_bitpat_numeral `pat_set p e` n) will produce an instantiation
  -- theta for p and e such that e[theta] = n, and a proof of
  --  `|- (pat_set p e)[theta]`.
  let inst_bitpat_numeral : term → ExceptT String IO (Nat → ExceptT String IO (List (term × term) × thm)) ← do
    -- `let en,ep,ex,ei,ea = ... and eN,T,F = ...`
    let ea ← q "a:num"
    let ei ← q "i:num"
    let ex ← q "x:num"
    let ep ← q "p:bitpat"
    let en ← q "n:num"
    let F ← q "F"
    let T ← q "T"
    let eN ← qty "N"
    let dim : hol_type → ExceptT String IO thm ← do
      let dN ← q "dimindex(:N)"
      pure (fun N => DIMINDEX_CONV (inst [(N, eN)] dN))
    -- `let w0 = ... and wS,(w1T,w1F) = ...`: w0 first; then pth, then the
    -- pair, right to left.
    let w0 ← prove r"pat_set NILPAT _0"
      (REWRITE_TAC [NILPAT_pat_set, NUMERAL])
    let (wS, w1T, w1F) ← do
      let pth ← prove
       r"pat_set p x ==>
       pat_set (CONSPAT p (word a:N word)) (num_shift_add a x (dimindex(:N)))"
       (REWRITE_TAC [CONSPAT_pat_set, num_shift_add] THEN
        DISCH_THEN (fun th =>
          EXISTS_TAC ex THEN REWRITE_TAC [th, VAL_WORD, MULT_SYM]))
      let (w1T, w1F) ← CONJ_PAIR (← UNDISCH (← prove
       r"pat_set p x ==>
       pat_set (CONSPAT p (word1 T)) (BIT1 x) /\
       pat_set (CONSPAT p (word1 F)) (BIT0 x)"
       (REWRITE_TAC [word1, bitval] THEN
        DISCH_THEN (fun th => CONJ_TAC THEN ASSUME_TAC th) THENL [
          POP_ASSUM (fun th => tactic_of do
            pure (MP_TAC (← MP (← PINST [(← qty "1", eN)] [(← q "1", ea)] pth) th))) THEN
          SUBGOAL_THEN
            (← q "num_shift_add 1 x (dimindex(:1)) = num_shift_add (BIT1 0) x (SUC 0)")
            (fun th => REWRITE_TAC [th, num_shift_add_SUC, num_shift_add_0]) THEN
          CONV_TAC (ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
          REWRITE_TAC [BIT1_0, ONE],
          POP_ASSUM (fun th => tactic_of do
            pure (MP_TAC (← MP (← PINST [(← qty "1", eN)] [(← q "0", ea)] pth) th))) THEN
          SUBGOAL_THEN
            (← q "num_shift_add 0 x (dimindex(:1)) = num_shift_add (BIT0 0) x (SUC 0)")
            (fun th => REWRITE_TAC [th, num_shift_add_SUC, num_shift_add_0]) THEN
          CONV_TAC (ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
          REWRITE_TAC [BIT0_0, ONE]])))
      let wS ← UNDISCH_ALL (← prove
       r"dimindex(:N) = NUMERAL n ==> num_shift_add a x n = i ==> pat_set p x ==>
       pat_set (CONSPAT p (word (NUMERAL a):N word)) i"
       (REWRITE_TAC [NUMERAL] THEN
        REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN ACCEPT_TAC pth))
      pure (wS, w1T, w1F)
    let w1F0 ← REWRITE_RULE [ARITH_ZERO] (← INST [(← q "_0", ex)] w1F)

    let C : InstNumCtx := ⟨en, ep, ex, ei, ea, T, F, eN, dim, w0, wS, w1T, w1F, w1F0,
      mk_numeral, NUM_SHIFT_ADD_CORE⟩

    -- `let pth1 = ... and pth2 = ... and conv = ...`, left to right
    let pth1 ← SYM (← SPEC en NUMERAL)
    let pth2 ← UNDISCH_ALL (← prove
     r"pat_size p = NUMERAL n ==> dimindex(:N) = NUMERAL n ==>
     pat_set p x ==> pat_set p (val (word (NUMERAL x):N word))"
     (DISCH_THEN (SUBST1_TAC o SYM) THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC [NUMERAL] THEN IMP_REWRITE_TAC [VAL_WORD_EQ] THEN
      POP_ASSUM (ACCEPT_TAC o MATCH_MP pat_set_lt)))
    let conv : term → ExceptT String IO thm ← do
      let ps ← q "pat_size"
      -- `REWRITE_CONV ths` builds its net once
      let rc ← REWRITE_CONV_NET [CONSPAT_pat_size, NILPAT_pat_size]
      pure (fun tm => do
        (rc THENC ONCE_DEPTH_CONV DIMINDEX_CONV THENC REDEPTH_CONV NUM_ADD_CONV)
          (← liftExcept (mk_comb ps tm)))

    let check (p : term) (i : Nat) : ExceptT String IO (List (term × term) × thm) := do
      match ← liftExcept (bitpat_matches p i) with
      | none => instBitpatGo C i p
      | _ => throw "inst_bitpat_numeral: number does not match pattern"

    pure (fun tm => do
      match tm with
      | .Comb (.Comb (.Const "pat_set" _) p) (.Comb (.Const "val" _) e) =>
        let N' ← dest_word_ty (type_of e)
        let thd ← dim N'
        let pth2 ← PROVE_HYP thd (← PROVE_HYP (← conv p)
          (← INST [(p, ep), (← liftExcept (do rand (← rhs (concl thd))), en)]
            (← INST_TYPE [(N', eN)] pth2)))
        pure (fun i => do
          let (ls, th) ← check p i
          let e' ← liftExcept (rand (concl th))
          let th1 ← PROVE_HYP th (← INST ((e', ex) :: ls) pth2)
          let r ← liftExcept (do rand (← rand (concl th1)))
          match e with
          | .Var _ _ => pure ((r, e) :: ls, th1)
          | _ => if aconv e r then pure (ls, th1)
                 else throw "inst_bitpat_numeral: pattern failed")
      | .Comb (.Comb (.Const "pat_set" _) p) e =>
        pure (fun i => do
          let (ls, th) ← check p i
          let (f, e') ← liftExcept (dest_comb (concl th))
          let th1 ← INST [(e', en)] pth1
          let th2 ← EQ_MP (← AP_TERM f th1) th
          let r ← liftExcept (rhs (concl th1))
          match e with
          | .Var _ _ => pure ((r, e) :: ls, th2)
          | _ => if aconv e r then pure (ls, th2)
                 else throw "inst_bitpat_numeral: pattern failed")
      | _ => throw "inst_bitpat_numeral")

  -- @@RETURN BEGIN
  return { inst_bitpat_numeral }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- BITMATCH_CONV, BITMATCH_SIMP_CONV, bitpat_irrefutable(_thm).              -/
/- (bitmatch.ml 943-1092)                                                    -/
/- ------------------------------------------------------------------------- -/

/-- `try x with Failure _ -> h ()`: OCaml's `Invalid_argument` and
    `Match_failure` are not caught. -/
def tryFailure {α : Type} (x : ExceptT String IO α) (h : Unit → ExceptT String IO α) :
    ExceptT String IO α :=
  tryCatch x (fun e => if isInvalidArg e || e == "Match_failure" then throw e else h ())

/-- What `BITMATCH_SIMP_CONV`'s `conv` closes over. -/
structure SimpCtx where
  (BITMATCH_ELSEPATTERN NOT_EXISTS_THM : thm)
  BITMATCH_CONV : term → ExceptT String IO thm
  BM_FIRST_CASE_CONV : term → ExceptT String IO thm
  bm_skip_clause : (term → ExceptT String IO thm) → term → ExceptT String IO thm
  bm_analyze_pat : Nat → term → ExceptT String IO (Array (Option Bool))
  pat_to_bit : Bool → term → term → ExceptT String IO thm
  mk_numeral : Rat → Except String term
  N : hol_type

/-- `BITMATCH_SIMP_CONV`'s `conv` (bitmatch.ml 974-1027). -/
partial def bmSimpConv [HolBase] (C : SimpCtx) (pos neg : List thm) (tm : term) :
    ExceptT String IO thm := do
  let conv := bmSimpConv C pos neg
  let tryConv (t : term) : ExceptT String IO thm :=
    tryFailure (conv t) (fun _ => pure (REFL t))
  match tm with
  | .Comb (.Comb (.Const "_BITMATCH" _) _) (.Comb (.Const "_ELSEPATTERN" _) _) =>
    PART_MATCH lhs C.BITMATCH_ELSEPATTERN tm
  | .Comb (.Comb (.Const "_BITMATCH" _) (.Comb (.Const "word" _) n)) _ =>
    if HolMath.Nums.is_numeral n then C.BITMATCH_CONV tm else simpSeq tryConv
  | _ => simpSeq tryConv
where
  simpSeq (tryConv : term → ExceptT String IO thm) : ExceptT String IO thm := do
  match tm with
  | .Comb (.Comb (.Const "_BITMATCH" _) e) (.Comb (.Comb (.Const "_SEQPATTERN" _) c) _) =>
    let pat ← do
      -- `mk_comb (f, x)`: the pair right to left
      let x ← liftExcept (mk_comb (← ExceptT.mk (mk_const "val"
        [((← match type_of e with | .Tyapp "word" [i] => pure i | _ => throw "dest_word_ty"), C.N)])) e)
      let f ← liftExcept (do rator (← lhand (strip_exists (← body (← body c))).2))
      liftExcept (mk_comb f x)
    let vars := frees (← liftExcept (lhand pat))
    let rec check_pos : List thm → ExceptT String IO thm
      | th :: ths => tryFailure (do
          let (_, ls, _) ← ExceptT.mk (HolCore.Drule.term_unify vars pat (concl th))
          PROVE_HYP th (← INST ls (← C.BM_FIRST_CASE_CONV tm)))
          (fun _ => check_pos ths)
      | [] =>
        let rec check_neg : List thm → ExceptT String IO thm
          | th :: ths => tryFailure (do
              let pat' := (strip_exists (← liftExcept (rand (concl th)))).2
              let (_, ls, _) ← ExceptT.mk (HolCore.Drule.term_unify (frees (← liftExcept (lhand pat'))) pat' pat)
              let ath ← INST ls (← SPEC_ALL
                (← PURE_REWRITE_RULE [C.NOT_EXISTS_THM] (← ASSUME (concl th))))
              let th' ← PROVE_HYP th (← C.bm_skip_clause (fun _ => pure ath) tm)
              TRANS th' (← tryConv (← liftExcept (rhs (concl th')))))
              (fun _ => check_neg ths)
          | [] => do
            let sz := ratNat (← liftExcept (dest_finty
              (← match type_of e with | .Tyapp "word" [i] => pure i | _ => throw "dest_word_ty")))
            let a ← C.bm_analyze_pat sz pat
            let rec check_disj : List thm → ExceptT String IO thm
              | th :: ths => tryFailure (do
                  let h := concl th
                  let a' ← C.bm_analyze_pat sz h
                  let mut r : Option Nat := none
                  for i in [0:a.size] do
                    match a[i]!, a'[i]?, r with
                    | some b, some (some c), none => if b != c then r := some i
                    | _, none, _ => throw (invalidArgPrefix ++ "index out of bounds")
                    | _, _, _ => pure ()
                  let i ← match r with
                    | some i => liftExcept (C.mk_numeral (i : Rat))
                    | _ => throw "fail"
                  -- arguments right to left
                  let sk ← C.bm_skip_clause (C.pat_to_bit false i) tm
                  let th' ← PROVE_HYP th (← PROVE_HYP (← C.pat_to_bit true i h) sk)
                  TRANS th' (← tryConv (← liftExcept (rhs (concl th')))))
                  (fun _ => check_disj ths)
              | [] => throw "BITMATCH_SIMP_CONV"
            check_disj pos
        check_neg neg
    check_pos pos
  | _ => throw "BITMATCH_SIMP_CONV"

/-- `bitpat_irrefutable` (bitmatch.ml 1029-1041). -/
partial def bitpat_irrefutable : term → Except String Bool
  | .Comb (.Comb (.Const "CONSPAT" _) p) a =>
    match a with
    | .Comb (.Const "word1" _) (.Var _ _) => bitpat_irrefutable p
    | .Var _ _ => bitpat_irrefutable p
    | _ => .ok false
  | .Const "NILPAT" _ => .ok true
  | .Abs _ c => bitpat_irrefutable c
  | .Comb (.Const "?" _) c => bitpat_irrefutable c
  | .Comb (.Comb (.Const "_UNGUARDED_PATTERN" _) c) _ => bitpat_irrefutable c
  | .Comb (.Comb (.Const "pat_set" _) c) _ => bitpat_irrefutable c
  | _ => failwith "bitpat_irrefutable"

/-- What `bitpat_irrefutable_thm`'s `build` closes over. -/
structure IrrefCtx where
  eN : hol_type
  (ee en em ek ep dN pl one e2n : term)
  (pth pth1 pth0 pthS : thm)
  (DIMINDEX_CONV NUM_ADD_CONV : ioconv)

/-- `bitpat_irrefutable_thm`'s `build` (bitmatch.ml 1074-1099). -/
partial def irrefBuild [HolBase] (C : IrrefCtx) :
    term × term → ExceptT String IO (List (term × term) × thm)
  | (.Const "NILPAT" _, e) => do pure ([], ← INST [(e, C.ee)] C.pth0)
  | (.Comb (.Comb (.Const "CONSPAT" _) p) v, e) => do
    let pthS (n m : term) : ExceptT String IO thm := do
      let th ← ExceptT.mk (C.NUM_ADD_CONV (← liftExcept (mk_comb (← mk_comb C.pl n) m)))
      PROVE_HYP th (← INST [(n, C.en), (m, C.em), (← liftExcept (rhs (concl th)), C.ek), (e, C.ee)] C.pthS)
    match v with
    | .Comb (.Const "word1" _) v@(.Var _ _) =>
      let (ls, th) ← irrefBuild C (p, (← liftExcept (vsubst [(e, C.ee), (C.one, C.en)])) C.e2n)
      let th' ← PROVE_HYP th (← INST [(← liftExcept (lhand (concl th)), C.ep), (e, C.ee)] C.pth1)
      -- the pair right to left
      let snd ← PROVE_HYP (← pthS C.one (← liftExcept (do rand (← rand (← hd (hyp th)))))) th'
      pure ((← liftExcept (do rand (← rand (← lhand (concl th')))), v) :: ls, snd)
    | .Var _ ty =>
      let N ← match ty with | .Tyapp "word" [i] => pure i | _ => throw "dest_word_ty"
      let th1 ← ExceptT.mk (C.DIMINDEX_CONV (inst [(N, C.eN)] C.dN))
      let n ← liftExcept (rhs (concl th1))
      let (ls, th) ← irrefBuild C (p, (← liftExcept (vsubst [(e, C.ee), (n, C.en)])) C.e2n)
      let th' ← PROVE_HYP th1
        (← INST [(n, C.en), (← liftExcept (lhand (concl th)), C.ep), (e, C.ee)]
          (← INST_TYPE [(N, C.eN)] C.pth))
      let th' ← PROVE_HYP th th'
      let snd ← PROVE_HYP (← pthS n (← liftExcept (do rand (← rand (← hd (hyp th)))))) th'
      pure ((← liftExcept (do rand (← lhand (concl th'))), v) :: ls, snd)
    | _ => throw "bitpat_irrefutable_thm: not irrefutable"
  | _ => throw "bitpat_irrefutable_thm"

/-- `bitpat_irrefutable_thm`'s `build_ex` (bitmatch.ml 1104-1109). -/
partial def irrefBuildEx [HolBase] (ls : List (term × term)) (th : thm) (t : term) :
    ExceptT String IO thm := do
  match t with
  | .Comb (.Const "?" _) (.Abs v c) =>
    let e ← liftExcept (rev_assoc v ls)
    -- arguments right to left
    let b ← irrefBuildEx ls th ((← liftExcept (vsubst [(e, v)])) c)
    EXISTS (t, e) b
  | _ => if aconv (concl th) t then pure th
         else throw "bitpat_irrefutable_thm: nonlinear pattern"

structure Conv where
  -- @@FIELDS
  BITMATCH_CONV : term → ExceptT String IO thm
  BITMATCH_SIMP_CONV : List thm → term → ExceptT String IO thm
  bitpat_irrefutable_thm : term → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupConv [HolBase] (D : BitMatchDeps) (BDefs : Defs) (BAnalyze : Analyze) (BCases : Cases) (BNumeral : Numeral) :
    ExceptT String IO Conv := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, DIMINDEX_CONV, IMP_REWRITE_TAC, NUM_ADD_CONV, mk_numeral, .. } := D
  let { ADD_SYM, DIVISION, EXP, EXP_2_NE_0, EXP_ADD, MULT_SYM, NOT_EXISTS_THM,
        RDIV_LT_EQ, .. } := D.core1
  let { VAL_BOUND, VAL_WORD, .. } := D.core2
  let { CONSPAT_pat_set, NILPAT_pat_set, WORD1_ODD, .. } := BDefs
  let { BITMATCH_ELSEPATTERN, bm_analyze_pat, bm_skip_clause, dest_word_ty, pat_to_bit, .. } := BAnalyze
  let { BM_FIRST_CASE_CONV, bm_build_pos_tree, .. } := BCases
  let { inst_bitpat_numeral, .. } := BNumeral
  -- @@SCOPE END

  let BITMATCH_CONV : term → ExceptT String IO thm ← pure (fun tm => do
    match tm with
    | .Comb (.Comb (.Const "_BITMATCH" _)
        (.Comb (.Const "word" (.Tyapp _ [_, .Tyapp _ [N]])) n)) _ =>
      if !HolMath.Nums.is_numeral n then throw "BITMATCH_CONV"
      let (_, tr) ← bm_build_pos_tree tm
      -- `let n = ... and sz = ...`
      let n := ratNat (← liftExcept (dest_numeral n))
      let sz := ratNat (← liftExcept (dest_finty N))
      let a : Array (Option Bool) := Array.ofFn (n := sz) (fun i => some (n.testBit i.val))
      match (← liftExcept (get_dt a tr)).2.2 with
      | th :: _ =>
        let ps ← liftExcept (hd (hyp th))
        let (ls, th') ← (← inst_bitpat_numeral ps) n
        PROVE_HYP th' (← INST ls th)
      | _ => throw "BITMATCH_CONV"
    | _ => throw "BITMATCH_CONV")

  let BITMATCH_SIMP_CONV : List thm → term → ExceptT String IO thm ← do
    let N ← qty "N"
    pure (fun asl =>
      let rec go : List thm → List thm × List thm
        | [] => ([], [])
        | th :: ths =>
          let (pos, neg) := go ths
          match concl th with
          | .Comb (.Const "~" _) c =>
            match (strip_exists c).2 with
            | .Comb (.Comb (.Const "pat_set" _) _) _ => (pos, th :: neg)
            | _ => (pos, neg)
          | .Comb (.Comb (.Const "pat_set" _) _) _ => (th :: pos, neg)
          | _ => (pos, neg)
      let (pos, neg) := go asl
      bmSimpConv ⟨BITMATCH_ELSEPATTERN, NOT_EXISTS_THM, BITMATCH_CONV, BM_FIRST_CASE_CONV,
        bm_skip_clause, bm_analyze_pat, pat_to_bit, mk_numeral, N⟩ pos neg)

  let bitpat_irrefutable_thm : term → ExceptT String IO thm ← do
    -- `let eN,... = ... and ep,dN,pl,_1 = ... and e2n = ... and pth,pth1 = ...
    -- and pth0 = ... and pthS = ... and pthW = ...`, left to right; each
    -- tuple right to left.
    let ek ← q "k:num"
    let em ← q "m:num"
    let en ← q "n:num"
    let ee' ← q "e:N word"
    let ee ← q "e:num"
    let eN ← qty "N"
    let _1 ← q "1"
    let pl ← q "(+)"
    let dN ← q "dimindex(:N)"
    let ep ← q "p:bitpat"
    let e2n ← q "e DIV 2 EXP n"
    let (pth, pth1) ← do
      let pth ← prove
       r"dimindex(:N) = n ==> pat_set p (e DIV 2 EXP n) ==>
       pat_set (CONSPAT p (word e:N word)) e"
       (REWRITE_TAC [CONSPAT_pat_set] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
        DISCH_THEN (fun th => tactic_of do
          pure (EXISTS_TAC (← q "e DIV 2 EXP dimindex(:N)") THEN
            REWRITE_TAC [th, VAL_WORD, ADD_SYM, MULT_SYM,
              ← GSYM (← MATCH_MP DIVISION (← SPEC (← q "n:num") EXP_2_NE_0))])))
      let pth1 ← UNDISCH (← prove
       r"pat_set p (e DIV 2 EXP 1) ==> pat_set (CONSPAT p (word1 (ODD e))) e"
       (REWRITE_TAC [WORD1_ODD] THEN
        ACCEPT_TAC (← MATCH_MP pth (← DIMINDEX_CONV (← q "dimindex(:1)")))))
      pure (← UNDISCH_ALL pth, pth1)
    let pth0 ← UNDISCH (← prove r"e < 2 EXP 0 ==> pat_set NILPAT e"
      (REWRITE_TAC [EXP, ← ARITH_RULE (← q "n < 1 <=> n = 0"), NILPAT_pat_set]))
    let pthS ← UNDISCH_ALL (← prove r"n + m = k ==>
    e < 2 EXP k ==> e DIV 2 EXP n < 2 EXP m"
      (DISCH_THEN (SUBST1_TAC o SYM) THEN
       IMP_REWRITE_TAC [EXP_ADD, RDIV_LT_EQ, EXP_2_NE_0]))
    let pthW ← UNDISCH_ALL (← prove
     r"dimindex(:N) = n ==> val (e:N word) < 2 EXP n"
     (DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [VAL_BOUND]))
    let C : IrrefCtx := ⟨eN, ee, en, em, ek, ep, dN, pl, _1, e2n, pth, pth1, pth0, pthS,
      DIMINDEX_CONV, NUM_ADD_CONV⟩
    pure (fun tm => do
      match (strip_exists tm).2 with
      | .Comb (.Comb (.Const "pat_set" _) p) e@(.Comb (.Const "val" _) e') =>
        let (ls, th) ← irrefBuild C (p, e)
        let th ← irrefBuildEx ls th tm
        let N ← dest_word_ty (type_of e')
        let th1 ← DIMINDEX_CONV (inst [(N, eN)] dN)
        let n ← liftExcept (rhs (concl th1))
        if aconv n (← liftExcept (do rand (← rand (← hd (hyp th))))) then
          PROVE_HYP (← PROVE_HYP th1 (← PINST [(N, eN)] [(n, en), (e', ee')] pthW)) th
        else throw "bitpat_irrefutable_thm: incorrect bit length"
      | _ => throw "bitpat_irrefutable_thm")

  -- @@RETURN BEGIN
  return { BITMATCH_CONV, BITMATCH_SIMP_CONV, bitpat_irrefutable_thm }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- ONLY_BITMATCH_CASES_THEN and the case tactics, bm_seq_numeral,            -/
/- BITMATCH_SEQ_CONV, bm_check_disjointness and its load-time tests.         -/
/- (bitmatch.ml 1124-1247)                                                   -/
/- ------------------------------------------------------------------------- -/

/-- `ONLY_BITMATCH_CASES_THEN`'s `go` (bitmatch.ml 1134-1141). -/
partial def onlyBmGo [HolBase] (e : term) (nty : hol_type) : term → ExceptT String IO (term × tactic)
  | .Comb f@(.Const "?" _) (.Abs z c) => do
    let (tm, tac1) ← onlyBmGo e nty c
    -- the pair right to left
    let t2 := POP_ASSUM CHOOSE_TAC THEN tac1
    pure (← liftExcept (mk_comb f (← mk_abs z tm)), t2)
  | tm => do
    let ety ← match type_of e with | .Tyapp "word" [i] => pure i | _ => throw "dest_word_ty"
    let x ← liftExcept (mk_comb (← ExceptT.mk (mk_const "val" [(ety, nty)])) e)
    pure (← liftExcept (do mk_comb (← rator (← lhand tm)) x), ALL_TAC)

/-- `ONLY_BITMATCH_CASES_THEN`'s `tac` (bitmatch.ml 1132-1151). -/
partial def onlyBmTac [HolBase] (bitpat_irrefutable_thm : term → ExceptT String IO thm)
    (thltac : List thm → tactic) (e : term) (nty : hol_type) (thl : List thm) :
    term → ExceptT String IO tactic
  | .Comb (.Comb (.Const "_SEQPATTERN" _) (.Abs _ (.Abs _ c))) cs => do
    let (tm, tac1) ← onlyBmGo e nty c
    if ← liftExcept (bitpat_irrefutable c) then
      pure (ASSUME_TAC (← bitpat_irrefutable_thm tm) THEN
        tac1 THEN POP_ASSUM (fun th => thltac (th :: thl)))
    else
      pure (ASM_CASES_TAC tm THENL [
        tac1 THEN POP_ASSUM (fun th => thltac (th :: thl)),
        POP_ASSUM (fun th => tactic_of (onlyBmTac bitpat_irrefutable_thm thltac e nty (th :: thl) cs))])
  | _ => pure (thltac thl)

/-- What `bm_seq_numeral`'s `mk_fun` closes over. -/
structure SeqCtx where
  (me e : term)
  sz : Nat
  BM_FIRST_CASE_CONV : term → ExceptT String IO thm
  bm_skip_clause : (term → ExceptT String IO thm) → term → ExceptT String IO thm
  pat_to_bit : Bool → term → term → ExceptT String IO thm
  mk_numeral : Rat → Except String term
  inst_bitpat_numeral : term → ExceptT String IO (Nat → ExceptT String IO (List (term × term) × thm))
  WORD_RED_CONV : ioconv

/-- `bm_seq_numeral`'s `mk_fun` (bitmatch.ml 1172-1196). -/
partial def bmSeqMkFun [HolBase] (C : SeqCtx) (cs : term) :
    ExceptT String IO (Nat → term → ExceptT String IO thm) := do
  let tm ← liftExcept (mk_comb C.me cs)
  let th ← C.BM_FIRST_CASE_CONV tm
  let inst (e' : term) (th : thm) : ExceptT String IO thm :=
    if is_var C.e then INST [(e', C.e)] th else pure th
  match cs with
  | .Comb (.Comb (.Const "_SEQPATTERN" _) c) cs' =>
    let ps ← liftExcept (hd (hyp th))
    let pats ← (List.range C.sz).toArray.mapM (fun (i : Nat) =>
      tryFailure (do
        pure (some (← C.bm_skip_clause (C.pat_to_bit false (← liftExcept (C.mk_numeral (i : Rat)))) tm)))
        (fun _ => pure none))
    let f ← bmSeqMkFun C cs'
    pure (fun n e' => do
      match ← liftExcept (bitpat_matches c n) with
      | none =>
        let (ls, th') ← (← C.inst_bitpat_numeral ps) n
        PROVE_HYP th' (← INST ls th)
      | some i =>
        let th' ← match pats[i]? with
          | some (some th') => pure th'
          | some none => throw "Match_failure"
          | none => throw (invalidArgPrefix ++ "index out of bounds")
        let th1 ← inst e' th'
        let th2 ← match ← liftExcept (hd (hyp th1)) with
          | .Comb (.Const "~" _) p => EQF_ELIM (← ExceptT.mk (C.WORD_RED_CONV p))
          | p => EQT_ELIM (← ExceptT.mk (C.WORD_RED_CONV p))
        -- arguments right to left
        let r ← f n e'
        TRANS (← PROVE_HYP th2 th1) r)
  | .Comb (.Const "_ELSEPATTERN" _) _ => pure (fun _ e' => inst e' th)
  | _ => throw "bm_seq_numeral"

/-- `first_n` (bitmatch.ml 1215-1216). -/
def first_n {α : Type} : List α → Nat → List α
  | _, 0 => []
  | h :: t, n + 1 => h :: first_n t n
  | [], _ => []

/-- Do two patterns overlap? (bitmatch.ml 1218-1226) -/
def bmOverlaps (pat0 pat1 : Array (Option Bool)) (sz : Nat) : Except String Bool := do
  let overlaps_i (idx : Nat) : Except String Bool :=
    match pat0[idx]?, pat1[idx]? with
    | some (some b0), some (some b1) => .ok (b0 == b1)
    | some _, some _ => .ok true  -- always can assign bit(s) that make them equal
    | _, _ => .error (invalidArgPrefix ++ "index out of bounds")
  let mut idx := 0
  while idx < sz do
    if !(← overlaps_i idx) then return false
    idx := idx + 1
  return true

structure Tactics where
  -- @@FIELDS
  ONLY_BITMATCH_CASES_THEN : (List thm → tactic) → tactic
  BITMATCH_ASM_CASES_TAC : tactic
  BITMATCH_CASES_TAC : tactic
  bm_seq_numeral : term → ExceptT String IO (Nat → ExceptT String IO (term × thm))
  BITMATCH_SEQ_CONV : term → ExceptT String IO thm
  bm_check_disjointness : term → ExceptT String IO Unit
  deriving Inhabited

@[nospecialize]
def setupTactics [HolBase] (D : BitMatchDeps) (BDefs : Defs) (BAnalyze : Analyze) (BCases : Cases) (BNumeral : Numeral) (BConv : Conv) :
    ExceptT String IO Tactics := do
  -- @@SCOPE BEGIN
  let { WORD_RED_CONV, mk_numeral, .. } := D
  let { WITH_GOAL, .. } := BDefs
  let { bm_analyze_clauses, bm_skip_clause, dest_word_ty, pat_to_bit, .. } := BAnalyze
  let { BM_FIRST_CASE_CONV, .. } := BCases
  let { inst_bitpat_numeral, .. } := BNumeral
  let { BITMATCH_SIMP_CONV, bitpat_irrefutable_thm, .. } := BConv
  -- @@SCOPE END

  let ONLY_BITMATCH_CASES_THEN : (List thm → tactic) → tactic ← do
    let nty ← qty "N"
    pure (fun thltac => WITH_GOAL (fun w => tactic_of do
      let (e, cs) ← do
        let f : term → Bool := fun
          | .Comb (.Comb (.Const "_BITMATCH" _) _) _ => true
          | _ => false
        let (r, cs) ← liftExcept (do dest_comb (← find_term f w))
        pure (← liftExcept (rand r), cs)
      onlyBmTac bitpat_irrefutable_thm thltac e nty [] cs))

  let BITMATCH_ASM_CASES_TAC : tactic ← pure (
    ONLY_BITMATCH_CASES_THEN (fun thl =>
      CONV_TAC (TOP_SWEEP_CONV (BITMATCH_SIMP_CONV thl)) THEN
      MAP_EVERY ASSUME_TAC thl))

  let BITMATCH_CASES_TAC : tactic ← pure (
    ONLY_BITMATCH_CASES_THEN (fun thl => CONV_TAC (TOP_SWEEP_CONV (BITMATCH_SIMP_CONV thl))))

  -- (bm_seq_numeral `bitmatch e with ...` n) will
  -- return `word n` and `(bitmatch word n with ...) = res` where `res` is the
  -- appropriate match branch. Unlike BITMATCH_CONV this also works with matches
  -- with non-disjoint cases.  (`n` is a `Nat`.)
  let bm_seq_numeral : term → ExceptT String IO (Nat → ExceptT String IO (term × thm)) ←
    pure (fun tm => do
      match tm with
      | .Comb me@(.Comb (.Const "_BITMATCH" _) e) cs =>
        let N ← dest_word_ty (type_of e)
        let sz := ratNat (← liftExcept (dest_finty N))
        let word ← ExceptT.mk (mk_const "word" [(N, ← qty "N")])
        let f ← bmSeqMkFun ⟨me, e, sz, BM_FIRST_CASE_CONV, bm_skip_clause, pat_to_bit,
          mk_numeral, inst_bitpat_numeral, WORD_RED_CONV⟩ cs
        pure (fun n => do
          let e ← liftExcept (mk_comb word (← mk_numeral (n : Rat)))
          pure (e, ← f n e))
      | _ => throw "bm_seq_numeral")

  let BITMATCH_SEQ_CONV : term → ExceptT String IO thm ← pure (fun tm => do
    match tm with
    | .Comb (.Comb (.Const "_BITMATCH" _) (.Comb (.Const "word" _) n)) _ =>
      let k := ratNat (← liftExcept (dest_numeral n))
      pure (← (← bm_seq_numeral tm) k).2
    | _ => throw "BITMATCH_CONV")

  -- Given a bitmatch term 'tm', 'bm_check_disjointness tm' checks whether there
  -- exist two bit patterns that overlap. Two bit patterns overlap if there
  -- exists at least one bitvector that can be matched to both of them. If there
  -- exists such overlapping patterns, 'bm_check_disjointness' throws
  -- Invalid_argument. This function is useful when you want to ensure that
  -- the bitmatch can be successfully handled by BITMATCH_CONV.
  let bm_check_disjointness : term → ExceptT String IO Unit ← pure (fun tm => do
    match tm with
    -- (bitmatch.ml's `bitval`, renamed so it does not hide words.ml's)
    | .Comb (.Comb (.Const "_BITMATCH" _) bitval_tm) patterns =>
      let valty := type_of bitval_tm
      match valty with
      | .Tyapp "word" [N] =>
        let bitwidth := ratNat (← liftExcept (dest_finty N))
        let pattern_arrs ← bm_analyze_clauses bitwidth patterns
        let mut idx0 := 0
        for pattern0 in pattern_arrs do
          let mut idx1 := 0
          for pattern1 in first_n pattern_arrs idx0 do
            if ← liftExcept (bmOverlaps pattern0 pattern1 bitwidth) then
              let idx0_str := toString idx0
              let idx1_str := toString idx1
              throw (invalidArgPrefix ++ "Pattern number " ++ idx0_str ++
                " and pattern number " ++ idx1_str ++ " overlap")
            idx1 := idx1 + 1
          idx0 := idx0 + 1
      | _ => throw (invalidArgPrefix ++ "bm_check_disjointness: word's bitwidth is unknown")
    | _ => throw (invalidArgPrefix ++ "bm_check_disjointness: not bitmatch"))

  -- Unit tests for bm_check_disjointness
  bm_check_disjointness
    (← q "bitmatch (x:(2)word) with | [0b00:2] -> T | [0b10:2] -> T")
  bm_check_disjointness
    (← q "bitmatch (x:(2)word) with | [T; x] -> T | [F; y] -> T")
  let mustFail (s : String) : ExceptT String IO Unit := do
    let t ← q s
    match ← ExceptT.lift (bm_check_disjointness t).run with
    | .error e => if isInvalidArg e then pure () else throw e
    | .ok () => throw "Must fail"
  mustFail "bitmatch (x:(2)word) with | [0b00:2] -> T | [0b00:2] -> T"
  mustFail "bitmatch (x:(2)word) with | [T; x] -> T | [y; T] -> T"
  mustFail "bitmatch (x:(2)word) with | [0b11:2] -> T | [0b00:2] -> T | [0b00:2] -> T"

  -- @@RETURN BEGIN
  return { ONLY_BITMATCH_CASES_THEN, BITMATCH_ASM_CASES_TAC, BITMATCH_CASES_TAC,
           bm_seq_numeral, BITMATCH_SEQ_CONV, bm_check_disjointness }
  -- @@RETURN END

end HolLibrary.BitMatch
