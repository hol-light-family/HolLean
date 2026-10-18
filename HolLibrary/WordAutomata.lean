/- ========================================================================= -/
/- Generic-length analog of bit-blasting using automata.                     -/
/- ========================================================================= -/
/- File: HolLibrary/WordAutomata.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/word_automata.ml`, by hand, in file
  order, in the style of HolLibrary/Words.lean and HolLibrary/BDD.lean (see
  there and HolMath/Base.lean for the conventions).  word_automata.ml begins
  with `needs "Library/rstc.ml"` and `needs "Library/words.ml"` (which needs
  bdd.ml); the theorems it uses from them are supplied via the CoreThms
  structures, and their rules, conversions and BDD operations via
  WordAutomataDeps.  Each section is a bundle (a `structure`) built by a
  `setup` function; SessionLibrary/WordAutomata.lean builds the bundles in
  order and exports every name under its HOL Light name.  The reachability
  fixpoint loop and the other recursive OCaml functions are top-level
  `partial def`s.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, TAUT) they are bound first, in OCaml's
  order.
-/

import HolLibrary.RSTC
import HolLibrary.Words

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLibrary.BDD (Tables Bdd VTable UTable CTable)
open HolLight HolLight.Syntax

namespace HolLibrary.WordAutomata

-- @@COREFILL BEGIN
/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD1 ADD_EQ_0 ADD_SUB ADD_SYM AND_FORALL_THM ARITH_EQ ARITH_LE ARITH_LT
   BIT0 BIT1 BITVAL_CLAUSES BIT_GUARD BIT_WORD_0 BIT_WORD_ADD BIT_WORD_AND
   BIT_WORD_BITVAL BIT_WORD_INT_MIN BIT_WORD_ISHR BIT_WORD_NEG BIT_WORD_NOT
   BIT_WORD_OR BIT_WORD_OR_NEG BIT_WORD_SHL BIT_WORD_SUB BIT_WORD_USHR
   BIT_WORD_XOR CONJ_ACI DE_MORGAN_THM DIMINDEX_NONZERO DIVIDES_LE EXP_EQ_0
   FORALL_AND_THM FORALL_PAIR_FUN_THM FORALL_PAIR_THM FORALL_UNWIND_THM2 GE
   GT IMP_CONJ_ALT INT_GE INT_GT INT_MUL_RNEG INT_NOT_LT INT_OF_NUM_CLAUSES
   INT_POW IWORD_EQ LEFT_IMP_EXISTS_THM LET_TRANS LE_1 LE_CASES LE_EXP
   LT_IMP_NE MSB_IVAL NOT_LT NOT_SUC NUMERAL RIGHT_FORALL_IMP_THM
   RTC_INDUCT_L RTC_RULES SUC_SUB1 WORD_ADD_OR WORD_AND_0 WORD_AND_1
   WORD_EQ_BITS WORD_EQ_BITS_ALT WORD_ISHR_COMPOSE WORD_ISHR_ZERO WORD_IWORD
   WORD_MUL_0 WORD_OR_0 WORD_OR_EQ_0 : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (WORD_SHL_COMPOSE WORD_SHL_ZERO WORD_USHR_COMPOSE WORD_USHR_ZERO WORD_XOR_0
   WORD_XOR_EQ_0 bitval irelational2 num_CASES num_INDUCTION num_divides
   relational2 word_INT_MIN word_ige word_igt word_ile word_ilt word_ugt
   word_ule word_ult : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms3 where
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms4 where
  deriving Inhabited

-- @@COREFILL END

/-- What wordautomata.ml uses from Session besides theorems. -/
structure WordAutomataDeps where
  -- definitions and parser state
  define : String → ExceptT String IO thm
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  INTEGER_RULE : term → ExceptT String IO thm
  NUMBER_RULE : term → ExceptT String IO thm
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  -- conversions and rules from Session
  NUM_REDUCE_CONV : ioconv
  NUM_RED_CONV : ioconv
  NNFC_CONV : ioconv
  CNF_CONV : ioconv
  PRENEX_CONV : ioconv
  GEN_BETA_CONV : ioconv
  num_CONV : ioconv
  TAUT : term → ExceptT String IO thm
  DISJ_ACI_RULE : term → ExceptT String IO thm
  /-- bdd.ml's `BDD_VAR`, `BDD_OF_TERM`, ...: the raw BDD operations
      exported from SessionLibrary.BDD (the `BDDThms` is applied by Session). -/
  mk_vtable : Int → ExceptT String IO VTable
  mk_utable : ExceptT String IO UTable
  mk_ctable : ExceptT String IO CTable
  BDD_VAR : Tables → term → ExceptT String IO Bdd
  BDD_OF_TERM : Func term Bdd → Tables → term → ExceptT String IO Bdd
  BDD_AND : Tables → Bdd × Bdd → ExceptT String IO Bdd
  BDD_OR : Tables → Bdd × Bdd → ExceptT String IO Bdd
  BDD_IMP : Tables → Bdd × Bdd → ExceptT String IO Bdd
  BDD_EXISTS : Tables → term → ExceptT String IO (Bdd → ExceptT String IO Bdd)
  /-- words.ml's bit-blasting rule/tactic and reduction conv (from
      SessionLibrary.Words). -/
  BITBLAST_TAC : tactic
  BITBLAST_RULE : term → ExceptT String IO thm
  WORD_RED_CONV : ioconv
  WORD_RULE : term → ExceptT String IO thm
  WORD_ARITH : term → ExceptT String IO thm
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3
  core4 : CoreThms4

/- ------------------------------------------------------------------------- -/
/- Use reachable states (or any overapproximation) to verify reachability.   -/
/- ------------------------------------------------------------------------- -/

/-- The `fixpoint`/`aux` loop of REACHABLE_STATE_TAC (word_automata.ml). -/
private partial def reachFixaux
    (step : Bdd × Bdd → ExceptT String IO (Bdd × Bdd))
    (reachedfix : (Bdd × Bdd) → (Bdd × Bdd) → ExceptT String IO Bool)
    (n : Nat) (p : Bdd × Bdd) : ExceptT String IO ((Bdd × Bdd) × (Bdd × Bdd)) := do
  let p' ← step p
  if ← reachedfix p p' then
    let _ ← (report
      ("Fixpoint reached after " ++ toString n ++ " iteration" ++
       (if n == 1 then "" else "s")) : IO Unit)
    pure (p, p')
  else do
    let _ ← (remark ("No fixpoint after iteration " ++ toString n) : IO Unit)
    reachFixaux step reachedfix (n + 1) p'

structure Reachable where
  -- @@FIELDS
  OVERAPPROXIMATE_REACHABLE : thm
  REACHABLE_STATE_TAC : tactic
  deriving Inhabited

@[nospecialize]
def setupReachable [HolBase] (D : WordAutomataDeps) :
    ExceptT String IO Reachable := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, .. } := D
  let { FORALL_PAIR_THM, IMP_CONJ_ALT, LEFT_IMP_EXISTS_THM, RIGHT_FORALL_IMP_THM,
        RTC_INDUCT_L, .. } := D.core1
  -- @@SCOPE END

  let OVERAPPROXIMATE_REACHABLE ← prove
   r"!init step final invariant.
        (!s. init s ==> invariant s) /\
        (!s s'. invariant s /\ step s s' ==> invariant s') /\
        (!s. invariant s ==> final s)
        ==> (!s s':S. init s /\ RTC step s s' ==> final s')"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"!s s':S. init s /\ RTC step s s' ==> invariant s'") MP_TAC THENL
     [REWRITE_TAC [IMP_CONJ_ALT, RIGHT_FORALL_IMP_THM], ASM_MESON_TAC []] THEN
    MATCH_MP_TAC RTC_INDUCT_L THEN ASM_MESON_TAC [])

  /- --------------------------------------------------------------------- -/
  /- Classic "model checking" forward reachability fixpoint loop with BDDs. -/
  /-                                                                        -/
  /- The states P_k reachable in <= k steps from the initial state P are    -/
  /-                                                                        -/
  /-       P_0 s <=> P s                                                    -/
  /-   P_{k+1} s <=> P_k s \/ ?s'. P_k s' /\ R s' s                         -/
  /-                                                                        -/
  /- To avoid additional renaming, which is fiddlier with inference-based   -/
  /- BDDs, we derive pairs (P_k s,P_k s') in the main recursion step.       -/
  /- --------------------------------------------------------------------- -/

  let REACHABLE_STATE_TAC : tactic ← pure (fun gl => tactic_of (do
    let (_asl, w) := gl
    let (istm, ftm) ← liftExcept (dest_imp (strip_forall w).2)
    let (itm, stm) ← liftExcept (dest_conj istm)
    let pinit ← liftExcept (rator itm)
    let ptrans ← liftExcept (do lhand (← rator stm))
    let pfinal' ← liftExcept (rator ftm)
    let (gtup, _gbod) ← liftExcept (do dest_gabs (← rator itm))
    let k := (striplist HolMath.Pair.dest_pair gtup).length
    -- `let k = length(striplist dest_pair(fst(dest_gabs(rator itm))))`
    let _ ← (remark ("State space size 2^" ++ toString k ++
                     " = " ++ string_of_num (pow2 (Int.ofNat k))) : IO Unit)
    let (tups, trans) := strip_gabs ptrans
    let (tup, tup') ← match tups with | [a, b] => pure (a, b) | _ => throw "strip_gabs"
    let (tup'', init) ← liftExcept (dest_gabs pinit)
    let _ ← if tup != tup'' then throw "inconsistent variables" else pure ()
    let (tup''', final') ← liftExcept (dest_gabs pfinal')
    let _ ← if tup' != tup''' then throw "inconsistent variables" else pure ()
    let vars := striplist HolMath.Pair.dest_pair tup
    let vars' := striplist HolMath.Pair.dest_pair tup'
    let vt ← D.mk_vtable (Int.ofNat (vars.length + vars'.length))
    let ut ← D.mk_utable
    let ct ← D.mk_ctable
    let bddstate : Tables := (vt, ut, ct)
    let bddvars := itlist (fun (ab : term × term) c => ab.1 :: ab.2 :: c)
                          (← liftExcept (zip vars vars')) []
    let _ ← bddvars.forM (fun v => do let _ ← D.BDD_VAR bddstate v; pure ())
    let bdd_trans ← D.BDD_OF_TERM undefined bddstate trans
    let bdd_init ← D.BDD_OF_TERM undefined bddstate init
    let twizzle (t : term) : Except String term := do
      let sub ← vsubst ((← zip vars vars') ++ (← zip vars' vars))
      pure (sub t)
    let trans' ← liftExcept (twizzle trans)
    let init' ← liftExcept (twizzle init)
    let final ← liftExcept (twizzle final')
    let bdd_trans' ← D.BDD_OF_TERM undefined bddstate trans'
    let bdd_init' ← D.BDD_OF_TERM undefined bddstate init'
    let step (p : Bdd × Bdd) : ExceptT String IO (Bdd × Bdd) := do
      let (pk, pk') := p
      let a ← do
        let andr ← D.BDD_AND bddstate (pk', bdd_trans')
        let ex ← vars'.foldrM (fun v acc => do (← D.BDD_EXISTS bddstate v) acc) andr
        D.BDD_OR bddstate (pk, ex)
      let b ← do
        let andr ← D.BDD_AND bddstate (pk, bdd_trans)
        let ex ← vars.foldrM (fun v acc => do (← D.BDD_EXISTS bddstate v) acc) andr
        D.BDD_OR bddstate (pk', ex)
      pure (a, b)
    let reachedfix (before after : Bdd × Bdd) : ExceptT String IO Bool := do
      let ok := before.1.1 == after.1.1
      let ok' := before.2.1 == after.2.1
      if ok != ok' then throw "reachedfix: sanify check"
      else pure ok
    let p0 : Bdd × Bdd := (bdd_init, bdd_init')
    let ((pk, pk'), (_pl, pl')) ← reachFixaux step reachedfix 1 p0
    let bdd_final ← D.BDD_OF_TERM undefined bddstate final
    let th_init ← EQT_ELIM (← D.BDD_IMP bddstate (bdd_init, pk)).2
    let th_fix ← TRANS pl'.2 (← SYM pk'.2)
    let th_final ← EQT_ELIM (← D.BDD_IMP bddstate (pk, bdd_final)).2
    let th_init' ← GENL vars th_init
    let th_fix' ← do
      let mp ← MATCH_MP (← D.TAUT (← q r"(p \/ q <=> r) ==> q ==> r")) th_fix
      let rec fp (n : Nat) (t : thm) : ExceptT String IO thm := match n with
        | 0 => pure t
        | n+1 => do fp n (← PURE_ONCE_REWRITE_RULE [LEFT_IMP_EXISTS_THM] t)
      let g ← GENL vars (← fp vars.length mp)
      let sp ← SPECL (vars' ++ vars) g
      GENL (vars ++ vars') sp
    let th_final' ← GENL vars th_final
    let vtm ← ExceptT.mk (mk_gabs tup (← liftExcept (do lhand (concl pk.2))))
    let pty ← vars.map type_of |>.foldrM (fun ty acc => ExceptT.mk (mk_fun_ty ty acc)) aty
    let pva := mk_var "P" pty
    let gab ← ExceptT.mk (mk_gabs tup (← liftExcept (list_mk_comb pva vars)))
    let rth ← ExceptT.mk (D.GEN_BETA_CONV (← liftExcept (mk_comb gab tup)))
    pure (MATCH_MP_TAC OVERAPPROXIMATE_REACHABLE THEN
     PURE_REWRITE_TAC [FORALL_PAIR_THM] THEN EXISTS_TAC vtm THEN
     PURE_REWRITE_TAC [rth] THEN
     CONJ_TAC THENL [ACCEPT_TAC th_init', ALL_TAC] THEN
     CONJ_TAC THENL [ACCEPT_TAC th_fix', ACCEPT_TAC th_final'])) gl)

  -- @@RETURN BEGIN
  return { OVERAPPROXIMATE_REACHABLE, REACHABLE_STATE_TAC }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Expand multi-bit shifts into repeated 1-bit shifts.                       -/
/- ------------------------------------------------------------------------- -/

/-- The recursive `conv` inside EXPAND_SHIFT_CONV (word_automata.ml). -/
private partial def expandShiftConv [HolBase] (num_CONV baseconv stepconv : ioconv) :
    ioconv := fun tm => ExceptT.run do
  match tm with
  | .Comb (.Comb _ _) ntm =>
      let n ← liftExcept (HolMath.Nums.dest_small_numeral ntm)
      if n == 0 then ExceptT.mk (baseconv tm)
      else if n == 1 then pure (REFL tm)
      else ExceptT.mk ((RAND_CONV num_CONV THENC stepconv THENC
                        expandShiftConv num_CONV baseconv stepconv) tm)
  | _ => throw "EXPAND_SHIFT_CONV: inapplicable"

structure Shifts where
  -- @@FIELDS
  EXPAND_SHIFT_CONV : ioconv
  word_shladd : thm
  WORD_SHLADD : thm
  BIT_WORD_SHLADD : thm
  WORD_SHLADD_0 : thm
  WORD_NUMERAL_SHLADD : thm
  WORD_USHR_SHLADD : thm
  WORD_ISHR_SHLADD : thm
  DEFINE_WORD_INT_MIN : thm
  deriving Inhabited

@[nospecialize]
def setupShifts [HolBase] (D : WordAutomataDeps) :
    ExceptT String IO Shifts := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, INTEGER_RULE, MESON, MESON_TAC, NUMBER_RULE, NUM_REDUCE_CONV, TAUT,
        WORD_RULE, .. } := D
  let { ADD1, ADD_EQ_0, ADD_SUB, ADD_SYM, ARITH_EQ, ARITH_LE, ARITH_LT, BIT0, BIT1,
        BITVAL_CLAUSES, BIT_GUARD, BIT_WORD_0, BIT_WORD_AND, BIT_WORD_BITVAL,
        BIT_WORD_INT_MIN, BIT_WORD_ISHR, BIT_WORD_OR, BIT_WORD_SHL, BIT_WORD_USHR,
        CONJ_ACI, DIMINDEX_NONZERO, DIVIDES_LE, EXP_EQ_0, FORALL_AND_THM, INT_MUL_RNEG,
        INT_OF_NUM_CLAUSES, INT_POW, IWORD_EQ, LE_1, LE_EXP, LT_IMP_NE, NOT_SUC,
        NUMERAL, SUC_SUB1, WORD_ADD_OR, WORD_AND_0, WORD_AND_1, WORD_EQ_BITS_ALT,
        WORD_ISHR_COMPOSE, WORD_ISHR_ZERO, WORD_IWORD, WORD_OR_0, .. } := D.core1
  let { WORD_SHL_COMPOSE, WORD_SHL_ZERO, WORD_USHR_COMPOSE, WORD_USHR_ZERO, bitval,
        num_CASES, num_divides, word_INT_MIN, .. } := D.core2
  -- @@SCOPE END

  let EXPAND_SHIFT_CONV : ioconv ← do
    let pth ← prove
     r"(!x n. word_shl x (SUC n):N word = word_shl (word_shl x 1) n) /\
     (!x n. word_ushr x (SUC n):N word = word_ushr (word_ushr x 1) n) /\
     (!x n. word_ishr x (SUC n):N word = word_ishr (word_ishr x 1) n)"
     (REWRITE_TAC [WORD_SHL_COMPOSE, WORD_USHR_COMPOSE, WORD_ISHR_COMPOSE] THEN
      REWRITE_TAC [ADD1, ADD_SYM])
    let baseconv ← GEN_REWRITE_CONV_NET I
      [WORD_SHL_ZERO, WORD_USHR_ZERO, WORD_ISHR_ZERO]
    let stepconv ← GEN_REWRITE_CONV_NET I [pth]
    let conv : ioconv := expandShiftConv D.num_CONV baseconv stepconv
    pure (fun tm => ExceptT.run do
      match tm with
      | .Comb (.Comb (.Const "word_shl" _) _x) ntm
      | .Comb (.Comb (.Const "word_ushr" _) _x) ntm
      | .Comb (.Comb (.Const "word_ishr" _) _x) ntm =>
          if HolMath.Nums.is_numeral ntm && !((← liftExcept (HolMath.Nums.dest_small_numeral ntm)) == 1) then
            ExceptT.mk (conv tm)
          else throw "EXPAND_SHIFT_CONV: inapplicable"
      | _ => throw "EXPAND_SHIFT_CONV: inapplicable")

  /- --------------------------------------------------------------------- -/
  /- A useful operation for both shifts and specific numerals.             -/
  /- --------------------------------------------------------------------- -/

  let word_shladd ← D.define
   r"word_shladd (x:N word) b = word_or (word_shl x 1) (word(bitval b))"

  let WORD_SHLADD ← prove
   r"!(x:N word) b.
        word_shladd (x:N word) b = word_add (word_shl x 1) (word(bitval b))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [word_shladd] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORD_ADD_OR THEN
    REWRITE_TAC [bitval] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [WORD_AND_0, WORD_AND_1, BIT_WORD_SHL] THEN
    CONV_TAC NUM_REDUCE_CONV)

  let BIT_WORD_SHLADD ← prove
   r"(!(x:N word) b. bit 0 (word_shladd x b) <=> b) /\
   (!(x:N word) b i. bit (i + 1) (word_shladd x b) <=>
                     i + 1 < dimindex(:N) /\ bit i x)"
   (REWRITE_TAC [word_shladd, BIT_WORD_OR, BIT_WORD_SHL, BIT_WORD_BITVAL] THEN
    SIMP_TAC [ADD_EQ_0, LE_1, ADD_SUB, ARITH_EQ, DIMINDEX_NONZERO] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [CONJ_ACI])

  let WORD_SHLADD_0 ← prove
   r"!x:N word. word_shladd x F = word_shl x 1"
   (REWRITE_TAC [word_shladd, BITVAL_CLAUSES, WORD_OR_0])

  let WORD_NUMERAL_SHLADD ← prove
   r"word(NUMERAL(BIT0 n)):N word = word_shladd (word(NUMERAL n)) F /\
   word(NUMERAL(BIT1 n)):N word = word_shladd (word(NUMERAL n)) T"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [NUMERAL, BIT0, BIT1] THEN
    REWRITE_TAC [WORD_SHLADD, BITVAL_CLAUSES, WORD_OR_0, ADD1] THEN
    CONV_TAC WORD_RULE)

  /- --------------------------------------------------------------------- -/
  /- Expressing right shifts in terms of left, and characterizing top bit. -/
  /- --------------------------------------------------------------------- -/

  let (WORD_USHR_SHLADD, WORD_ISHR_SHLADD) ← (do
    let th ← prove
     r"(!x y:N word.
        word_ushr x 1 = y <=>
        word_and word_INT_MIN y = word 0 /\
        word_shladd y (bit 0 x) = x) /\
   (!x y:N word.
        word_ishr x 1 = y <=>
        word_and word_INT_MIN y = word_and word_INT_MIN x /\
        word_shladd y (bit 0 x) = x)"
     (← do
      let a7 ← ARITH_RULE (← q r"i < n - 1 <=> SUC i < n")
      let m6 ← MESON [num_CASES]
       (← q r"(!i. P i) <=> P 0 /\ (!i. P(SUC i))")
      let a5 ← ARITH_RULE (← q r"n - 1 < n <=> ~(n = 0)")
      let t4 ← TAUT (← q r"p \/ q ==> r <=> (p ==> r) /\ (q ==> r)")
      let a3 ← ARITH_RULE (← q r"~(n = 0) ==> (i < n <=> i = n - 1 \/ i < n - 1)")
      let a2 ← ARITH_RULE (← q r"i < n ==> (i + 1 < n <=> ~(i = n - 1))")
      pure (REPEAT STRIP_TAC THEN
      REWRITE_TAC [WORD_EQ_BITS_ALT, BIT_WORD_AND, BIT_WORD_INT_MIN] THEN
      REWRITE_TAC [word_shladd, BIT_WORD_OR, BIT_WORD_BITVAL] THEN
      SIMP_TAC [BIT_WORD_SHL, BIT_WORD_USHR, BIT_WORD_ISHR, BIT_WORD_0] THENL
       [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [BIT_GUARD], ALL_TAC] THEN
      SIMP_TAC [a2] THEN
      CONV_TAC (LAND_CONV (SIMP_CONV [DIMINDEX_NONZERO, a3])) THEN
      SIMP_TAC [LT_IMP_NE, t4] THEN
      REWRITE_TAC [FORALL_AND_THM] THEN
      (BINOP_TAC THENL
        [MESON_TAC [DIMINDEX_NONZERO, a5], ALL_TAC]) THEN
      GEN_REWRITE_TAC RAND_CONV [m6] THEN
      SIMP_TAC [NOT_SUC, LE_1, ARITH_LE, ARITH_LT, SUC_SUB1, ← GSYM ADD1] THEN
      MESON_TAC [a7]))
    CONJ_PAIR th)

  let DEFINE_WORD_INT_MIN ← prove
   r"~(word_INT_MIN:N word = word 0) /\
   word_shladd word_INT_MIN F :N word = word 0"
   (← do
    let a6 ← ARITH_RULE (← q r"n <= n - 1 <=> n = 0")
    let n5 ← NUMBER_RULE (← q r"(n:num) divides n")
    let a4 ← ARITH_RULE (← q r"~(n = 0) ==> SUC(n - 1) = n")
    let i3 ← INTEGER_RULE (← q r"(--x:int == &0) (mod n) <=> n divides x")
    let w2 ← WORD_RULE (← q r"word_shl (iword x) 1 = iword(&2 * x)")
    pure (REWRITE_TAC [WORD_SHLADD_0, word_INT_MIN, w2] THEN
    REWRITE_TAC [WORD_IWORD, IWORD_EQ, INT_MUL_RNEG] THEN
    REWRITE_TAC [i3] THEN
    SIMP_TAC [← GSYM (← CONJUNCT2 INT_POW), DIMINDEX_NONZERO, a4] THEN
    REWRITE_TAC [INT_OF_NUM_CLAUSES, ← GSYM num_divides] THEN
    REWRITE_TAC [n5] THEN
    DISCH_THEN (MP_TAC o MATCH_MP DIVIDES_LE) THEN
    REWRITE_TAC [LE_EXP, EXP_EQ_0, ARITH_EQ] THEN
    REWRITE_TAC [DIMINDEX_NONZERO, a6]))

  -- @@RETURN BEGIN
  return { EXPAND_SHIFT_CONV, word_shladd, WORD_SHLADD, BIT_WORD_SHLADD, WORD_SHLADD_0,
           WORD_NUMERAL_SHLADD, WORD_USHR_SHLADD, WORD_ISHR_SHLADD, DEFINE_WORD_INT_MIN }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Identify shift-right terms, and terms involving carry from bit i to i + 1 -/
/- ------------------------------------------------------------------------- -/

/-- `is_shr tm` (word_automata.ml). -/
def is_shr (tm : term) : Bool :=
  match tm with
  | .Comb (.Comb (.Const "word_ushr" _) _) _ => true
  | .Comb (.Comb (.Const "word_ishr" _) _) _ => true
  | _ => false

/-- `carrying tm` (word_automata.ml). -/
def carrying (tm : term) : Bool :=
  match tm with
  | .Comb (.Comb (.Const "word_add" _) _) _ => true
  | .Comb (.Comb (.Const "word_sub" _) _) _ => true
  | .Comb (.Comb (.Const "word_shladd" _) _) _ => true
  | .Comb (.Const "word_neg" _)
      (.Comb (.Const "word" _) (.Comb (.Const "bitval" _) _)) => false
  | .Comb (.Const "word_neg" _) _ => true
  | _ => false

/- ------------------------------------------------------------------------- -/
/- Expressing inequalities in terms of the top bit, and reducing to Horn.    -/
/- ------------------------------------------------------------------------- -/

structure Ineq where
  -- @@FIELDS
  VAL_LT_ELIM_THM : thm
  IVAL_LT_ELIM_THM : thm
  IVAL_LT_0_ELIM_THM : thm
  CONJ_WORD_EQ_0 : thm
  DISJ_WORD_EQ_0 : thm
  deriving Inhabited

@[nospecialize]
def setupIneq [HolBase] (D : WordAutomataDeps) :
    ExceptT String IO Ineq := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, TAUT, WORD_ARITH, .. } := D
  let { BIT_WORD_0, BIT_WORD_AND, BIT_WORD_INT_MIN, BIT_WORD_OR_NEG,
        FORALL_UNWIND_THM2, LET_TRANS, LE_CASES, MSB_IVAL, WORD_EQ_BITS,
        WORD_EQ_BITS_ALT, WORD_OR_EQ_0, .. } := D.core1
  -- @@SCOPE END

  let VAL_LT_ELIM_THM ← prove
   r"!x y:N word.
        val x < val y <=>
        ~(word_and word_INT_MIN
                   (word_or (word_and (word_not x) y)
                            (word_and (word_or (word_not x) y)
                                      (word_sub x y))) =
          word 0)"
   (← do
    let t1 ← TAUT (← q r"~(p /\ q /\ r) <=> q ==> p ==> ~r")
    pure (REWRITE_TAC [WORD_EQ_BITS, BIT_WORD_AND, BIT_WORD_INT_MIN, BIT_WORD_0] THEN
    SIMP_TAC [FORALL_UNWIND_THM2, t1] THEN
    CONV_TAC WORD_ARITH))

  let IVAL_LT_ELIM_THM ← prove
   r"!x y:N word.
        ival x < ival y <=>
        ~(word_and word_INT_MIN
                   (word_or (word_and x (word_not y))
                            (word_and (word_not(word_xor x y))
                                      (word_sub x y))) =
          word 0)"
   (← do
    let t1 ← TAUT (← q r"~(p /\ q /\ r) <=> q ==> p ==> ~r")
    pure (REWRITE_TAC [WORD_EQ_BITS, BIT_WORD_AND, BIT_WORD_INT_MIN, BIT_WORD_0] THEN
    SIMP_TAC [FORALL_UNWIND_THM2, t1] THEN
    CONV_TAC WORD_ARITH))

  let IVAL_LT_0_ELIM_THM ← prove
   r"!x:N word.
        ival x < &0 <=> ~(word_and word_INT_MIN x = word 0)"
   (← do
    let t1 ← TAUT (← q r"~(p /\ q /\ r) <=> q ==> p ==> ~r")
    pure (REWRITE_TAC [← GSYM MSB_IVAL, WORD_EQ_BITS, BIT_WORD_AND,
                BIT_WORD_INT_MIN, BIT_WORD_0] THEN
    SIMP_TAC [FORALL_UNWIND_THM2, t1] THEN
    CONV_TAC WORD_ARITH))

  /- --------------------------------------------------------------------- -/
  /- Useful to reduce to the Horn case.                                    -/
  /- --------------------------------------------------------------------- -/

  let CONJ_WORD_EQ_0 ← GSYM WORD_OR_EQ_0

  let DISJ_WORD_EQ_0 ← prove
   r"!x y:N word.
        x = word 0 \/ y = word 0 <=>
        word_and (word_or x (word_neg x)) (word_or y (word_neg y)) = word 0"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [WORD_EQ_BITS_ALT] THEN
    SIMP_TAC [BIT_WORD_AND, BIT_WORD_OR_NEG, BIT_WORD_0] THEN
    MESON_TAC [LE_CASES, LET_TRANS])

  -- @@RETURN BEGIN
  return { VAL_LT_ELIM_THM, IVAL_LT_ELIM_THM, IVAL_LT_0_ELIM_THM, CONJ_WORD_EQ_0,
           DISJ_WORD_EQ_0 }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Convert canonical goal into Boolean reachability.                         -/
/- Basic tactic for special Horn s = 0 ==> t = 0 case.                       -/
/- ------------------------------------------------------------------------- -/

/-- `tryfind (fun f -> f x) rules` (word_automata.ml's *_CARRY_RULE). -/
private def tryfindRule (rules : List (thm → ExceptT String IO thm)) (x : thm) :
    ExceptT String IO thm := do
  match rules with
  | [] => throw "tryfind"
  | f :: fs => tryCatch (f x) (fun _ => tryfindRule fs x)

structure Horn where
  -- @@FIELDS
  WORD_AUTO_TRANSIFY_TAC : tactic
  LSB_CARRYING : thm
  XSB_CARRYING : thm
  ABBREVIATE_SHR_TAC : tactic
  ABBREVIATE_CARRYING_TAC : tactic
  LSB_CARRY_RULE : thm → ExceptT String IO thm
  XSB_CARRY_RULE : thm → ExceptT String IO thm
  BIT_PUSH_CONV : ioconv
  LSB_SIMP_CONV : ioconv
  MSB_SIMP_CONV : ioconv
  HORN_WORD_AUTO_TAC : tactic
  CORE_WORD_AUTO_TAC : tactic
  deriving Inhabited

@[nospecialize]
def setupHorn [HolBase] (D : WordAutomataDeps) (BReachable : Reachable) (BShifts : Shifts) (BIneq : Ineq) :
    ExceptT String IO Horn := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON, NUM_REDUCE_CONV, TAUT, .. } := D
  let { ADD1, ADD_SUB, AND_FORALL_THM, BIT_WORD_0, BIT_WORD_ADD, BIT_WORD_AND,
        BIT_WORD_NEG, BIT_WORD_NOT, BIT_WORD_OR, BIT_WORD_SUB, BIT_WORD_XOR,
        DE_MORGAN_THM, DIMINDEX_NONZERO, FORALL_PAIR_FUN_THM, LE_1, RTC_RULES,
        WORD_EQ_BITS_ALT, .. } := D.core1
  let { num_INDUCTION, .. } := D.core2
  let { REACHABLE_STATE_TAC, .. } := BReachable
  let { BIT_WORD_SHLADD, .. } := BShifts
  let { CONJ_WORD_EQ_0, DISJ_WORD_EQ_0, .. } := BIneq
  -- @@SCOPE END

  let WORD_AUTO_TRANSIFY_TAC : tactic ← do
    let pth ← prove
     r"!step init final b n.
          (!s s':S. init s /\ RTC step s s' ==> final s')
          ==> init(b 0)
              ==> (!i. i + 1 < n ==> step (b i) (b(i+1)))
                  ==> !i. i < n ==> final(b i)"
     (← do
      let a1 ← ARITH_RULE (← q r"i + 1 < n ==> i < n")
      pure (REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN (← q r"!i. i < n ==> RTC step ((b:num->S) 0) (b i)")
      MP_TAC THENL [MATCH_MP_TAC num_INDUCTION, ASM_MESON_TAC []] THEN
      ASM_MESON_TAC [RTC_RULES, ADD1, a1]))
    let n_ty ← qty "N"
    let plus ← q r"(+):num->num->num"
    let one_tm ← q "1"
    let has_word_ty (tm : term) : Bool :=
      match type_of tm with
      | .Tyapp "word" [_] => true
      | _ => false
    let boolify (tm : term) : Except String term :=
      match tm with
      | .Var s _ => .ok (mk_var s bool_ty)
      | _ => .error "boolify"
    let mk_bit (itm tm : term) : ExceptT String IO term :=
      match type_of tm with
      | .Tyapp "word" [nty] => do
          let bitc ← ExceptT.mk (mk_const "bit" [(nty, n_ty)])
          liftExcept (do mk_comb (← mk_comb bitc itm) tm)
      | _ => throw "mk_bit"
    let plus1 (itm : term) : Except String term := do mk_comb (← mk_comb plus itm) one_tm
    pure (fun gl => tactic_of (do
      let (_asl, w) := gl
      let wvs := filter has_word_ty (frees w)
      let bvs ← liftExcept (variants (frees w) (← liftExcept (wvs.mapM boolify)))
      let bvs' ← liftExcept (variants (bvs ++ frees w) bvs)
      let btup ← end_itlist (fun a b => ExceptT.mk (HolMath.Pair.mk_pair (a, b))) bvs
      let btup' ← end_itlist (fun a b => ExceptT.mk (HolMath.Pair.mk_pair (a, b))) bvs'
      let (init, stepconc) ← liftExcept (dest_imp w)
      let zero ← q "0"
      let init' ← do
        let bits ← wvs.mapM (fun v => mk_bit zero v)
        let subf ← ExceptT.mk (subst (← liftExcept (zip bvs bits)))
        let sub ← ExceptT.mk (subf init)
        ExceptT.mk (mk_gabs btup sub)
      let (step, conc) ← liftExcept (dest_imp stepconc)
      let (itm, stepimp) ← liftExcept (dest_forall step)
      let step' ← do
        let b1 ← wvs.mapM (fun v => mk_bit itm v)
        let p1 ← liftExcept (plus1 itm)
        let b2 ← wvs.mapM (fun v => mk_bit p1 v)
        let s1 ← liftExcept (zip bvs b1)
        let s2 ← liftExcept (zip bvs' b2)
        let subf ← ExceptT.mk (subst (s1 ++ s2))
        let sub ← ExceptT.mk (subf (← liftExcept (rand stepimp)))
        ExceptT.mk (list_mk_gabs [btup, btup'] sub)
      let (jtm, finalimp) ← liftExcept (dest_forall conc)
      let final' ← do
        let bits ← wvs.mapM (fun v => mk_bit jtm v)
        let subf ← ExceptT.mk (subst (← liftExcept (zip bvs' bits)))
        let sub ← ExceptT.mk (subf (← liftExcept (rand finalimp)))
        ExceptT.mk (mk_gabs btup' sub)
      let th1 ← ISPECL [step', init', final'] pth
      let th2 ← REWRITE_RULE [FORALL_PAIR_FUN_THM] th1
      let th3 ← SPECL (← wvs.mapM (fun v => do liftExcept (mk_abs itm (← mk_bit itm v)))) th2
      let th4 ← CONV_RULE (TOP_DEPTH_CONV D.GEN_BETA_CONV) th3
      pure (MATCH_MP_TAC th4)) gl)

  let LSB_CARRYING ← prove
   r"(!x z:N word. word_neg x = z ==> (bit 0 z <=> bit 0 x)) /\
   (!x y z:N word. word_add x y = z ==> (bit 0 z <=> ~(bit 0 x <=> bit 0 y))) /\
   (!x y z:N word. word_sub x y = z ==> (bit 0 z <=> ~(bit 0 x <=> bit 0 y))) /\
   (!x (z:N word) b. word_shladd x b = z ==> (bit 0 z <=> b)) /\
   (!a b:N word. a = b ==> (bit 0 a <=> bit 0 b))"
   (REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [BIT_WORD_NEG, BIT_WORD_ADD,
                     BIT_WORD_SUB, BIT_WORD_SHLADD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC [LE_1, DIMINDEX_NONZERO])

  let XSB_CARRYING ← prove
   r"(!x z:N word.
        word_neg x = z
        ==> !i. i + 1 < dimindex(:N)
                ==> (bit (i + 1) z <=>
                     (bit (i + 1) x <=> ~bit i x /\ ~bit i z))) /\
   (!x y z:N word.
        word_add x y = z
        ==> !i. i + 1 < dimindex(:N)
                ==> (bit (i + 1) z <=>
                     ((bit (i + 1) x <=> bit (i + 1) y) <=>
                      bit i x /\ bit i y \/
                      (bit i x \/ bit i y) /\ ~bit i z))) /\
   (!x y z:N word.
        word_sub x y = z
        ==> !i. i + 1 < dimindex(:N)
                ==> (bit (i + 1) z <=>
                     ((bit (i + 1) x <=> bit (i + 1) y) <=>
                      ~bit i x /\ bit i y \/
                      (~bit i x \/ bit i y) /\ bit i z))) /\
   (!x (z:N word) b.
        word_shladd x b = z
        ==> !i. i + 1 < dimindex(:N) ==> (bit (i + 1) z <=> bit i x)) /\
   (!a b:N word.
        a = b
        ==> !i. i + 1 < dimindex(:N) ==> (bit (i + 1) a = bit (i + 1) b))"
   (← do
    let a1 ← ARITH_RULE (← q r"~(i + 1 = 0) /\ 1 <= i + 1")
    pure (REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN (fun th => tactic_of do pure (ASSUME_TAC th THEN SUBST1_TAC (← SYM th))) THEN
    REWRITE_TAC [] THEN GEN_TAC THEN DISCH_TAC THEN
    GEN_REWRITE_TAC LAND_CONV
     [BIT_WORD_NEG, BIT_WORD_ADD, BIT_WORD_SUB, BIT_WORD_SHLADD] THEN
    ASM_REWRITE_TAC [ADD_SUB, a1]))

  let ABBREVIATE_SHR_TAC : tactic ← pure (fun gl => tactic_of (do
    let (_asl, w) := gl
    match sort free_in (find_terms is_shr w) with
    | t :: _ => do
        let mkeq ← ExceptT.mk mk_eq
        let eq ← liftExcept (mkeq ((← genvar (type_of t)), t))
        pure (ABBREV_TAC eq)
    | _ => throw "ABBREVIATE_SHR_TAC: No word_ushr/word_ishr subterms") gl)

  let ABBREVIATE_CARRYING_TAC : tactic ← pure (fun gl => tactic_of (do
    let (_asl, w) := gl
    match sort free_in (find_terms carrying w) with
    | t :: _ => do
        let mkeq ← ExceptT.mk mk_eq
        let eq ← liftExcept (mkeq ((← genvar (type_of t)), t))
        pure (ABBREV_TAC eq)
    | _ => throw "ABBREVIATE_CARRYING_TAC: No carrying constructs") gl)

  let LSB_CARRY_RULE : thm → ExceptT String IO thm ← do
    let rules := (CONJUNCTS LSB_CARRYING).map (fun c => MATCH_MP c)
    pure (fun x => tryfindRule rules x)

  let XSB_CARRY_RULE : thm → ExceptT String IO thm ← do
    let rules := (CONJUNCTS XSB_CARRYING).map (fun c => MATCH_MP c)
    pure (fun x => tryfindRule rules x)

  let BIT_PUSH_CONV : ioconv ←
    GEN_REWRITE_CONV_NET TOP_DEPTH_CONV
     [BIT_WORD_OR, BIT_WORD_AND, BIT_WORD_XOR, BIT_WORD_NOT, BIT_WORD_0]

  let LSB_SIMP_CONV : ioconv ← do
    let m1 ← MESON [LE_1, DIMINDEX_NONZERO] (← q r"0 < dimindex(:N)")
    pure (BIT_PUSH_CONV THENC REWRITE_CONV [m1])

  let MSB_SIMP_CONV : ioconv ← do
    let t1 ← TAUT (← q r"(i + 1 < n ==> p) /\ (i + 1 < n ==> q) <=> (i + 1 < n ==> p /\ q)")
    let a2 ← ARITH_RULE (← q r"i + 1 < dimindex(:N) ==> i < dimindex(:N)")
    pure (BIT_PUSH_CONV THENC
      REWRITE_CONV [AND_FORALL_THM, t1] THENC
      SIMP_CONV [a2])

  let HORN_WORD_AUTO_TAC : tactic ← pure (
    REPEAT ABBREVIATE_CARRYING_TAC THEN
    DISCH_THEN (fun th => if is_eq (concl th) then ASSUME_TAC th else ALL_TAC) THEN
    TRY (GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
        CONV_TAC BIT_PUSH_CONV THEN SIMP_TAC []) THEN
    ASSUM_LIST (fun ths => tactic_of do
      pure (MP_TAC (← CONV_RULE MSB_SIMP_CONV (← end_itlist CONJ (← ths.mapM XSB_CARRY_RULE))))) THEN
    POP_ASSUM_LIST (fun ths => tactic_of do
      pure (MP_TAC (← CONV_RULE LSB_SIMP_CONV (← end_itlist CONJ (← ths.mapM LSB_CARRY_RULE))))) THEN
    WORD_AUTO_TRANSIFY_TAC THEN REACHABLE_STATE_TAC)

  /- --------------------------------------------------------------------- -/
  /- Turn clause into the special s = 0 ==> t = 0 Horn clause and call the -/
  /- basic Horn prover (use T ==> t = 0 or s = 0 ==> F if no neg/pos lits). -/
  /- --------------------------------------------------------------------- -/

  let CORE_WORD_AUTO_TAC : tactic ← do
    let true_tm ← q "T"
    let false_tm ← q "F"
    let DEIMP_CONV ← do
      let t1 ← TAUT (← q r"T ==> p <=> p")
      let t2 ← TAUT (← q r"p ==> F <=> ~p")
      let t3 ← TAUT (← q r"p ==> q <=> ~p \/ q")
      let c1 ← GEN_REWRITE_CONV_NET I [t1, t2]
      let c2 ← GEN_REWRITE_CONV_NET I [t3]
      let c3 ← GEN_REWRITE_CONV_NET TOP_SWEEP_CONV [DE_MORGAN_THM]
      pure ((c1 ORELSEC c2) THENC c3)
    let MERGE_CONV ← GEN_REWRITE_CONV_NET DEPTH_CONV [CONJ_WORD_EQ_0, DISJ_WORD_EQ_0]
    pure (fun gl => tactic_of (do
      let (_asl, w) := gl
      let (ndj, pdj) := partition is_neg (disjuncts w)
      let lcon ← if ndj == [] then pure true_tm
                 else liftExcept (HolCore.Bool.list_mk_conj (← liftExcept (ndj.mapM rand)))
      let rdis ← if pdj == [] then pure false_tm else liftExcept (HolCore.Bool.list_mk_disj pdj)
      let t ← liftExcept (HolCore.Bool.mk_imp lcon rdis)
      let th1 ← TRANS (← SYM (← ExceptT.mk (DEIMP_CONV t))) (← ExceptT.mk (MERGE_CONV t))
      let mkeq ← ExceptT.mk mk_eq
      let eqw ← liftExcept (mkeq (w, (← liftExcept (lhand (concl th1)))))
      let th2 ← TRANS (← D.DISJ_ACI_RULE eqw) th1
      pure (CONV_TAC (fun _ => pure (.ok th2)) THEN HORN_WORD_AUTO_TAC)) gl)

  -- @@RETURN BEGIN
  return { WORD_AUTO_TRANSIFY_TAC, LSB_CARRYING, XSB_CARRYING, ABBREVIATE_SHR_TAC,
           ABBREVIATE_CARRYING_TAC, LSB_CARRY_RULE, XSB_CARRY_RULE, BIT_PUSH_CONV,
           LSB_SIMP_CONV, MSB_SIMP_CONV, HORN_WORD_AUTO_TAC, CORE_WORD_AUTO_TAC }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Overall: prenormalize and split up then call the basic tactic.            -/
/- ------------------------------------------------------------------------- -/

/-- `is_intmin tm` of CHARACTERIZE_INT_MIN_TAC (word_automata.ml). -/
private def is_intmin (tm : term) : Bool :=
  match tm with
  | .Const "word_INT_MIN" _ => true
  | _ => false

structure Overall where
  -- @@FIELDS
  WORD_MUL_SHLADD : thm
  CHARACTERIZE_INT_MIN_TAC : tactic
  PURE_WORD_AUTO_TAC : tactic
  PURE_WORD_AUTO_RULE : term → ExceptT String IO thm
  WORD_AUTO_TAC : tactic
  WORD_AUTO_RULE : term → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupOverall [HolBase] (D : WordAutomataDeps) (BShifts : Shifts) (BIneq : Ineq) (BHorn : Horn) :
    ExceptT String IO Overall := do
  -- @@SCOPE BEGIN
  let { BITBLAST_RULE, BITBLAST_TAC, CNF_CONV, NNFC_CONV, NUM_RED_CONV, PRENEX_CONV,
        WORD_RED_CONV, WORD_RULE, .. } := D
  let { BITVAL_CLAUSES, GE, GT, INT_GE, INT_GT, INT_NOT_LT, NOT_LT, WORD_AND_0,
        WORD_MUL_0, WORD_OR_0, .. } := D.core1
  let { WORD_XOR_0, WORD_XOR_EQ_0, irelational2, relational2, word_ige, word_igt,
        word_ile, word_ilt, word_ugt, word_ule, word_ult, .. } := D.core2
  let { DEFINE_WORD_INT_MIN, EXPAND_SHIFT_CONV, WORD_ISHR_SHLADD, WORD_NUMERAL_SHLADD,
        WORD_SHLADD, WORD_SHLADD_0, WORD_USHR_SHLADD, .. } := BShifts
  let { IVAL_LT_0_ELIM_THM, IVAL_LT_ELIM_THM, VAL_LT_ELIM_THM, .. } := BIneq
  let { ABBREVIATE_SHR_TAC, CORE_WORD_AUTO_TAC, .. } := BHorn
  -- @@SCOPE END

  let WORD_MUL_SHLADD ← prove
   r"!x y:N word.
    word_mul (word_shladd x T) y = word_add (word_shladd (word_mul x y) F) y /\
    word_mul y (word_shladd x T) = word_add (word_shladd (word_mul y x) F) y /\
    word_mul (word_shladd x F) y = word_shladd (word_mul x y) F /\
    word_mul y (word_shladd x F) = word_shladd (word_mul y x) F"
   (REWRITE_TAC [WORD_SHLADD, BITVAL_CLAUSES] THEN CONV_TAC WORD_RULE)

  let CHARACTERIZE_INT_MIN_TAC : tactic ← do
    let n_ty ← qty "N"
    pure (fun gl => tactic_of (do
      let (_asl, w) := gl
      let tms := find_terms is_intmin w
      pure (MAP_EVERY (fun tm => tactic_of do
        let (_, args) ← liftExcept (dest_type (type_of tm))
        let ty := args.head!
        pure (MP_TAC (← HolLight.INST_TYPE [(ty, n_ty)] DEFINE_WORD_INT_MIN) THEN
         SPEC_TAC (tm, (← genvar (type_of tm))) THEN GEN_TAC)) tms)) gl)

  let PURE_WORD_AUTO_TAC : tactic ← pure (
    CONV_TAC (DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV)) THEN
    REWRITE_TAC [word_ile, word_ilt, word_ige, word_igt, irelational2,
                word_ule, word_ult, word_ige, word_ugt, relational2,
                INT_GT, INT_GE, ← GSYM INT_NOT_LT, GT, GE, ← GSYM NOT_LT,
                VAL_LT_ELIM_THM, IVAL_LT_ELIM_THM, IVAL_LT_0_ELIM_THM] THEN
    GEN_REWRITE_TAC TOP_DEPTH_CONV [WORD_NUMERAL_SHLADD] THEN
    GEN_REWRITE_TAC TOP_DEPTH_CONV [WORD_MUL_SHLADD, WORD_MUL_0] THEN
    CONV_TAC NNFC_CONV THEN CONV_TAC PRENEX_CONV THEN REPEAT GEN_TAC THEN
    CONV_TAC (DEPTH_CONV EXPAND_SHIFT_CONV) THEN
    REPEAT ABBREVIATE_SHR_TAC THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I
     [WORD_USHR_SHLADD, WORD_ISHR_SHLADD])) THEN
    CHARACTERIZE_INT_MIN_TAC THEN
    CONV_TAC NNFC_CONV THEN
    CONV_TAC CNF_CONV THEN REPEAT CONJ_TAC THEN
    GEN_REWRITE_TAC DEPTH_CONV [← GSYM WORD_SHLADD_0] THEN
    GEN_REWRITE_TAC ONCE_DEPTH_CONV [← GSYM WORD_XOR_EQ_0] THEN
    GEN_REWRITE_TAC DEPTH_CONV [WORD_XOR_0, WORD_AND_0, WORD_OR_0] THEN
    CORE_WORD_AUTO_TAC)

  let PURE_WORD_AUTO_RULE : term → ExceptT String IO thm ← pure (fun tm =>
    ExceptT.mk (Tactics.prove HolBase.B tm PURE_WORD_AUTO_TAC))

  /- --------------------------------------------------------------------- -/
  /- Version with an initial sanity check on specific size 4 when there    -/
  /- is a single type variable, and defaulting to trying bit-blasting      -/
  /- first for the case of no type variables.                              -/
  /- --------------------------------------------------------------------- -/

  let WORD_AUTO_TAC : tactic ← do
    let nty ← qty "4"
    pure (fun gl => tactic_of (do
      let (_asl, w) := gl
      match type_vars_in_term w with
      | [] => pure (BITBLAST_TAC ORELSE PURE_WORD_AUTO_TAC)
      | [n] => do
          let w' := inst [(nty, n)] w
          let ok ← tryCatch
            (do pure (concl (← BITBLAST_RULE w') == w'))
            (fun _ => pure false)
          if ok then do
            let _ ← (remark "Sanity check for size 4 OK" : IO Unit)
            pure PURE_WORD_AUTO_TAC
          else throw "WORD_AUTO_TAC: Sanity check for size 4 failed!"
      | _ => throw "WORD_AUTO_TAC: Multiple generic types not supported") gl)

  let WORD_AUTO_RULE : term → ExceptT String IO thm ← pure (fun tm =>
    ExceptT.mk (Tactics.prove HolBase.B tm WORD_AUTO_TAC))

  -- @@RETURN BEGIN
  return { WORD_MUL_SHLADD, CHARACTERIZE_INT_MIN_TAC, PURE_WORD_AUTO_TAC,
           PURE_WORD_AUTO_RULE, WORD_AUTO_TAC, WORD_AUTO_RULE }
  -- @@RETURN END

end HolLibrary.WordAutomata
