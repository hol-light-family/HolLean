/- File: Canon.lean
Reasonably efficient conversions for various canonical forms (`canon.ml`).
Original       John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026 -/

import HolCore.Bool
import HolCore.Equal
import HolCore.Drule
import HolCore.Tactics
import HolCore.Itab
import HolCore.Simp
import HolCore.Parser
import HolCore.Theorems
import HolCore.IndDefs
import HolCore.Classic
import HolCore.Trivia

open HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Bool HolCore.Equal
     HolCore.Drule HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Parser
     HolCore.Theorems HolCore.IndDefs HolCore.Classic HolCore.Trivia

namespace HolCore.Canon

set_option maxRecDepth 4000

/-- Build-and-apply a `GEN_REWRITE_CONV cnvl thl` as a single `ioconv`. -/
def genRewrite (B : BoolThms) (cnvl : ioconv → ioconv) (thl : List thm) : ioconv :=
  fun tm => do
    match ← (Simp.GEN_REWRITE_CONV B cnvl thl : IO (Except String ioconv)) with
    | .error e => return .error e
    | .ok c => (c tm : IO (Except String thm))

/- ---------------------------------------------------------------------- -/
/- Pre-simplification.                                                    -/
/- ---------------------------------------------------------------------- -/

/-- Pre-simplification conversion. -/
def PRESIMP_CONV (B : BoolThms) (T : TheoremThms) (C : ClassThms) : ioconv :=
  genRewrite B Simp.topDepthConvIO
    [C.NOT_CLAUSES, T.AND_CLAUSES, T.OR_CLAUSES, T.IMP_CLAUSES, T.EQ_CLAUSES,
     T.FORALL_SIMP, T.EXISTS_SIMP, T.EXISTS_OR_THM, T.FORALL_AND_THM,
     T.LEFT_EXISTS_AND_THM, T.RIGHT_EXISTS_AND_THM,
     C.LEFT_FORALL_OR_THM, C.RIGHT_FORALL_OR_THM]

/- ---------------------------------------------------------------------- -/
/- ACI rearrangements of conjunctions and disjunctions. This is much      -/
/- faster than AC xxx_ACI on large problems, as well as being more        -/
/- controlled.                                                            -/
/- ---------------------------------------------------------------------- -/

/-- Build a term→thm finite map from a conjunctive theorem's leaves. -/
private partial def conjMkFun (B : BoolThms) (th : thm) (fn : Func term thm) :
    Except String (Func term thm) := do
  let tm := concl th
  if Basics.is_conj tm then do
    let (th1, th2) ← B.CONJ_PAIR th
    conjMkFun B th1 (← conjMkFun B th2 fn)
  else return ((tm |-> th) fn)

/-- Reassemble a conjunction from the finite map. -/
private partial def conjUseFun (B : BoolThms) (fn : Func term thm) (tm : term) :
    Except String thm := do
  if Basics.is_conj tm then do
    let (l, r) ← Basics.dest_conj tm
    B.CONJ (← conjUseFun B fn l) (← conjUseFun B fn r)
  else apply fn tm

/-- `CONJ_ACI_RULE fm`: prove an AC-rearrangement equation between two
    conjunctions (fast, controlled alternative to `AC CONJ_ACI`). -/
def CONJ_ACI_RULE (B : BoolThms) (fm : term) : Except String thm := do
  let (p, p') ← dest_eq fm
  if p == p' then return (REFL p)
  else
    let th ← conjUseFun B (← conjMkFun B (← ASSUME p) undefined) p'
    let th' ← conjUseFun B (← conjMkFun B (← ASSUME p') undefined) p
    B.IMP_ANTISYM_RULE (← DISCH_ALL B.DISCH th) (← DISCH_ALL B.DISCH th')

/-- `~(a\/b)==>~a` / `~(a\/b)==>~b` split of a negated-disjunction theorem. -/
private def notDisjPair (_B : BoolThms) (pthLeft pthRight : thm) (aTm bTm : term) (th : thm) :
    Except String (thm × thm) := do
  let (p, q) ← Basics.dest_disj (← rand (concl th))
  let ilist := [(p, aTm), (q, bTm)]
  let l ← PROVE_HYP th (← INST ilist pthLeft)
  let r ← PROVE_HYP th (← INST ilist pthRight)
  return (l, r)

/-- Combine `~a` and `~b` theorems into `~(a\/b)`. -/
private def notDisj (_B : BoolThms) (pth : thm) (aTm bTm : term) (th1 th2 : thm) :
    Except String thm := do
  let th3 ← INST [((← rand (concl th1)), aTm), ((← rand (concl th2)), bTm)] pth
  PROVE_HYP th1 (← PROVE_HYP th2 th3)

private partial def disjMkFun (B : BoolThms) (pthLeft pthRight : thm) (aTm bTm : term)
    (th : thm) (fn : Func term thm) : Except String (Func term thm) := do
  let tm ← rand (concl th)
  if Basics.is_disj tm then do
    let (th1, th2) ← notDisjPair B pthLeft pthRight aTm bTm th
    disjMkFun B pthLeft pthRight aTm bTm th1 (← disjMkFun B pthLeft pthRight aTm bTm th2 fn)
  else return ((tm |-> th) fn)

private partial def disjUseFun (B : BoolThms) (pth : thm) (aTm bTm : term)
    (fn : Func term thm) (tm : term) : Except String thm := do
  if Basics.is_disj tm then do
    let (l, r) ← Basics.dest_disj tm
    notDisj B pth aTm bTm (← disjUseFun B pth aTm bTm fn l) (← disjUseFun B pth aTm bTm fn r)
  else apply fn tm

/-- `DISJ_ACI_RULE fm`: dual of `CONJ_ACI_RULE` for disjunctions.
    `pthLeft = ~(a\/b)==>~a`, `pthRight = ~(a\/b)==>~b`,
    `pth = ~a==>~b==>~(a\/b)` (both UNDISCHed), `pthNeg = (~a<=>~b)==>(a<=>b)`. -/
def DISJ_ACI_RULE (B : BoolThms) (pthLeft pthRight pth pthNeg : thm) (aTm bTm : term)
    (fm : term) : Except String thm := do
  let (p, p') ← dest_eq fm
  if p == p' then return (REFL p)
  else
    let th ← disjUseFun B pth aTm bTm (← disjMkFun B pthLeft pthRight aTm bTm (← ASSUME (← mk_neg p)) undefined) p'
    let th' ← disjUseFun B pth aTm bTm (← disjMkFun B pthLeft pthRight aTm bTm (← ASSUME (← mk_neg p')) undefined) p
    let th1 ← B.IMP_ANTISYM_RULE (← DISCH_ALL B.DISCH th) (← DISCH_ALL B.DISCH th')
    PROVE_HYP th1 (← INST [(p, aTm), (p', bTm)] pthNeg)

/- ---------------------------------------------------------------------- -/
/- Order canonically, right-associate and remove duplicates.              -/
/- ---------------------------------------------------------------------- -/

/-- Order canonically, right-associate and remove duplicates (conjunction). -/
def CONJ_CANON_CONV (B : BoolThms) : ioconv := fun tm => do
  match ← (mk_eq : IO (Except String ((term × term) → Except String term))) with
  | .error e => return .error e
  | .ok mkEq =>
    return (do
      let tm' ← list_mk_conj (setify (conjuncts tm))
      CONJ_ACI_RULE B (← mkEq (tm, tm')))

/-- Order canonically, right-associate and remove duplicates (disjunction). -/
def DISJ_CANON_CONV (B : BoolThms) (pthLeft pthRight pth pthNeg : thm) (aTm bTm : term) :
    ioconv := fun tm => do
  match ← (mk_eq : IO (Except String ((term × term) → Except String term))) with
  | .error e => return .error e
  | .ok mkEq =>
    return (do
      let tm' ← list_mk_disj (setify (disjuncts tm))
      DISJ_ACI_RULE B pthLeft pthRight pth pthNeg aTm bTm (← mkEq (tm, tm')))

/- ---------------------------------------------------------------------- -/
/- General NNF conversion. The user supplies some conversion to be        -/
/- applied to atomic formulas.                                            -/
/-                                                                        -/
/- "Iff"s are split conjunctively or disjunctively according to the flag  -/
/- argument (conjuctively = true) until a universal quantifier (modulo    -/
/- current parity) is passed; after that they are split conjunctively.    -/
/- This is appropriate when the result is passed to a disjunctive         -/
/- splitter followed by a clausal form inner core, such as MESON.         -/
/-                                                                        -/
/- To avoid some duplicate computation, this function will in general     -/
/- enter a recursion where it simultaneously computes NNF representations -/
/- for "p" and "~p", so the user needs to supply an atomic "conversion"   -/
/- that does the same.                                                    -/
/- ---------------------------------------------------------------------- -/

/-- The auxiliary `pth`s + constant terms for `GEN_NNF_CONV`, proved once. -/
structure NNFPths where
  and_tm : term
  or_tm  : term
  not_tm : term
  p_tm   : term
  q_tm   : term
  pth_not_not : thm
  pth_not_and : thm
  pth_not_or  : thm
  pth_imp     : thm
  pth_not_imp : thm
  pth_eq      : thm
  pth_not_eq  : thm
  pth_eq'     : thm
  pth_not_eq' : thm
  pth_not_forall : thm
  pth_not_exists : thm
  pth_not_exu    : thm
  pth_exu        : thm
  deriving Inhabited

/-- Prove the `GEN_NNF_CONV` auxiliary theorems. `ETA_AX` passed in. -/
def setupNNFPths (B : BoolThms) (T : TheoremThms) (C : ClassThms) (ETA_AX : thm) :
    ExceptT String IO NNFPths := do
  let TAUT (s : String) : ExceptT String IO thm := do
    (Classic.TAUT B C.BOOL_CASES_AX (← parse_term s) : IO (Except String thm))
  let prove := Tactics.prove B
  let GEN_REWRITE_TAC := Simp.GEN_REWRITE_TAC B
  let REWRITE_TAC := Simp.REWRITE_TAC B
  let and_tm ← parse_term "(/\\)"
  let or_tm ← parse_term "(\\/)"
  let not_tm ← parse_term "(~)"
  let p_tm ← parse_term "p:bool"
  let q_tm ← parse_term "q:bool"
  let pth_not_not ← TAUT "~ ~ p = p"
  let pth_not_and ← TAUT "~(p /\\ q) <=> ~p \\/ ~q"
  let pth_not_or  ← TAUT "~(p \\/ q) <=> ~p /\\ ~q"
  let pth_imp     ← TAUT "p ==> q <=> ~p \\/ q"
  let pth_not_imp ← TAUT "~(p ==> q) <=> p /\\ ~q"
  let pth_eq      ← TAUT "(p <=> q) <=> p /\\ q \\/ ~p /\\ ~q"
  let pth_not_eq  ← TAUT "~(p <=> q) <=> p /\\ ~q \\/ ~p /\\ q"
  let pth_eq'     ← TAUT "(p <=> q) <=> (p \\/ ~q) /\\ (~p \\/ q)"
  let pth_not_eq' ← TAUT "~(p <=> q) <=> (p \\/ q) /\\ (~p \\/ ~q)"
  -- [pth_not_forall; pth_not_exists; pth_not_exu] = CONJUNCTS (prove ...)
  let landFunpow2Rand : ioconv → ioconv := fun c => Simp.landConvIO (Simp.randConvIO (Simp.randConvIO c))
  let notQuantThm ← (prove (← parse_term
      "(~((!) P) <=> ?x:A. ~(P x)) /\\ (~((?) P) <=> !x:A. ~(P x)) /\\ (~((?!) P) <=> (!x:A. ~(P x)) \\/ ?x y. P x /\\ P y /\\ ~(y = x))")
      (THEN B (REPEAT B (Tactics.CONJ_TAC B))
        (THEN B (GEN_REWRITE_TAC landFunpow2Rand [(← liftExcept (GSYM ETA_AX))])
          (THEN B (REWRITE_TAC [C.NOT_EXISTS_THM, C.NOT_FORALL_THM, B.EXISTS_UNIQUE_DEF,
                                C.DE_MORGAN_THM, C.NOT_IMP])
            (REWRITE_TAC [T.CONJ_ASSOC, T.EQ_SYM_EQ])))) : IO (Except String thm))
  let notQuants := B.CONJUNCTS notQuantThm
  let pth_not_forall ← liftExcept (match notQuants with | a :: _ => .ok a | _ => .error "pth_not_forall")
  let pth_not_exists ← liftExcept (match notQuants with | _ :: a :: _ => .ok a | _ => .error "pth_not_exists")
  let pth_not_exu ← liftExcept (match notQuants with | _ :: _ :: a :: _ => .ok a | _ => .error "pth_not_exu")
  let aOrLemma ← TAUT "a /\\ b ==> c <=> ~a \\/ ~b \\/ c"
  let landRand : ioconv → ioconv := fun c => Simp.landConvIO (Simp.randConvIO c)
  let pth_exu ← (prove (← parse_term
      "((?!) P) <=> (?x:A. P x) /\\ !x y. ~(P x) \\/ ~(P y) \\/ (y = x)")
      (THEN B (GEN_REWRITE_TAC landRand [(← liftExcept (GSYM ETA_AX))])
        (THEN B (REWRITE_TAC [B.EXISTS_UNIQUE_DEF, aOrLemma])
          (REWRITE_TAC [T.EQ_SYM_EQ]))) : IO (Except String thm))
  return { and_tm, or_tm, not_tm, p_tm, q_tm,
           pth_not_not, pth_not_and, pth_not_or, pth_imp, pth_not_imp,
           pth_eq, pth_not_eq, pth_eq', pth_not_eq',
           pth_not_forall, pth_not_exists, pth_not_exu, pth_exu }

/-- A "dual" NNF conversion: given a term, return `(|- t = t+, |- ~t = t-)`. -/
abbrev dconv := term → IO (Except String (thm × thm))

/-- Extract the domain type `ty` of a quantifier body `Abs x t` from the
    quantifier constant's type `(A->bool)->bool` etc. -/
private def binderDomTy (q : term) : Except String hol_type := do
  match type_of q with
  | .Tyapp "fun" [.Tyapp "fun" (ty :: _), _] => .ok ty
  | _ => .error "binderDomTy"

/-- `mk_fun_ty ty bool` (IO). -/
private def mk_fun_ty' (ty : hol_type) : IO (Except String hol_type) := mk_fun_ty ty bool_ty

/-- Build the equation `l = r` (IO, via the `=` constant). -/
def mkEq2 (l r : term) : IO (Except String term) := do
  match ← (mk_eq : IO (Except String ((term × term) → Except String term))) with
  | .error e => return .error e | .ok f => return (f (l, r))

mutual
/-- Simultaneously compute NNF of `t` and `~t` (splitting iffs). -/
partial def nnfDconv (B : BoolThms) (P : NNFPths) (cf : Bool) (baseconvs : dconv)
    (tm : term) : IO (Except String (thm × thm)) := do
  match tm with
  | .Comb (.Comb (.Const "/\\" _) l) r =>
      match ← (nnfDconv B P cf baseconvs l : IO (Except String (thm × thm))) with
      | .error e => return .error e
      | .ok (th_lp, th_ln) =>
      match ← (nnfDconv B P cf baseconvs r : IO (Except String (thm × thm))) with
      | .error e => return .error e
      | .ok (th_rp, th_rn) =>
        return (do
          let pos ← MK_COMB (← AP_TERM P.and_tm th_lp) th_rp
          let neg ← TRANS (← INST [(l, P.p_tm), (r, P.q_tm)] P.pth_not_and)
                          (← MK_COMB (← AP_TERM P.or_tm th_ln) th_rn)
          pure (pos, neg))
  | .Comb (.Comb (.Const "\\/" _) l) r =>
      match ← (nnfDconv B P cf baseconvs l : IO (Except String (thm × thm))) with
      | .error e => return .error e
      | .ok (th_lp, th_ln) =>
      match ← (nnfDconv B P cf baseconvs r : IO (Except String (thm × thm))) with
      | .error e => return .error e
      | .ok (th_rp, th_rn) =>
        return (do
          let pos ← MK_COMB (← AP_TERM P.or_tm th_lp) th_rp
          let neg ← TRANS (← INST [(l, P.p_tm), (r, P.q_tm)] P.pth_not_or)
                          (← MK_COMB (← AP_TERM P.and_tm th_ln) th_rn)
          pure (pos, neg))
  | .Comb (.Comb (.Const "==>" _) l) r =>
      match ← (nnfDconv B P cf baseconvs l : IO (Except String (thm × thm))) with
      | .error e => return .error e
      | .ok (th_lp, th_ln) =>
      match ← (nnfDconv B P cf baseconvs r : IO (Except String (thm × thm))) with
      | .error e => return .error e
      | .ok (th_rp, th_rn) =>
        return (do
          let pos ← TRANS (← INST [(l, P.p_tm), (r, P.q_tm)] P.pth_imp)
                          (← MK_COMB (← AP_TERM P.or_tm th_ln) th_rp)
          let neg ← TRANS (← INST [(l, P.p_tm), (r, P.q_tm)] P.pth_not_imp)
                          (← MK_COMB (← AP_TERM P.and_tm th_lp) th_rn)
          pure (pos, neg))
  | .Comb (.Comb (.Const "=" (.Tyapp "fun" (.Tyapp "bool" _ :: _))) l) r =>
      match ← (nnfDconv B P cf baseconvs l : IO (Except String (thm × thm))) with
      | .error e => return .error e
      | .ok (th_lp, th_ln) =>
      match ← (nnfDconv B P cf baseconvs r : IO (Except String (thm × thm))) with
      | .error e => return .error e
      | .ok (th_rp, th_rn) =>
        if cf then
          return (do
            let pos ← TRANS (← INST [(l, P.p_tm), (r, P.q_tm)] P.pth_eq')
                        (← MK_COMB (← AP_TERM P.and_tm (← MK_COMB (← AP_TERM P.or_tm th_lp) th_rn))
                                   (← MK_COMB (← AP_TERM P.or_tm th_ln) th_rp))
            let neg ← TRANS (← INST [(l, P.p_tm), (r, P.q_tm)] P.pth_not_eq')
                        (← MK_COMB (← AP_TERM P.and_tm (← MK_COMB (← AP_TERM P.or_tm th_lp) th_rp))
                                   (← MK_COMB (← AP_TERM P.or_tm th_ln) th_rn))
            pure (pos, neg))
        else
          return (do
            let pos ← TRANS (← INST [(l, P.p_tm), (r, P.q_tm)] P.pth_eq)
                        (← MK_COMB (← AP_TERM P.or_tm (← MK_COMB (← AP_TERM P.and_tm th_lp) th_rp))
                                   (← MK_COMB (← AP_TERM P.and_tm th_ln) th_rn))
            let neg ← TRANS (← INST [(l, P.p_tm), (r, P.q_tm)] P.pth_not_eq)
                        (← MK_COMB (← AP_TERM P.or_tm (← MK_COMB (← AP_TERM P.and_tm th_lp) th_rn))
                                   (← MK_COMB (← AP_TERM P.and_tm th_ln) th_rp))
            pure (pos, neg))
  | .Comb (.Const "!" qty) (.Abs x t) =>
      let q := term.Const "!" qty
      let bod := term.Abs x t
      match binderDomTy q with
      | .error e => return .error e
      | .ok ty =>
      match ← (nnfDconv B P true baseconvs t : IO (Except String (thm × thm))) with
      | .error e => return .error e
      | .ok (th_p, th_n) =>
        return (← (do
          let pos ← liftExcept (do AP_TERM q (← ABS x th_p))
          let Pty := mk_var "P" (← (mk_fun_ty' ty : IO (Except String hol_type)))
          let th1 ← liftExcept (do INST [(bod, Pty)] (← INST_TYPE [(ty, aty)] P.pth_not_forall))
          let bx ← liftExcept (mk_comb bod x)
          let th2 ← liftExcept (do TRANS (← AP_TERM P.not_tm (← BETA bx)) th_n)
          let mex ← (MK_EXISTS x th2 : IO (Except String thm))
          let neg ← liftExcept (TRANS th1 mex)
          pure (pos, neg) : ExceptT String IO (thm × thm)).run)
  | .Comb (.Const "?" qty) (.Abs x t) =>
      let q := term.Const "?" qty
      let bod := term.Abs x t
      match binderDomTy q with
      | .error e => return .error e
      | .ok ty =>
      match ← (nnfDconv B P cf baseconvs t : IO (Except String (thm × thm))) with
      | .error e => return .error e
      | .ok (th_p, th_n) =>
        return (← (do
          let pos ← liftExcept (do AP_TERM q (← ABS x th_p))
          let Pty := mk_var "P" (← (mk_fun_ty' ty : IO (Except String hol_type)))
          let th1 ← liftExcept (do INST [(bod, Pty)] (← INST_TYPE [(ty, aty)] P.pth_not_exists))
          let bx ← liftExcept (mk_comb bod x)
          let th2 ← liftExcept (do TRANS (← AP_TERM P.not_tm (← BETA bx)) th_n)
          let mfa ← (MK_FORALL x th2 : IO (Except String thm))
          let neg ← liftExcept (TRANS th1 mfa)
          pure (pos, neg) : ExceptT String IO (thm × thm)).run)
  | .Comb (.Const "?!" qty) (.Abs x t) =>
      let q := term.Const "?!" qty
      let bod := term.Abs x t
      match binderDomTy q with
      | .error e => return .error e
      | .ok ty =>
      match ← (nnfDconv B P cf baseconvs t : IO (Except String (thm × thm))) with
      | .error e => return .error e
      | .ok (th_p, th_n) =>
        return (← (do
          let y ← liftExcept (variant (x :: frees t) x)
          let eq ← (mkEq2 y x : IO (Except String term))
          let (eth_p, eth_n) ← (baseconvs eq : IO (Except String (thm × thm)))
          let bth ← liftExcept (do BETA (← mk_comb bod x))
          let bth' ← liftExcept (do BETA_CONV (← mk_comb bod y))
          let th_p' ← liftExcept (INST [(y, x)] th_p)
          let th_n' ← liftExcept (INST [(y, x)] th_n)
          let Pty := mk_var "P" (← (mk_fun_ty' ty : IO (Except String hol_type)))
          let th1 ← liftExcept (do INST [(bod, Pty)] (← INST_TYPE [(ty, aty)] P.pth_exu))
          let th1' ← liftExcept (do INST [(bod, Pty)] (← INST_TYPE [(ty, aty)] P.pth_not_exu))
          -- th2 (positive)
          let ex_p ← (MK_EXISTS x (← liftExcept (TRANS bth th_p)) : IO (Except String thm))
          -- `pth_exu` is `!x y. ~(P x) \/ ~(P y) \/ (y = x)`, so in `th2` the
          -- UNPRIMED (`x`) disjunct is OUTERMOST and the PRIMED (`y`) one nests
          -- inside it, exactly as canon.ml 202-207 builds it.  THESE TWO WERE
          -- TRANSPOSED, which made `TRANS th1 th2` fail with `TRANS` for the
          -- POSITIVE `?!` form only.  That is why `?!` worked under `==>` (which
          -- needs just the negative form, built correctly in `th2'` below) but
          -- failed under `<=>`, which needs BOTH - the symptom that surfaced as
          -- sets.ml's SING_ALT killing setupSetsMisc.  The sibling `?!` branch
          -- further down had it right, which is what pinned the intended form.
          let inner2 ← liftExcept (do
            MK_COMB (← AP_TERM P.or_tm (← TRANS (← AP_TERM P.not_tm bth') th_n')) eth_p)
          let innerR ← liftExcept (do
            MK_COMB (← AP_TERM P.or_tm (← TRANS (← AP_TERM P.not_tm bth) th_n)) inner2)
          let fa_y ← (MK_FORALL y innerR : IO (Except String thm))
          let fa_xy ← (MK_FORALL x fa_y : IO (Except String thm))
          let th2 ← liftExcept (do MK_COMB (← AP_TERM P.and_tm ex_p) fa_xy)
          -- th2' (negative)
          let fa_n ← (MK_FORALL x (← liftExcept (TRANS (← AP_TERM P.not_tm bth) th_n)) : IO (Except String thm))
          let inner2' ← liftExcept (do
            MK_COMB (← AP_TERM P.and_tm (← TRANS bth' th_p')) eth_n)
          let innerR' ← liftExcept (do
            MK_COMB (← AP_TERM P.and_tm (← TRANS bth th_p)) inner2')
          let ex_y ← (MK_EXISTS y innerR' : IO (Except String thm))
          let ex_xy ← (MK_EXISTS x ex_y : IO (Except String thm))
          let th2' ← liftExcept (do MK_COMB (← AP_TERM P.or_tm fa_n) ex_xy)
          let pos ← liftExcept (TRANS th1 th2)
          let neg ← liftExcept (TRANS th1' th2')
          pure (pos, neg) : ExceptT String IO (thm × thm)).run)
  | .Comb (.Const "~" _) t =>
      match ← (nnfDconv B P cf baseconvs t : IO (Except String (thm × thm))) with
      | .error e => return .error e
      | .ok (th1, th2) =>
        return ((do
          let n ← TRANS (← INST [(t, P.p_tm)] P.pth_not_not) th1
          pure (th2, n)) : Except String (thm × thm))
  | _ =>
      match ← (baseconvs tm : IO (Except String (thm × thm))) with
      | .ok r => return .ok r
      | .error _ => return ((do pure (REFL tm, REFL (← mk_neg tm))) : Except String (thm × thm))

/-- Positive-position NNF conversion. `baseconvs = (base1, base2)`. -/
partial def nnfConvP (B : BoolThms) (P : NNFPths) (cf : Bool)
    (base1 : ioconv) (base2 : dconv) (tm : term) : IO (Except String thm) := do
  match tm with
  | .Comb (.Comb (.Const "/\\" _) l) r =>
      match ← (nnfConvP B P cf base1 base2 l : IO (Except String thm)) with
      | .error e => return .error e | .ok th_lp =>
      match ← (nnfConvP B P cf base1 base2 r : IO (Except String thm)) with
      | .error e => return .error e | .ok th_rp =>
        return (do MK_COMB (← AP_TERM P.and_tm th_lp) th_rp)
  | .Comb (.Comb (.Const "\\/" _) l) r =>
      match ← (nnfConvP B P cf base1 base2 l : IO (Except String thm)) with
      | .error e => return .error e | .ok th_lp =>
      match ← (nnfConvP B P cf base1 base2 r : IO (Except String thm)) with
      | .error e => return .error e | .ok th_rp =>
        return (do MK_COMB (← AP_TERM P.or_tm th_lp) th_rp)
  | .Comb (.Comb (.Const "==>" _) l) r =>
      match ← (nnfConvN B P cf base1 base2 l : IO (Except String thm)) with
      | .error e => return .error e | .ok th_ln =>
      match ← (nnfConvP B P cf base1 base2 r : IO (Except String thm)) with
      | .error e => return .error e | .ok th_rp =>
        return (do TRANS (← INST [(l, P.p_tm), (r, P.q_tm)] P.pth_imp)
                         (← MK_COMB (← AP_TERM P.or_tm th_ln) th_rp))
  | .Comb (.Comb (.Const "=" (.Tyapp "fun" (.Tyapp "bool" _ :: _))) l) r =>
      match ← (nnfDconv B P cf base2 l : IO (Except String (thm × thm))) with
      | .error e => return .error e | .ok (th_lp, th_ln) =>
      match ← (nnfDconv B P cf base2 r : IO (Except String (thm × thm))) with
      | .error e => return .error e | .ok (th_rp, th_rn) =>
        if cf then
          return (do TRANS (← INST [(l, P.p_tm), (r, P.q_tm)] P.pth_eq')
                       (← MK_COMB (← AP_TERM P.and_tm (← MK_COMB (← AP_TERM P.or_tm th_lp) th_rn))
                                  (← MK_COMB (← AP_TERM P.or_tm th_ln) th_rp)))
        else
          return (do TRANS (← INST [(l, P.p_tm), (r, P.q_tm)] P.pth_eq)
                       (← MK_COMB (← AP_TERM P.or_tm (← MK_COMB (← AP_TERM P.and_tm th_lp) th_rp))
                                  (← MK_COMB (← AP_TERM P.and_tm th_ln) th_rn)))
  | .Comb (.Const "!" qty) (.Abs x t) =>
      let q := term.Const "!" qty
      match ← (nnfConvP B P true base1 base2 t : IO (Except String thm)) with
      | .error e => return .error e | .ok th_p => return (do AP_TERM q (← ABS x th_p))
  | .Comb (.Const "?" qty) (.Abs x t) =>
      let q := term.Const "?" qty
      match ← (nnfConvP B P cf base1 base2 t : IO (Except String thm)) with
      | .error e => return .error e | .ok th_p => return (do AP_TERM q (← ABS x th_p))
  | .Comb (.Const "?!" qty) (.Abs x t) =>
      let bod := term.Abs x t
      match binderDomTy (term.Const "?!" qty) with
      | .error e => return .error e | .ok ty =>
      match ← (nnfDconv B P cf base2 t : IO (Except String (thm × thm))) with
      | .error e => return .error e | .ok (th_p, th_n) =>
        return (← (do
          let y ← liftExcept (variant (x :: frees t) x)
          let eq ← (mkEq2 y x : IO (Except String term))
          let (eth_p, _eth_n) ← (base2 eq : IO (Except String (thm × thm)))
          let bth ← liftExcept (do BETA (← mk_comb bod x))
          let bth' ← liftExcept (do BETA_CONV (← mk_comb bod y))
          let th_n' ← liftExcept (INST [(y, x)] th_n)
          let Pty := mk_var "P" (← (mk_fun_ty' ty : IO (Except String hol_type)))
          let th1 ← liftExcept (do INST [(bod, Pty)] (← INST_TYPE [(ty, aty)] P.pth_exu))
          let ex_p ← (MK_EXISTS x (← liftExcept (TRANS bth th_p)) : IO (Except String thm))
          let inner2 ← liftExcept (do
            MK_COMB (← AP_TERM P.or_tm (← TRANS (← AP_TERM P.not_tm bth') th_n')) eth_p)
          let innerR ← liftExcept (do
            MK_COMB (← AP_TERM P.or_tm (← TRANS (← AP_TERM P.not_tm bth) th_n)) inner2)
          let fa_y ← (MK_FORALL y innerR : IO (Except String thm))
          let fa_xy ← (MK_FORALL x fa_y : IO (Except String thm))
          let th2 ← liftExcept (do MK_COMB (← AP_TERM P.and_tm ex_p) fa_xy)
          liftExcept (TRANS th1 th2) : ExceptT String IO thm).run)
  | .Comb (.Const "~" _) t => (nnfConvN B P cf base1 base2 t : IO (Except String thm))
  | _ =>
      match ← (base1 tm : IO (Except String thm)) with
      | .ok r => return .ok r | .error _ => return (.ok (REFL tm))

/-- Negative-position NNF conversion (NNF of `~tm`). -/
partial def nnfConvN (B : BoolThms) (P : NNFPths) (cf : Bool)
    (base1 : ioconv) (base2 : dconv) (tm : term) : IO (Except String thm) := do
  match tm with
  | .Comb (.Comb (.Const "/\\" _) l) r =>
      match ← (nnfConvN B P cf base1 base2 l : IO (Except String thm)) with
      | .error e => return .error e | .ok th_ln =>
      match ← (nnfConvN B P cf base1 base2 r : IO (Except String thm)) with
      | .error e => return .error e | .ok th_rn =>
        return (do TRANS (← INST [(l, P.p_tm), (r, P.q_tm)] P.pth_not_and)
                         (← MK_COMB (← AP_TERM P.or_tm th_ln) th_rn))
  | .Comb (.Comb (.Const "\\/" _) l) r =>
      match ← (nnfConvN B P cf base1 base2 l : IO (Except String thm)) with
      | .error e => return .error e | .ok th_ln =>
      match ← (nnfConvN B P cf base1 base2 r : IO (Except String thm)) with
      | .error e => return .error e | .ok th_rn =>
        return (do TRANS (← INST [(l, P.p_tm), (r, P.q_tm)] P.pth_not_or)
                         (← MK_COMB (← AP_TERM P.and_tm th_ln) th_rn))
  | .Comb (.Comb (.Const "==>" _) l) r =>
      match ← (nnfConvP B P cf base1 base2 l : IO (Except String thm)) with
      | .error e => return .error e | .ok th_lp =>
      match ← (nnfConvN B P cf base1 base2 r : IO (Except String thm)) with
      | .error e => return .error e | .ok th_rn =>
        return (do TRANS (← INST [(l, P.p_tm), (r, P.q_tm)] P.pth_not_imp)
                         (← MK_COMB (← AP_TERM P.and_tm th_lp) th_rn))
  | .Comb (.Comb (.Const "=" (.Tyapp "fun" (.Tyapp "bool" _ :: _))) l) r =>
      match ← (nnfDconv B P cf base2 l : IO (Except String (thm × thm))) with
      | .error e => return .error e | .ok (th_lp, th_ln) =>
      match ← (nnfDconv B P cf base2 r : IO (Except String (thm × thm))) with
      | .error e => return .error e | .ok (th_rp, th_rn) =>
        if cf then
          return (do TRANS (← INST [(l, P.p_tm), (r, P.q_tm)] P.pth_not_eq')
                       (← MK_COMB (← AP_TERM P.and_tm (← MK_COMB (← AP_TERM P.or_tm th_lp) th_rp))
                                  (← MK_COMB (← AP_TERM P.or_tm th_ln) th_rn)))
        else
          return (do TRANS (← INST [(l, P.p_tm), (r, P.q_tm)] P.pth_not_eq)
                       (← MK_COMB (← AP_TERM P.or_tm (← MK_COMB (← AP_TERM P.and_tm th_lp) th_rn))
                                  (← MK_COMB (← AP_TERM P.and_tm th_ln) th_rp)))
  | .Comb (.Const "!" qty) (.Abs x t) =>
      let bod := term.Abs x t
      match binderDomTy (term.Const "!" qty) with
      | .error e => return .error e | .ok ty =>
      match ← (nnfConvN B P cf base1 base2 t : IO (Except String thm)) with
      | .error e => return .error e | .ok th_n =>
        return (← (do
          let Pty := mk_var "P" (← (mk_fun_ty' ty : IO (Except String hol_type)))
          let th1 ← liftExcept (do INST [(bod, Pty)] (← INST_TYPE [(ty, aty)] P.pth_not_forall))
          let bx ← liftExcept (mk_comb bod x)
          let th2 ← liftExcept (do TRANS (← AP_TERM P.not_tm (← BETA bx)) th_n)
          let mex ← (MK_EXISTS x th2 : IO (Except String thm))
          liftExcept (TRANS th1 mex) : ExceptT String IO thm).run)
  | .Comb (.Const "?" qty) (.Abs x t) =>
      let bod := term.Abs x t
      match binderDomTy (term.Const "?" qty) with
      | .error e => return .error e | .ok ty =>
      match ← (nnfConvN B P true base1 base2 t : IO (Except String thm)) with
      | .error e => return .error e | .ok th_n =>
        return (← (do
          let Pty := mk_var "P" (← (mk_fun_ty' ty : IO (Except String hol_type)))
          let th1 ← liftExcept (do INST [(bod, Pty)] (← INST_TYPE [(ty, aty)] P.pth_not_exists))
          let bx ← liftExcept (mk_comb bod x)
          let th2 ← liftExcept (do TRANS (← AP_TERM P.not_tm (← BETA bx)) th_n)
          let mfa ← (MK_FORALL x th2 : IO (Except String thm))
          liftExcept (TRANS th1 mfa) : ExceptT String IO thm).run)
  | .Comb (.Const "?!" qty) (.Abs x t) =>
      let bod := term.Abs x t
      match binderDomTy (term.Const "?!" qty) with
      | .error e => return .error e | .ok ty =>
      match ← (nnfDconv B P cf base2 t : IO (Except String (thm × thm))) with
      | .error e => return .error e | .ok (th_p, th_n) =>
        return (← (do
          let y ← liftExcept (variant (x :: frees t) x)
          let eq ← (mkEq2 y x : IO (Except String term))
          let (_eth_p, eth_n) ← (base2 eq : IO (Except String (thm × thm)))
          let bth ← liftExcept (do BETA (← mk_comb bod x))
          let bth' ← liftExcept (do BETA_CONV (← mk_comb bod y))
          let th_p' ← liftExcept (INST [(y, x)] th_p)
          let Pty := mk_var "P" (← (mk_fun_ty' ty : IO (Except String hol_type)))
          let th1' ← liftExcept (do INST [(bod, Pty)] (← INST_TYPE [(ty, aty)] P.pth_not_exu))
          let fa_n ← (MK_FORALL x (← liftExcept (TRANS (← AP_TERM P.not_tm bth) th_n)) : IO (Except String thm))
          let inner2' ← liftExcept (do MK_COMB (← AP_TERM P.and_tm (← TRANS bth' th_p')) eth_n)
          let innerR' ← liftExcept (do MK_COMB (← AP_TERM P.and_tm (← TRANS bth th_p)) inner2')
          let ex_y ← (MK_EXISTS y innerR' : IO (Except String thm))
          let ex_xy ← (MK_EXISTS x ex_y : IO (Except String thm))
          let th2' ← liftExcept (do MK_COMB (← AP_TERM P.or_tm fa_n) ex_xy)
          liftExcept (TRANS th1' th2') : ExceptT String IO thm).run)
  | .Comb (.Const "~" _) t =>
      match ← (nnfConvP B P cf base1 base2 t : IO (Except String thm)) with
      | .error e => return .error e | .ok th1 =>
        return (do TRANS (← INST [(t, P.p_tm)] P.pth_not_not) th1)
  | _ =>
      match mk_neg tm with
      | .error e => return .error e
      | .ok tm' =>
        match ← (base1 tm' : IO (Except String thm)) with
        | .ok r => return .ok r | .error _ => return (.ok (REFL tm'))
end

/-- `GEN_NNF_CONV cf (base1, base2)`: the general NNF conversion. -/
def GEN_NNF_CONV (B : BoolThms) (P : NNFPths) (cf : Bool)
    (base1 : ioconv) (base2 : dconv) : ioconv :=
  nnfConvP B P cf base1 base2

/-- Default atomic base convs: identity on atoms. -/
private def nnfBase1 : ioconv := fun t => pure (.ok (REFL t))
private def nnfBase2 : dconv := fun t => pure ((do pure (REFL t, REFL (← mk_neg t))) : Except String (thm × thm))

/- ---------------------------------------------------------------------- -/
/- Some common special cases.                                             -/
/- ---------------------------------------------------------------------- -/

/-- Negation normal form (iffs split disjunctively). -/
def NNF_CONV (B : BoolThms) (P : NNFPths) : ioconv := GEN_NNF_CONV B P false nnfBase1 nnfBase2

/-- Negation normal form (iffs split conjunctively). -/
def NNFC_CONV (B : BoolThms) (P : NNFPths) : ioconv := GEN_NNF_CONV B P true nnfBase1 nnfBase2

/- ---------------------------------------------------------------------- -/
/- Skolemize a term already in NNF (doesn't matter if it's not prenex).   -/
/- ---------------------------------------------------------------------- -/

/-- Skolemize a term already in NNF. -/
def SKOLEM_CONV (B : BoolThms) (T : TheoremThms) (C : ClassThms) : ioconv :=
  Simp.thencIO
    (genRewrite B Simp.topDepthConvIO
      [T.EXISTS_OR_THM, T.LEFT_EXISTS_AND_THM, T.RIGHT_EXISTS_AND_THM,
       T.FORALL_AND_THM, C.LEFT_FORALL_OR_THM, C.RIGHT_FORALL_OR_THM,
       T.FORALL_SIMP, T.EXISTS_SIMP])
    (genRewrite B Simp.redepthConvIO
      [T.RIGHT_AND_EXISTS_THM, T.LEFT_AND_EXISTS_THM, T.OR_EXISTS_THM,
       T.RIGHT_OR_EXISTS_THM, T.LEFT_OR_EXISTS_THM, C.SKOLEM_THM])

/- ---------------------------------------------------------------------- -/
/- Put a term already in NNF into prenex form.                            -/
/- ---------------------------------------------------------------------- -/

/-- Put a term already in NNF into prenex form. -/
def PRENEX_CONV (B : BoolThms) (T : TheoremThms) (C : ClassThms) : ioconv :=
  genRewrite B Simp.redepthConvIO
    [T.AND_FORALL_THM, T.LEFT_AND_FORALL_THM, T.RIGHT_AND_FORALL_THM,
     C.LEFT_OR_FORALL_THM, C.RIGHT_OR_FORALL_THM,
     T.OR_EXISTS_THM, T.LEFT_OR_EXISTS_THM, T.RIGHT_OR_EXISTS_THM,
     T.LEFT_AND_EXISTS_THM, T.RIGHT_AND_EXISTS_THM]

/- ---------------------------------------------------------------------- -/
/- Weak and normal DNF conversion. The "weak" form gives a disjunction of -/
/- conjunctions, but has no particular associativity at either level and  -/
/- may contain duplicates. The regular forms give canonical               -/
/- right-associate lists without duplicates, but do not remove subsumed   -/
/- disjuncts.                                                             -/
/-                                                                        -/
/- In both cases the input term is supposed to be in NNF already. We do   -/
/- go inside quantifiers and transform their body, but don't move them.   -/
/- ---------------------------------------------------------------------- -/

/-- Distribute `/\` over `\/` (for DNF). `pth1 = a/\(b\/c) <=> a/\b\/a/\c`,
    `pth2 = (a\/b)/\c <=> a/\c\/b/\c`. -/
private partial def dnfDistribute (B : BoolThms) (pth1 pth2 : thm) (aTm bTm cTm : term)
    (tm : term) : Except String thm := do
  match tm with
  | .Comb (.Comb (.Const "/\\" _) a) (.Comb (.Comb (.Const "\\/" _) b) c) =>
      let th ← INST [(a, aTm), (b, bTm), (c, cTm)] pth1
      TRANS th (← BINOP_CONV (dnfDistribute B pth1 pth2 aTm bTm cTm) (← rand (concl th)))
  | .Comb (.Comb (.Const "/\\" _) (.Comb (.Comb (.Const "\\/" _) a) b)) c =>
      let th ← INST [(a, aTm), (b, bTm), (c, cTm)] pth2
      TRANS th (← BINOP_CONV (dnfDistribute B pth1 pth2 aTm bTm cTm) (← rand (concl th)))
  | _ => .ok (REFL tm)

/-- Weak DNF (disjunction of conjunctions, unnormalized). -/
partial def weakdnf (B : BoolThms) (pth1 pth2 : thm) (aTm bTm cTm : term) (tm : term) :
    Except String thm := do
  match tm with
  | .Comb (.Const "!" _) (.Abs _ _) => BINDER_CONV (weakdnf B pth1 pth2 aTm bTm cTm) tm
  | .Comb (.Const "?" _) (.Abs _ _) => BINDER_CONV (weakdnf B pth1 pth2 aTm bTm cTm) tm
  | .Comb (.Comb (.Const "\\/" _) _) _ => BINOP_CONV (weakdnf B pth1 pth2 aTm bTm cTm) tm
  | .Comb (.Comb (.Const "/\\" op') l) r =>
      let th ← MK_COMB (← AP_TERM (.Const "/\\" op') (← weakdnf B pth1 pth2 aTm bTm cTm l))
                       (← weakdnf B pth1 pth2 aTm bTm cTm r)
      TRANS th (← dnfDistribute B pth1 pth2 aTm bTm cTm (← rand (concl th)))
  | _ => .ok (REFL tm)

mutual
/-- Strong DNF: weak form under binders + strengthen (canonicalize). -/
partial def substrongdnf (B : BoolThms) (pth1 pth2 : thm) (aTm bTm cTm : term)
    (strengthen : ioconv) (tm : term) : IO (Except String thm) := do
  match tm with
  | .Comb (.Const "!" _) (.Abs _ _) =>
      (Simp.binderConvIO (strongdnf B pth1 pth2 aTm bTm cTm strengthen) tm : IO (Except String thm))
  | .Comb (.Const "?" _) (.Abs _ _) =>
      (Simp.binderConvIO (strongdnf B pth1 pth2 aTm bTm cTm strengthen) tm : IO (Except String thm))
  | .Comb (.Comb (.Const "\\/" _) _) _ =>
      (Simp.binopConvIO (substrongdnf B pth1 pth2 aTm bTm cTm strengthen) tm : IO (Except String thm))
  | .Comb (.Comb (.Const "/\\" op') l) r =>
      -- OCaml: `MK_COMB(AP_TERM op (substrongdnf l),substrongdnf r)`, arguments right to left.
      match ← (substrongdnf B pth1 pth2 aTm bTm cTm strengthen r : IO (Except String thm)) with
      | .error e => return .error e | .ok rth =>
      match ← (substrongdnf B pth1 pth2 aTm bTm cTm strengthen l : IO (Except String thm)) with
      | .error e => return .error e | .ok lth =>
        return (do
          let th ← MK_COMB (← AP_TERM (.Const "/\\" op') lth) rth
          TRANS th (← dnfDistribute B pth1 pth2 aTm bTm cTm (← rand (concl th))))
  | _ => return (.ok (REFL tm))

partial def strongdnf (B : BoolThms) (pth1 pth2 : thm) (aTm bTm cTm : term)
    (strengthen : ioconv) (tm : term) : IO (Except String thm) := do
  match ← (substrongdnf B pth1 pth2 aTm bTm cTm strengthen tm : IO (Except String thm)) with
  | .error e => return .error e
  | .ok th =>
    match rand (concl th) with
    | .error e => return .error e
    | .ok rhs =>
      match ← (strengthen rhs : IO (Except String thm)) with
      | .error e => return .error e
      | .ok th2 => return (TRANS th th2)
end

/-- Weak DNF conversion. -/
def WEAK_DNF_CONV (B : BoolThms) (pth1 pth2 : thm) (aTm bTm cTm : term) : ioconv :=
  fun tm => pure (weakdnf B pth1 pth2 aTm bTm cTm tm)

/-- DNF conversion (canonical). `strengthen = DEPTH_BINOP_CONV \/ CONJ_CANON THENC DISJ_CANON`. -/
def DNF_CONV (B : BoolThms) (pth1 pth2 : thm) (aTm bTm cTm orTm : term)
    (conjCanon disjCanon : ioconv) : ioconv :=
  let strengthen := Simp.thencIO (Simp.depthBinopConvIO orTm conjCanon) disjCanon
  fun tm => strongdnf B pth1 pth2 aTm bTm cTm strengthen tm

/- ---------------------------------------------------------------------- -/
/- Likewise for CNF.                                                      -/
/- ---------------------------------------------------------------------- -/

/-- Distribute `\/` over `/\` (for CNF). `pth1 = a\/(b/\c) <=> (a\/b)/\(a\/c)`,
    `pth2 = (a/\b)\/c <=> (a\/c)/\(b\/c)`. -/
private partial def cnfDistribute (B : BoolThms) (pth1 pth2 : thm) (aTm bTm cTm : term)
    (tm : term) : Except String thm := do
  match tm with
  | .Comb (.Comb (.Const "\\/" _) a) (.Comb (.Comb (.Const "/\\" _) b) c) =>
      let th ← INST [(a, aTm), (b, bTm), (c, cTm)] pth1
      TRANS th (← BINOP_CONV (cnfDistribute B pth1 pth2 aTm bTm cTm) (← rand (concl th)))
  | .Comb (.Comb (.Const "\\/" _) (.Comb (.Comb (.Const "/\\" _) a) b)) c =>
      let th ← INST [(a, aTm), (b, bTm), (c, cTm)] pth2
      TRANS th (← BINOP_CONV (cnfDistribute B pth1 pth2 aTm bTm cTm) (← rand (concl th)))
  | _ => .ok (REFL tm)

partial def weakcnf (B : BoolThms) (pth1 pth2 : thm) (aTm bTm cTm : term) (tm : term) :
    Except String thm := do
  match tm with
  | .Comb (.Const "!" _) (.Abs _ _) => BINDER_CONV (weakcnf B pth1 pth2 aTm bTm cTm) tm
  | .Comb (.Const "?" _) (.Abs _ _) => BINDER_CONV (weakcnf B pth1 pth2 aTm bTm cTm) tm
  | .Comb (.Comb (.Const "/\\" _) _) _ => BINOP_CONV (weakcnf B pth1 pth2 aTm bTm cTm) tm
  | .Comb (.Comb (.Const "\\/" op') l) r =>
      let th ← MK_COMB (← AP_TERM (.Const "\\/" op') (← weakcnf B pth1 pth2 aTm bTm cTm l))
                       (← weakcnf B pth1 pth2 aTm bTm cTm r)
      TRANS th (← cnfDistribute B pth1 pth2 aTm bTm cTm (← rand (concl th)))
  | _ => .ok (REFL tm)

mutual
/-- Strong CNF: distribute over the `\\/` leaves reached under `/\\`,
    applying `strengthen` at each leaf. -/
partial def substrongcnf (B : BoolThms) (pth1 pth2 : thm) (aTm bTm cTm : term)
    (strengthen : ioconv) (tm : term) : IO (Except String thm) := do
  match tm with
  | .Comb (.Const "!" _) (.Abs _ _) =>
      (Simp.binderConvIO (strongcnf B pth1 pth2 aTm bTm cTm strengthen) tm : IO (Except String thm))
  | .Comb (.Const "?" _) (.Abs _ _) =>
      (Simp.binderConvIO (strongcnf B pth1 pth2 aTm bTm cTm strengthen) tm : IO (Except String thm))
  | .Comb (.Comb (.Const "/\\" _) _) _ =>
      (Simp.binopConvIO (substrongcnf B pth1 pth2 aTm bTm cTm strengthen) tm : IO (Except String thm))
  | .Comb (.Comb (.Const "\\/" op') l) r =>
      -- OCaml: `MK_COMB(AP_TERM op (substrongcnf l),substrongcnf r)`, arguments right to left.
      match ← (substrongcnf B pth1 pth2 aTm bTm cTm strengthen r : IO (Except String thm)) with
      | .error e => return .error e | .ok rth =>
      match ← (substrongcnf B pth1 pth2 aTm bTm cTm strengthen l : IO (Except String thm)) with
      | .error e => return .error e | .ok lth =>
        return (do
          let th ← MK_COMB (← AP_TERM (.Const "\\/" op') lth) rth
          TRANS th (← cnfDistribute B pth1 pth2 aTm bTm cTm (← rand (concl th))))
  | _ => return (.ok (REFL tm))

partial def strongcnf (B : BoolThms) (pth1 pth2 : thm) (aTm bTm cTm : term)
    (strengthen : ioconv) (tm : term) : IO (Except String thm) := do
  match ← (substrongcnf B pth1 pth2 aTm bTm cTm strengthen tm : IO (Except String thm)) with
  | .error e => return .error e
  | .ok th =>
    match rand (concl th) with
    | .error e => return .error e
    | .ok rhs =>
      match ← (strengthen rhs : IO (Except String thm)) with
      | .error e => return .error e
      | .ok th2 => return (TRANS th th2)
end

/-- Weak CNF conversion. -/
def WEAK_CNF_CONV (B : BoolThms) (pth1 pth2 : thm) (aTm bTm cTm : term) : ioconv :=
  fun tm => pure (weakcnf B pth1 pth2 aTm bTm cTm tm)

/-- CNF conversion (canonical). `strengthen = DEPTH_BINOP_CONV /\ DISJ_CANON THENC CONJ_CANON`. -/
def CNF_CONV (B : BoolThms) (pth1 pth2 : thm) (aTm bTm cTm andTm : term)
    (conjCanon disjCanon : ioconv) : ioconv :=
  let strengthen := Simp.thencIO (Simp.depthBinopConvIO andTm disjCanon) conjCanon
  fun tm => strongcnf B pth1 pth2 aTm bTm cTm strengthen tm

/- ---------------------------------------------------------------------- -/
/- Simply right-associate w.r.t. a binary operator.                       -/
/- ---------------------------------------------------------------------- -/

/-- Distribution step for `ASSOC_CONV` (`th'` = symmetric associativity thm). -/
private partial def assocDistrib (th' : thm) (op x y z : term) (tm : term) :
    Except String thm := do
  match tm with
  | .Comb (.Comb op' (.Comb (.Comb op'' p) q)) r =>
      if op' == op && op'' == op then do
        let th1 ← INST [(p, x), (q, y), (r, z)] th'
        let (l, r') ← dest_comb (← rand (concl th1))
        let th2 ← AP_TERM l (← assocDistrib th' op x y z r')
        let th3 ← assocDistrib th' op x y z (← rand (concl th2))
        TRANS th1 (← TRANS th2 th3)
      else .ok (REFL tm)
  | _ => .ok (REFL tm)

/-- Association step for `ASSOC_CONV`. -/
private partial def assocFn (th' : thm) (op x y z : term) (tm : term) :
    Except String thm := do
  match tm with
  | .Comb (.Comb op' _p) q =>
      if op' == op then do
        let th ← AP_TERM (← rator tm) (← assocFn th' op x y z q)
        TRANS th (← assocDistrib th' op x y z (← rand (concl th)))
      else .ok (REFL tm)
  | _ => .ok (REFL tm)

/-- `ASSOC_CONV th`: right-associate w.r.t. the binary operator whose
    associativity is given by `th`. -/
def ASSOC_CONV (B : BoolThms) (th : thm) : Except String ioconv := do
  let th' ← SYM (← B.SPEC_ALL th)
  let (opx, yopz) ← dest_comb (← rhs (concl th'))
  let (op, x) ← dest_comb opx
  let y ← lhand yopz
  let z ← rand yopz
  .ok (fun tm => pure (assocFn th' op x y z tm))

/- ---------------------------------------------------------------------- -/
/- Eliminate select terms from a goal.                                    -/
/- ---------------------------------------------------------------------- -/

/-- Auxiliary `pth`s for `SELECT_ELIM_TAC` and `LAMBDA_ELIM_CONV`. -/
structure SelLamPths where
  selElimThm : thm      -- P((@) P) <=> (?) P
  selAxThm   : thm      -- ISPEC P SELECT_AX
  halfMkAbs  : thm      -- (s = \x. t x) <=> (!x. s x = t x)
  applyPth   : thm      -- (!a. (a=c) ==> P = Q a) ==> (P <=> !a. (a=c) ==> Q a)
  ptm        : term     -- P:A->bool
  deriving Inhabited

/-- Prove the `SELECT_ELIM`/`LAMBDA_ELIM` auxiliary theorems. -/
def setupSelLam (B : BoolThms) (T : TheoremThms) (C : ClassThms) (SELECT_AX : thm) :
    ExceptT String IO SelLamPths := do
  let prove := Tactics.prove B
  let REWRITE_TAC := Simp.REWRITE_TAC B
  let selElimThm ← (prove (← parse_term "(P:A->bool)((@) P) <=> (?) P")
      (THEN B (REWRITE_TAC [C.EXISTS_THM]) (THEN B (Tactics.BETA_TAC B) (Tactics.REFL_TAC B)))
      : IO (Except String thm))
  let ptm ← parse_term "P:A->bool"
  let selAxThm ← liftExcept (B.ISPEC ptm SELECT_AX)
  let halfMkAbs ← (prove (← parse_term "(s = \\x. t x) <=> (!x. s x = t x)")
      (REWRITE_TAC [C.FUN_EQ_THM]) : IO (Except String thm))
  let applyPth ← (prove (← parse_term
      "(!a. (a = c) ==> (P = Q a)) ==> (P <=> !a. (a = c) ==> Q a)")
      (Simp.SIMP_TAC B [T.LEFT_FORALL_IMP_THM, T.EXISTS_REFL]) : IO (Except String thm))
  return { selElimThm, selAxThm, halfMkAbs, applyPth, ptm }

/-- `SELECT_ELIM_THM t`: rewrite a select-term `(@) P` to `(?) P`. -/
private def selElimThmOf (S : SelLamPths) (tm : term) : IO (Except String thm) := do
  match dest_comb tm with
  | .error e => return .error e
  | .ok (stm, atm) =>
    match dest_const stm with
    | .ok (nm, _) =>
      if nm == "@" then
        return (do
          let v ← bndvar atm
          let inst ← PINST [(type_of v, aty)] [(atm, S.ptm)] S.selElimThm
          CONV_RULE (Equal.LAND_CONV Equal.BETA_CONV) inst)
      else return .error "SELECT_ELIM_THM: not a select-term"
    | _ => return .error "SELECT_ELIM_THM: not a select-term"

/-- `SELECT_ELIM_CONV`: eliminate all `@`-terms by rewriting to existentials. -/
def SELECT_ELIM_CONV (B : BoolThms) (S : SelLamPths) : ioconv := fun tm => do
  let selts := find_terms is_select tm
  let mut ths : List thm := []
  for t in selts do
    match ← (selElimThmOf S t : IO (Except String thm)) with
    | .error e => return .error e
    | .ok th => ths := ths ++ [th]
  match ← (Simp.PURE_REWRITE_CONV B ths : IO (Except String ioconv)) with
  | .error e => return .error e
  | .ok cnv => (cnv tm : IO (Except String thm))

/-- `SELECT_AX_THM t`: instantiate `SELECT_AX` for the select-term `t`. -/
private def selAxThmOf (B : BoolThms) (S : SelLamPths) (tm : term) : IO (Except String thm) := do
  match dest_comb tm with
  | .error e => return .error e
  | .ok (stm, atm) =>
    match dest_const stm with
    | .ok (nm, _) =>
      if nm == "@" then
        return (do
          let v ← bndvar atm
          let fvs := frees atm
          let th1 ← PINST [(type_of v, aty)] [(atm, S.ptm)] S.selAxThm
          let th2 ← CONV_RULE (Equal.BINDER_CONV (Equal.BINOP_CONV Equal.BETA_CONV)) th1
          B.GENL fvs th2)
      else return .error "SELECT_AX_THM: not a select-term"
    | _ => return .error "SELECT_AX_THM: not a select-term"

/-- `SELECT_ELIM_ICONV`: one step of implicational select elimination. -/
private def selElimIConv (B : BoolThms) (S : SelLamPths) (tm : term) : IO (Except String thm) := do
  match find_term is_select tm with
  | .error e => return .error e
  | .ok t =>
    match ← (selAxThmOf B S t : IO (Except String thm)) with
    | .error e => return .error e
    | .ok th1 =>
      -- fty = itlist (mk_fun_ty o type_of) fvs (type_of t) — mk_fun_ty is IO.
      -- `type_of` is total and `mk_fun_ty` is IO-valued, so plain `o` types: the
      -- composite is `term → hol_type → IO (Except ...)`, which the fold below
      -- consumes.  `type_of` runs FIRST.
      let funTyOf := mk_fun_ty o type_of
      let fvs := frees t
      let mut fty := type_of t
      for v in fvs.reverse do
        match ← (funTyOf v fty : IO (Except String hol_type)) with
        | .error e => return .error e
        | .ok ty => fty := ty
      let fn ← genvar fty
      return (← (do
        let itm ← liftExcept (mk_imp (concl th1) tm)
        let th2 ← liftExcept (do B.DISCH_ALL (← B.MP (← ASSUME itm) th1))
        let atm ← liftExcept (list_mk_abs fvs t)
        let rawdef ← (mkEq2 fn atm : IO (Except String term))
        let def_ ← liftExcept (do B.GENL fvs (← SYM (← RIGHT_BETAS fvs (← ASSUME rawdef))))
        let c ← (Simp.PURE_REWRITE_CONV B [def_] : IO (Except String ioconv))
        let th3 ← (c (← liftExcept (lhand (concl th2))) : IO (Except String thm))
        let gtm ← liftExcept (mk_forall fn (← rand (concl th3)))
        let th4 ← liftExcept (do EQ_MP (← SYM th3) (← B.SPEC fn (← ASSUME gtm)))
        let th5 ← liftExcept (do B.IMP_TRANS (← B.DISCH gtm th4) th2)
        liftExcept (do B.MP (← INST [(atm, fn)] (← B.DISCH rawdef th5)) (REFL atm))
        : ExceptT String IO thm).run)

/-- `SELECT_ELIMS_ICONV`: iterate select elimination to a fixpoint. -/
private partial def selElimsIConv (B : BoolThms) (S : SelLamPths) (tm : term) :
    IO (Except String thm) := do
  -- OCaml wraps the whole body in one `try ... with Failure _ -> DISCH tm (ASSUME tm)`,
  -- so ANY failure (first step, recursion, lhand, or IMP_TRANS) recovers.
  let fallback : Except String thm := do B.DISCH tm (← ASSUME tm)
  match ← (selElimIConv B S tm : IO (Except String thm)) with
  | .error _ => return fallback
  | .ok th =>
    match lhand (concl th) with
    | .error _ => return fallback
    | .ok tm' =>
      match ← (selElimsIConv B S tm' : IO (Except String thm)) with
      | .error _ => return fallback
      | .ok rth =>
        match B.IMP_TRANS rth th with
        | .ok r => return .ok r
        | .error _ => return fallback

/-- `SELECT_ELIM_TAC`: eliminate Hilbert-`@` terms from the goal. -/
def SELECT_ELIM_TAC (B : BoolThms) (S : SelLamPths) : tactic :=
  THEN B (Tactics.CONV_TAC B (SELECT_ELIM_CONV B S))
    (fun g => do
      match ← (selElimsIConv B S g.2 : IO (Except String thm)) with
      | .error e => return .error e
      | .ok th => (Tactics.MATCH_MP_TAC B th g : IO (Except String goalstate)))

/- ---------------------------------------------------------------------- -/
/- Eliminate all lambda-terms except those part of quantifiers.           -/
/- ---------------------------------------------------------------------- -/

/-- `find_lambda`: locate a non-quantifier lambda subterm. -/
private partial def findLambda (tm : term) : Except String term :=
  if is_abs tm then .ok tm
  else if is_var tm || is_const tm then .error "find_lambda"
  else if is_forall tm || is_exists tm || is_uexists tm then
    (do findLambda (← body (← rand tm)))
  else
    match dest_comb tm with
    | .error e => .error e
    | .ok (l, r) =>
      match findLambda l with
      | .ok x => .ok x
      | .error _ => findLambda r

/-- `ELIM_LAMBDA conv` (IO): apply `conv` at the found lambda position. -/
private partial def elimLambda (conv : ioconv) (tm : term) : IO (Except String thm) := do
  match ← (conv tm : IO (Except String thm)) with
  | .ok th => return .ok th
  | .error _ =>
    if is_abs tm then (Simp.absConvIO (elimLambda conv) tm : IO (Except String thm))
    else if is_var tm || is_const tm then return (.ok (REFL tm))
    else if is_forall tm || is_exists tm || is_uexists tm then
      (Simp.binderConvIO (elimLambda conv) tm : IO (Except String thm))
    else (Simp.combConvIO (elimLambda conv) tm : IO (Except String thm))

/-- `HALF_MK_ABS_CONV vs`: `s = \x1..xn. t x1..xn` ⟶ `!x1..xn. s .. = t ..`. -/
private partial def halfMkAbsConv (B : BoolThms) (halfMkAbs : thm) (vs : List term) : ioconv :=
  fun tm => do
    match vs with
    | [] => return (.ok (REFL tm))
    | _ :: rest =>
      let c := Simp.thencIO (genRewrite B (fun c => c) [halfMkAbs])
                            (Simp.binderConvIO (halfMkAbsConv B halfMkAbs rest))
      (c tm : IO (Except String thm))

/-- `LAMB1_CONV`: eliminate one lambda-term. -/
private def lamb1Conv (B : BoolThms) (S : SelLamPths) (tm : term) : IO (Except String thm) := do
  match findLambda tm with
  | .error e => return .error e
  | .ok atm =>
    match dest_abs atm with
    | .error e => return .error e
    | .ok (v, _bod) =>
      let vs := frees atm
      let vs' := vs ++ [v]
      match list_mk_abs vs atm with
      | .error e => return .error e
      | .ok aatm =>
        let f ← genvar (type_of aatm)
        return (← (do
          let eq ← (mkEq2 f aatm : IO (Except String term))
          let th1 ← liftExcept (do SYM (← RIGHT_BETAS vs (← ASSUME eq)))
          let th2 ← (elimLambda (genRewrite B (fun c => c) [th1]) tm : IO (Except String thm))
          let th3 ← (Drule.MATCH_MP B S.applyPth (← liftExcept (do B.GEN f (← B.DISCH_ALL th2)))
                     : IO (Except String thm))
          (Simp.convRuleIO
            (Simp.randConvIO (Simp.binderConvIO (Simp.landConvIO (halfMkAbsConv B S.halfMkAbs vs'))))
            th3 : IO (Except String thm))
          : ExceptT String IO thm).run)

/-- `LAMBDA_ELIM_CONV`: eliminate all non-quantifier lambda-terms. -/
partial def lambdaElimConv (B : BoolThms) (S : SelLamPths) (tm : term) : IO (Except String thm) := do
  match ← (Simp.thencIO (fun t => lamb1Conv B S t) (fun t => lambdaElimConv B S t) tm
           : IO (Except String thm)) with
  | .ok th => return .ok th
  | .error _ => return (.ok (REFL tm))

/-- `LAMBDA_ELIM_CONV` (canon.ml): replace lambda-abstractions by new
    function constants, so the result is first-order. -/
def LAMBDA_ELIM_CONV (B : BoolThms) (S : SelLamPths) : ioconv := fun tm => lambdaElimConv B S tm

/- ---------------------------------------------------------------------- -/
/- Eliminate conditionals; CONDS_ELIM_CONV aims for disjunctive           -/
/- splitting, for refutation procedures, and CONDS_CELIM_CONV for         -/
/- conjunctive. Both switch modes "sensibly" when going through a         -/
/- quantifier.                                                            -/
/- ---------------------------------------------------------------------- -/

/-- Auxiliary data for conditional elimination. `propsimps` is the basic
    propositional simplification net (supplied from `Session`). -/
structure CondsPths where
  thCond   : thm   -- ... ==> x = (b /\ x1 \/ ~b /\ x0)
  thCond'  : thm   -- ... ==> x = ((~b \/ x1) /\ (b \/ x0))
  falseTm  : term  -- F
  trueTm   : term  -- T
  propsimps : Nets.net Simp.gconv
  deriving Inhabited

/-- Prove the two conditional-elimination lemmas. -/
def setupConds (B : BoolThms) (C : ClassThms) (propsimps : Nets.net Simp.gconv) :
    ExceptT String IO CondsPths := do
  let prove := Tactics.prove B
  let ASM_REWRITE_TAC := Simp.ASM_REWRITE_TAC B
  let BOOL_CASES_TAC := Classic.BOOL_CASES_TAC B C.BOOL_CASES_AX
  -- canon.ml 606-616: each `prove` parses its own `b:bool`, then
  -- `false_tm = `F`` and `true_tm = `T``.
  let thCond ← (prove (← parse_term
      "((b <=> F) ==> x = x0) /\\ ((b <=> T) ==> x = x1) ==> x = (b /\\ x1 \\/ ~b /\\ x0)")
      (THEN B (BOOL_CASES_TAC (← parse_term "b:bool")) (ASM_REWRITE_TAC [])) : IO (Except String thm))
  let thCond' ← (prove (← parse_term
      "((b <=> F) ==> x = x0) /\\ ((b <=> T) ==> x = x1) ==> x = ((~b \\/ x1) /\\ (b \\/ x0))")
      (THEN B (BOOL_CASES_TAC (← parse_term "b:bool")) (ASM_REWRITE_TAC [])) : IO (Except String thm))
  let falseTm ← parse_term "F"
  let trueTm ← parse_term "T"
  return { thCond, thCond', falseTm, trueTm, propsimps }

/-- `find_conditional`: locate a conditional whose predicate is closed over `fvs`. -/
private partial def findConditional (fvs : List term) (tm : term) : Except String term :=
  match tm with
  | .Comb s t =>
      let closed := match lhand s with
                    | .ok ls => intersect (frees ls) fvs == []
                    | .error _ => false
      if is_cond tm && closed then .ok tm
      else
        match findConditional fvs s with
        | .ok r => .ok r
        | .error _ => findConditional fvs t
  | .Abs x t => findConditional (x :: fvs) t
  | _ => .error "find_conditional"

/-- `CONDS_ELIM_CONV'`: recursive conditional elimination with polarity flag `dfl`. -/
private partial def condsElimConv (B : BoolThms) (P : CondsPths) (dfl : Bool) (tm : term) :
    IO (Except String thm) := do
  let propsimp_conv : ioconv := Simp.depthConvIO (Simp.REWRITES_CONV P.propsimps)
  -- canon.ml 631-644: ONE `try ... with Failure _` covers the WHOLE success
  -- body - `find_conditional`, building `th_new`, AND the recursive
  -- `CONV_RULE (RAND_CONV (CONDS_ELIM_CONV dfl))` - so a failure at ANY step
  -- falls through to the structural cases below.  Matching on
  -- `findConditional` alone would route only ITS failure there (class #9).
  let attempt : IO (Except String thm) := do
   match findConditional [] tm with
   | .error e => return .error e
   | .ok t =>
    return (← (do
      let p ← liftExcept (do lhand (← rator t))
      let th_new ← (do
        if p == P.falseTm || p == P.trueTm then
          (propsimp_conv tm : IO (Except String thm))
        else
          (do
            let asm_0 ← (mkEq2 p P.falseTm : IO (Except String term))
            let asm_1 ← (mkEq2 p P.trueTm : IO (Except String term))
            let simp_0 ← (Simp.net_of_thm B false (← liftExcept (ASSUME asm_0)) P.propsimps
                          : IO (Except String (Nets.net Simp.gconv)))
            let simp_1 ← (Simp.net_of_thm B false (← liftExcept (ASSUME asm_1)) P.propsimps
                          : IO (Except String (Nets.net Simp.gconv)))
            let c0 ← (Simp.depthConvIO (Simp.REWRITES_CONV simp_0) tm : IO (Except String thm))
            let c1 ← (Simp.depthConvIO (Simp.REWRITES_CONV simp_1) tm : IO (Except String thm))
            let th_0 ← liftExcept (B.DISCH asm_0 c0)
            let th_1 ← liftExcept (B.DISCH asm_1 c1)
            let th_2 ← liftExcept (B.CONJ th_0 th_1)
            let th_3 ← (Drule.MATCH_MP B (if dfl then P.thCond else P.thCond') th_2
                        : IO (Except String thm))
            let proptsimp ← (do
              let cnv : ioconv := fun t' => do
                match ← (Simp.REWRITES_CONV P.propsimps t' : IO (Except String thm)) with
                | .ok th => return .ok th | .error _ => return (.ok (REFL t'))
              (Simp.thencIO (Simp.binopConvIO cnv) cnv (← liftExcept (rand (concl th_3)))
               : IO (Except String thm)))
            liftExcept (TRANS th_3 proptsimp))
        : ExceptT String IO thm)
      (Simp.convRuleIO (Simp.randConvIO (fun t' => condsElimConv B P dfl t')) th_new
       : IO (Except String thm))
      : ExceptT String IO thm).run)
  match ← attempt with
  | .ok th => return .ok th
  | .error _ =>
    if Basics.is_neg tm then
      (Simp.randConvIO (fun t => condsElimConv B P (!dfl) t) tm : IO (Except String thm))
    else if Basics.is_conj tm || Basics.is_disj tm then
      (Simp.binopConvIO (fun t => condsElimConv B P dfl t) tm : IO (Except String thm))
    else if Basics.is_imp tm || is_iff tm then
      (Simp.comb2ConvIO (Simp.randConvIO (fun t => condsElimConv B P (!dfl) t))
                        (fun t => condsElimConv B P dfl t) tm : IO (Except String thm))
    else if is_forall tm then
      (Simp.binderConvIO (fun t => condsElimConv B P false t) tm : IO (Except String thm))
    else if is_exists tm || is_uexists tm then
      (Simp.binderConvIO (fun t => condsElimConv B P true t) tm : IO (Except String thm))
    else return (.ok (REFL tm))

/-- `CONDS_ELIM_CONV`: eliminate conditionals, disjunctive splitting. -/
def CONDS_ELIM_CONV (B : BoolThms) (P : CondsPths) : ioconv := fun tm => condsElimConv B P true tm

/-- `CONDS_CELIM_CONV`: eliminate conditionals, conjunctive splitting. -/
def CONDS_CELIM_CONV (B : BoolThms) (P : CondsPths) : ioconv := fun tm => condsElimConv B P false tm

/- ---------------------------------------------------------------------- -/
/- Fix up all head arities to be consistent, in "first order logic"       -/
/- style. Applied to the assumptions (not conclusion) in a goal.          -/
/- ---------------------------------------------------------------------- -/

/-- `get_heads lconsts tm (cheads, vheads)`: accumulate `(head, arity)` pairs. -/
private partial def getHeads (lconsts : List term) (tm : term)
    (sofar : List (term × Nat) × List (term × Nat)) :
    List (term × Nat) × List (term × Nat) :=
  let (cheads, vheads) := sofar
  match dest_forall tm with
  | .ok (v, bod) => getHeads (subtract lconsts [v]) bod sofar
  | .error _ =>
    let conjDisj : Except String (term × term) :=
      match Basics.dest_conj tm with
      | .ok lr => .ok lr
      | .error _ => Basics.dest_disj tm
    match conjDisj with
    | .ok (l, r) => getHeads lconsts l (getHeads lconsts r sofar)
    | .error _ =>
      match Basics.dest_neg tm with
      | .ok tm' => getHeads lconsts tm' sofar
      | .error _ =>
        let (hop, args) := strip_comb tm
        let len := args.length
        let newheads :=
          if is_const hop || mem hop lconsts then (insert (hop, len) cheads, vheads)
          else if len > 0 then (cheads, insert (hop, len) vheads)
          else sofar
        itlist (getHeads lconsts) args newheads

/-- Auxiliary theorem for `ASM_FOL_TAC`: `!(f:A->B) x. f x = I f x`. -/
structure FolPths where
  appThm : thm
  deriving Inhabited

def setupFol (B : BoolThms) (I_THM : thm) : ExceptT String IO FolPths := do
  let prove := Tactics.prove B
  let appThm ← (prove (← parse_term "!(f:A->B) x. f x = I f x")
      (Simp.REWRITE_TAC B [I_THM]) : IO (Except String thm))
  return { appThm }

/-- `APP_N_CONV n`: apply `APP_CONV` `n` times up the operator spine. -/
private partial def appNConv (B : BoolThms) (appThm : thm) (n : Nat) (tm : term) :
    IO (Except String thm) := do
  if n == 1 then (Simp.REWR_CONV B appThm tm : IO (Except String thm))
  else (Simp.thencIO (Simp.ratorConvIO (fun t => appNConv B appThm (n - 1) t))
                     (fun t => Simp.REWR_CONV B appThm t) tm : IO (Except String thm))

/-- `FOL_CONV hddata`: fix up head arities. -/
private partial def folConv (B : BoolThms) (appThm : thm) (hddata : List (term × Nat))
    (tm : term) : IO (Except String thm) := do
  if is_forall tm then (Simp.binderConvIO (folConv B appThm hddata) tm : IO (Except String thm))
  else if Basics.is_conj tm || Basics.is_disj tm then
    (Simp.binopConvIO (folConv B appThm hddata) tm : IO (Except String thm))
  else
    let (op, args) := strip_comb tm
    -- th = rev_itlist (C (curry MK_COMB)) (map (FOL_CONV) args) (REFL op)
    let mut th := REFL op
    for a in args do
      match ← (folConv B appThm hddata a : IO (Except String thm)) with
      | .error e => return .error e
      | .ok ath =>
        match MK_COMB th ath with
        | .error e => return .error e
        | .ok t => th := t
    match rand (concl th) with
    | .error e => return .error e
    | .ok tm' =>
      let n := match assoc op hddata with
               | .ok k => if args.length ≥ k then args.length - k else 0
               | .error _ => 0
      if n == 0 then return .ok th
      else
        match ← (appNConv B appThm n tm' : IO (Except String thm)) with
        | .error e => return .error e
        | .ok ath => return (TRANS th ath)

/-- `GEN_FOL_CONV (cheads, vheads)`: build `hddata` then run `FOL_CONV`. -/
private def genFolConv (B : BoolThms) (P : FolPths)
    (heads : List (term × Nat) × List (term × Nat)) : ioconv :=
  let (cheads, vheads) := heads
  let hddata :=
    if vheads.isEmpty then
      let hops := setify (cheads.map Prod.fst)
      hops.filterMap (fun h =>
        let ns := cheads.filterMap (fun (k, n) => if k == h then some n else none)
        if ns.length < 2 then none
        else match ns with
             | [] => none
             | x :: xs => some (h, xs.foldl Nat.min x))
    else
      (setify ((vheads ++ cheads).map Prod.fst)).map (fun t =>
        if is_const t && (match dest_const t with | .ok (nm, _) => nm == "=" | _ => false)
        then (t, 2) else (t, 0))
  fun tm => folConv B P.appThm hddata tm

/-- `ASM_FOL_TAC`: normalise assumption head arities to first-order style. -/
def ASM_FOL_TAC (B : BoolThms) (P : FolPths) : tactic := fun (asl, w) => do
  let headsp := itlist
    (fun (p : String × thm) sofar => getHeads (freesl (hyp p.2)) (concl p.2) sofar)
    asl ([], [])
  (Tactics.RULE_ASSUM_TAC B (fun th => Simp.convRuleIO (genFolConv B P headsp) th) (asl, w)
   : IO (Except String goalstate))

/- ---------------------------------------------------------------------- -/
/- Depth conversion to apply at "atomic" formulas in "first-order" term.  -/
/- ---------------------------------------------------------------------- -/

/-- Apply `conv` at the atomic (non-propositional) subformulas. -/
partial def PROP_ATOM_CONV (conv : ioconv) (tm : term) : IO (Except String thm) := do
  match tm with
  | .Comb (.Const "!" _) (.Abs _ _)
  | .Comb (.Const "?" _) (.Abs _ _)
  | .Comb (.Const "?!" _) (.Abs _ _) =>
      (Simp.binderConvIO (PROP_ATOM_CONV conv) tm : IO (Except String thm))
  | .Comb (.Comb (.Const "/\\" _) _) _
  | .Comb (.Comb (.Const "\\/" _) _) _
  | .Comb (.Comb (.Const "==>" _) _) _
  | .Comb (.Comb (.Const "=" (.Tyapp "fun" (.Tyapp "bool" [] :: _))) _) _ =>
      (Simp.binopConvIO (PROP_ATOM_CONV conv) tm : IO (Except String thm))
  | .Comb (.Const "~" _) _ =>
      (Simp.randConvIO (PROP_ATOM_CONV conv) tm : IO (Except String thm))
  | _ =>
      match ← (conv tm : IO (Except String thm)) with
      | .ok th => return .ok th
      | .error _ => return (.ok (REFL tm))

/- ---------------------------------------------------------------------- -/
/- Consolidated Canon bundle (all pth's proved once).                     -/
/- ---------------------------------------------------------------------- -/

/-- All auxiliary theorems/terms needed by the `canon.ml` conversions. -/
structure CanonThms where
  nnf   : NNFPths
  selLam : SelLamPths
  conds : CondsPths
  fol   : FolPths
  -- DISJ_ACI pths
  disjPthLeft  : thm
  disjPthRight : thm
  disjPth      : thm
  disjPthNeg   : thm
  -- DNF/CNF distribution pths
  dnfPth1 : thm
  dnfPth2 : thm
  cnfPth1 : thm
  cnfPth2 : thm
  -- shared terms
  aTm : term
  bTm : term
  cTm : term
  orTm : term
  andTm : term
  deriving Inhabited

/-- Build the entire Canon auxiliary bundle. `propsimps` = basic conv net. -/
def setupCanon (B : BoolThms) (T : TheoremThms) (C : ClassThms)
    (ETA_AX SELECT_AX I_THM : thm) (propsimps : Nets.net Simp.gconv) :
    ExceptT String IO CanonThms := do
  let TAUT (s : String) : ExceptT String IO thm := do
    (Classic.TAUT B C.BOOL_CASES_AX (← parse_term s) : IO (Except String thm))
  let nnf ← setupNNFPths B T C ETA_AX
  let selLam ← setupSelLam B T C SELECT_AX
  let conds ← setupConds B C propsimps
  let fol ← setupFol B I_THM
  -- Each canon.ml block parses its own `a_tm`, `b_tm`, `c_tm` and operator
  -- quotations; the terms are equal, so the bundle keeps one copy.
  -- DISJ_ACI_RULE (canon.ml 46-51), the UNDISCH'd forms.
  let disjPthLeft ← liftExcept (B.UNDISCH (← TAUT "~(a \\/ b) ==> ~a"))
  let disjPthRight ← liftExcept (B.UNDISCH (← TAUT "~(a \\/ b) ==> ~b"))
  let disjPthTmp ← TAUT "~a ==> ~b ==> ~(a \\/ b)"
  let disjPth ← liftExcept (do B.UNDISCH (← B.UNDISCH disjPthTmp))
  let disjPthNeg ← liftExcept (B.UNDISCH (← TAUT "(~a <=> ~b) ==> (a <=> b)"))
  let aTm ← parse_term "a:bool"
  let bTm ← parse_term "b:bool"
  -- WEAK_DNF_CONV/DNF_CONV (canon.ml 393-406).
  let dnfPth1 ← TAUT "a /\\ (b \\/ c) <=> a /\\ b \\/ a /\\ c"
  let dnfPth2 ← TAUT "(a \\/ b) /\\ c <=> a /\\ c \\/ b /\\ c"
  let _ ← parse_term "a:bool"
  let _ ← parse_term "b:bool"
  let cTm ← parse_term "c:bool"
  let orTm ← parse_term "(\\/)"
  -- WEAK_CNF_CONV/CNF_CONV (canon.ml 435-448).
  let cnfPth1 ← TAUT "a \\/ (b /\\ c) <=> (a \\/ b) /\\ (a \\/ c)"
  let cnfPth2 ← TAUT "(a /\\ b) \\/ c <=> (a \\/ c) /\\ (b \\/ c)"
  let _ ← parse_term "a:bool"
  let _ ← parse_term "b:bool"
  let _ ← parse_term "c:bool"
  let andTm ← parse_term "(/\\)"
  return { nnf, selLam, conds, fol,
           disjPthLeft, disjPthRight, disjPth, disjPthNeg,
           dnfPth1, dnfPth2, cnfPth1, cnfPth2, aTm, bTm, cTm, orTm, andTm }

/- Convenience wrappers taking the full bundle. -/
def disjCanonConv (B : BoolThms) (K : CanonThms) : ioconv :=
  DISJ_CANON_CONV B K.disjPthLeft K.disjPthRight K.disjPth K.disjPthNeg K.aTm K.bTm

def dnfConv (B : BoolThms) (K : CanonThms) : ioconv :=
  DNF_CONV B K.dnfPth1 K.dnfPth2 K.aTm K.bTm K.cTm K.orTm
           (CONJ_CANON_CONV B) (disjCanonConv B K)

def cnfConv (B : BoolThms) (K : CanonThms) : ioconv :=
  CNF_CONV B K.cnfPth1 K.cnfPth2 K.aTm K.bTm K.cTm K.andTm
           (CONJ_CANON_CONV B) (disjCanonConv B K)

def weakDnfConv (B : BoolThms) (K : CanonThms) : ioconv :=
  WEAK_DNF_CONV B K.dnfPth1 K.dnfPth2 K.aTm K.bTm K.cTm

def weakCnfConv (B : BoolThms) (K : CanonThms) : ioconv :=
  WEAK_CNF_CONV B K.cnfPth1 K.cnfPth2 K.aTm K.bTm K.cTm

end HolCore.Canon
