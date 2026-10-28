/- File: SessionCore/Metis.lean
metis.ml: the Metis prover with proof reconstruction.  Its random-number
state and rule set (`MtRules`) are built by `initialize` when this module is
imported.
-/
import SessionCore.FirstOrder
import HolCore.Metis

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Theorems HolCore.Classic
open HolCore.Trivia HolCore.Printer

namespace Session


initialize metisRandGen  : IO.Ref StdGen ← IO.mkRef (mkStdGen 0)
initialize metisClauseId : IO.Ref Int    ← IO.mkRef 0
initialize metisGen      : IO.Ref Int    ← IO.mkRef 0

/-- Metis reuses MESON's term↔code stores (`fol_of_var`/`fol_of_const`). -/
def MetisS : Meson.FolStores := MesonS

/-- Metis's case-split limit (OCaml `split_limit` ref; default 0). -/
def metisSplitLimit : Int := 0

/-- `mk_eq` as a one-shot `(term×term) → IO (Except term)`. -/
private def metisMkEq (p : term × term) : IO (Except String term) := do
  match ← (mk_eq : IO (Except String ((term × term) → Except String term))) with
  | .ok f => return (f p)
  | .error e => return .error e

/-- `~`, `F`, `\/` as preterms (for building HOL literals during reconstruction). -/
private def metisQuotp (s : String) : IO HolCore.Preterm.preterm := do
  match ← HolCore.Parser.parse_term s with
  | .ok t => pure (HolCore.Preterm.preterm_of_term t)
  | .error e => panic! s!"Session.metisQuotp {s}: {e}"
-- metis.ml's Preterm module parses these quotations on every call.
private def metisNegp : IO HolCore.Preterm.preterm := metisQuotp "~"
private def metisFalsityp : IO HolCore.Preterm.preterm := metisQuotp "F"
private def metisDisjp : IO HolCore.Preterm.preterm := metisQuotp "\\/"

/-- `DISJ_ACI_RULE` as a `term → IO (Except thm)` (wraps Canon's pure form). -/
private def metisDisjAci (tm : term) : IO (Except String thm) :=
  pure (Canon.DISJ_ACI_RULE B Cn.disjPthLeft Cn.disjPthRight Cn.disjPth Cn.disjPthNeg
          Cn.aTm Cn.bTm tm)

/-- `CONJ_ACI_RULE` (canon.ml 28): prove `p <=> p'` for conjunctions equal up
    to associativity, commutativity and idempotence. -/
def CONJ_ACI_RULE : term → Except String thm := Canon.CONJ_ACI_RULE B

/-- `DISJ_ACI_RULE` (canon.ml 46): the same for disjunctions. -/
def DISJ_ACI_RULE (tm : term) : Except String thm :=
  Canon.DISJ_ACI_RULE B Cn.disjPthLeft Cn.disjPthRight Cn.disjPth Cn.disjPthNeg Cn.aTm Cn.bTm tm

/-- The RESOLVE / IMPL_NOT TAUT lemmas, proved once at load (metis.ml module
    `Metis_rules`, hol_lib.ml 76). -/
initialize MtRules : Metis.Metis_rules.MetisRulesDeps ← do
  let mkTaut (s : String) : ExceptT String IO thm := do
    (Classic.TAUT B C.BOOL_CASES_AX (← HolCore.Parser.parse_term s) : IO (Except String thm))
  match ← (do
    let r1  ← mkTaut "!a. a ==> ~a ==> F"
    let r2l ← mkTaut "!a b. a \\/ b ==> ~a ==> b"
    let r2r ← mkTaut "!a c. a ==> ~a \\/ c ==> c"
    let r3  ← mkTaut "!a b c. a \\/ b ==> ~a \\/ c ==> b \\/ c"
    let inl ← mkTaut "!a b. ~a ==> b <=> a \\/ b"
    let inr ← mkTaut "!a b. a ==> b <=> ~a \\/ b"
    pure ({ RESOLVE_1 := r1, RESOLVE_2L := r2l, RESOLVE_2R := r2r, RESOLVE_3 := r3,
            IMPL_NOT_L := inl, IMPL_NOT_R := inr,
            DISJ_ACI_RULE := metisDisjAci,
            PURE_ONCE_REWRITE_RULE := fun thl th => Simp.PURE_ONCE_REWRITE_RULE B thl th,
            mk_eq := metisMkEq } : Metis.Metis_rules.MetisRulesDeps)).run with
  | .ok r => pure r
  | .error e => throw (IO.userError s!"Metis rules setup failed: {e}")

/-- The reconstruction dependency bundle. -/
private def MetisRecon : Metis.Metis_reconstruct2.MetisReconDeps :=
  { S := MetisS, negp := metisNegp, falsityp := metisFalsityp, disjp := metisDisjp,
    rules := MtRules,
    EXCLUDED_MIDDLE := C.EXCLUDED_MIDDLE,
    term_type_unify := fun t1 t2 i => (Drule.term_type_unify t1 t2 i : IO (Except String _)),
    type_unify := fun a b s => pure (Drule.type_unify a b s),
    INSTANTIATE := fun i th => pure (Drule.INSTANTIATE i th),
    DISJ_CANON_CONV := Canon.disjCanonConv B Cn,
    PURE_ONCE_REWRITE_CONV := fun thl => Simp.PURE_ONCE_REWRITE_CONV B thl }

/-- `GEN_METIS_TAC ths`. -/
def GEN_METIS_TAC (ths : List thm) : tactic :=
  Metis.Metis.GEN_METIS_TAC B MesonD MetisS mesonContraposCache metisRandGen metisClauseId
    metisGen MetisRecon (Canon.disjCanonConv B Cn) metisSplitLimit ths

/-- `ASM_METIS_TAC = GEN_METIS_TAC`. -/
def ASM_METIS_TAC (ths : List thm) : tactic :=
  Metis.ASM_METIS_TAC B MesonD MetisS mesonContraposCache metisRandGen metisClauseId
    metisGen MetisRecon (Canon.disjCanonConv B Cn) metisSplitLimit ths

/-- `METIS_TAC ths = POP_ASSUM_LIST (K ALL_TAC) THEN ASM_METIS_TAC ths`. -/
def METIS_TAC (ths : List thm) : tactic :=
  Metis.METIS_TAC B MesonD MetisS mesonContraposCache metisRandGen metisClauseId
    metisGen MetisRecon (Canon.disjCanonConv B Cn) metisSplitLimit ths

/-- `METIS ths tm`: prove `tm` by Metis. -/
def METIS (ths : List thm) (tm : term) : IO (Except String thm) :=
  Metis.METIS B MesonD MetisS mesonContraposCache metisRandGen metisClauseId
    metisGen MetisRecon (Canon.disjCanonConv B Cn) metisSplitLimit ths tm

/-- `GEN_METIS_TAC_SPLIT n ths`: like `GEN_METIS_TAC` but with an explicit
    case-split limit `n` (OCaml sets the `split_limit` ref before calling). -/
def GEN_METIS_TAC_SPLIT (n : Int) (ths : List thm) : tactic :=
  Metis.Metis.GEN_METIS_TAC B MesonD MetisS mesonContraposCache metisRandGen metisClauseId
    metisGen MetisRecon (Canon.disjCanonConv B Cn) n ths

/-- `METIS_SPLIT n ths tm`: prove `tm` by Metis with case-split limit `n`. -/
def METIS_SPLIT (n : Int) (ths : List thm) (tm : term) : IO (Except String thm) :=
  Tactics.TAC_PROOF B ([], tm)
    (Tactics.THEN B (Tactics.POP_ASSUM_LIST (fun _ => Tactics.ALL_TAC)) (GEN_METIS_TAC_SPLIT n ths))

end Session
