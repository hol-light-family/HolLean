/- File: SessionCore/TheCops.lean
thecops.ml: the leanCoP and nanoCoP connection provers.  Their databases
and support theorems (`Cs`) are built by `initialize` when this module is
imported.
-/
import SessionCore.Metis
import HolCore.TheCops

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Theorems HolCore.Classic
open HolCore.Trivia HolCore.Printer

namespace Session


/-- Cached CoP support: Hashek theorems, the symmetry-augmented equality
    axioms, and the `~t==>F<=>t` tautology. -/
structure CopSupport where
  hashek : TheCops.Hashek.HashekThms
  eqSym : Meson.EqAxPths
  deriving Inhabited

initialize leancopDb : TheCops.Database.DB ← IO.mkRef []
initialize nanocopDb : TheCops.Ncdatabase.DB ← IO.mkRef []

/-- thecops.ml (module `Hashek`, hol_lib.ml 77) runs `new_definition
    `hashek = T`` and proves leanCoP's equality axioms at load; built here. -/
initialize Cs : CopSupport ← do
  match ← (do
    -- Hashek: hashek = T, and its supporting theorems.  Define FIRST so that
    -- `hashek` parses as the (bool) constant, not an untyped variable.
    let hashek_def ← (Drule.new_definition B (← parse_term "hashek = T") : IO (Except String thm))
    let hashek_tm ← parse_term "hashek"
    let hashek_thm ← (Tactics.prove B (← parse_term "hashek") (Simp.SIMP_TAC B [hashek_def]) : IO (Except String thm))
    let hashek_prop ← (Tactics.prove B
      (← parse_term "((x /\\ hashek) ==> (y /\\ hashek)) ==> (x ==> y)")
      (Simp.SIMP_TAC B [hashek_def]) : IO (Except String thm))
    let hashek_eq ← (Tactics.prove B (← parse_term "~ hashek <=> F")
      (Simp.SIMP_TAC B [hashek_def]) : IO (Except String thm))
    -- thecops.ml 43: MARK_ASSUMS = RULE_ASSUM_TAC (DISCH `hashek`).
    let mark_tm ← parse_term "hashek"
    let H : TheCops.Hashek.HashekThms :=
      { hashek_def, hashek_tm, hashek_thm, hashek_prop, hashek_eq, mark_tm }
    -- leanCoP equality axioms (Meson's + symmetry conjunct).
    let TAUT (s : String) : ExceptT String IO thm := do
      (Classic.TAUT B C.BOOL_CASES_AX (← parse_term s) : IO (Except String thm))
    let ASM_CASES_TAC := Classic.ASM_CASES_TAC B C.EXCLUDED_MIDDLE
    let tautConv : ioconv := fun w => (Classic.TAUT B C.BOOL_CASES_AX w : IO (Except String thm))
    let xeqy ← parse_term "x:A = y"
    let eqConj ← (Tactics.prove B
      (← parse_term "(x:A = x) /\\ (~(x = y) \\/ y = x) /\\ (~(x:A = y) \\/ ~(x = z) \\/ (y = z))")
      (Tactics.THEN B (Simp.REWRITE_TAC B [])
        (Tactics.THEN B (ASM_CASES_TAC xeqy)
          (Tactics.THEN B (Simp.ASM_REWRITE_TAC B []) (Tactics.CONV_TAC B tautConv)))) : IO (Except String thm))
    let eqThms := B.CONJUNCTS eqConj
    let impElim ← TAUT "(a ==> b) <=> ~a \\/ b"
    let eqElim ← TAUT "(a <=> b) ==> b \\/ ~a"
    let veqTm ← liftExcept (do match eqThms with
      | e0 :: _ => rator (← rator (concl e0)) | [] => .error "eqSym: no eq_thms")
    let eqSym : Meson.EqAxPths := { eqThms, impElim, eqElim, veqTm }
    -- thecops.ml 1256-1270: the three load-time `assert`s.  OCaml
    -- evaluates `x = y` and the list right to left.  They run when
    -- thecops.ml loads, with `copverb` at its default (false); this
    -- setup may be built later, so CONTRADICTION's trace is switched off.
    let verb ← HolCore.FirstOrder.copverb.get
    HolCore.FirstOrder.copverb.set false
    let want ← parse_term "c \\/ b \\/ a"
    let pc ← liftExcept (B.UNDISCH (← TAUT "c ==> c \\/ b \\/ a"))
    let pb ← liftExcept (B.UNDISCH (← TAUT "b ==> c \\/ b \\/ a"))
    let pa ← liftExcept (B.UNDISCH (← TAUT "a ==> c \\/ b \\/ a"))
    let abc ← liftExcept (HolCore.Kernel.ASSUME (← parse_term "a \\/ b \\/ c"))
    let got ← liftExcept (TheCops.Ncrecon.DISJ_CASES_LIST B abc [pa, pb, pc])
    unless concl got == want do throw "thecops.ml 1256: Assert_failure"
    for swap in [false, true] do
      let f ← parse_term "F"
      let (x, y) ← if swap then do
          let x ← parse_term "~p"; let y ← parse_term "p:bool"; pure (x, y)
        else do
          let y ← parse_term "p:bool"; let x ← parse_term "~p"; pure (x, y)
      let (tx, ty) ← liftExcept (do pure (← HolCore.Kernel.ASSUME x, ← HolCore.Kernel.ASSUME y))
      let c ← ExceptT.mk (if swap then TheCops.Ncrecon.CONTRADICTION B ty tx else TheCops.Ncrecon.CONTRADICTION B tx ty)
      unless concl c == f do throw "thecops.ml 1269: Assert_failure"
    HolCore.FirstOrder.copverb.set verb
    pure ({ hashek := H, eqSym } : CopSupport) : ExceptT String IO CopSupport).run with
  | .ok c => pure c
  | .error e => throw (IO.userError s!"CoP support setup failed: {e}")

/-- thecops.ml 33: MARK_CONCL's `TAUT `!t. (~t ==> F <=> t)``, proved each
    time PREPARE_COP_TAC is applied. -/
private def copNotTFimp : IO (Except String thm) := do
  match ← parse_term "!t. (~t ==> F <=> t)" with
  | .ok t => Classic.TAUT B C.BOOL_CASES_AX t
  | .error e => return .error e

private def LeancopD : TheCops.Leancop.LeancopDeps :=
  { S := MesonS, P := Mn.pths, mem := mesonContraposCache, db := leancopDb,
    E := Cs.eqSym, Emeson := Mn.eqAx, hashek := Cs.hashek, D := MesonD, notTFimp := copNotTFimp }

private def NanocopD : TheCops.Nanocop.NanocopDeps :=
  { S := MesonS, P := Mn.pths, mem := mesonContraposCache, db := nanocopDb,
    E := Cs.eqSym, Emeson := Mn.eqAx, hashek := Cs.hashek, D := MesonD, notTFimp := copNotTFimp,
    CONJ_ASSOC := T.CONJ_ASSOC, DISJ_ASSOC := T.DISJ_ASSOC }

/- ---------------------------------------------------------------------- -/
/- Expose the key functions at the top level.                             -/
/- (thecops.ml 1482)                                                      -/
/- ---------------------------------------------------------------------- -/

def LEANCOP_TAC (ths : List thm) : tactic := TheCops.Leancop.LEANCOP_TAC B LeancopD ths
def LEANCOP (ths : List thm) (tm : term) : IO (Except String thm) :=
  TheCops.Leancop.LEANCOP B LeancopD ths tm
/-- thecops.ml's `Hashek` theorems (`Hashek.hashek_def`, ...). -/
def hashekThms : TheCops.Hashek.HashekThms := Cs.hashek

def NANOCOP_TAC (ths : List thm) : tactic := TheCops.Nanocop.NANOCOP_TAC B NanocopD ths

/- ---------------------------------------------------------------------- -/
/- Probe accessors for the two DISTINCT equality-axiom bundles.            -/
/- ---------------------------------------------------------------------- -/
/-
  leanCoP and MESON must NOT share these.  thecops.ml 510-514 proves a
  THREE-conjunct `eq_thms` including the SYMMETRY clause `~(x = y) \/ y = x`;
  meson.ml 583-587 proves only TWO (reflexivity and transitivity).  Session
  wires `E := Cs.eqSym` (three) and `Emeson := Mn.eqAx` (two) accordingly.

  These accessors exist so a test can PIN that distinction, and so the cached
  `CopSupport` bundle is REACHABLE at all: it derives `Inhabited`, so without a
  public accessor a degenerate `|-  = ` bundle would be invisible unless a test
  actually ran leanCoP.
-/
def COP_EQ_THMS : List thm := Cs.eqSym.eqThms
def MESON_EQ_THMS : List thm := Mn.eqAx.eqThms
/- The tracing switches (HOL Light refs): `copverb` (firstorder.ml 13, the
   CoPs), `metisverb` (metis.ml 21) and `Metis_unify.verb` (metis.ml 9647).
   All off by default.  Set with e.g. `copverb.set true`. -/
export HolCore.FirstOrder (copverb)
export HolCore.Metis (metisverb metis_unify_verb)

/-- `PRINT_TAC`, `PRINT_ID_TAC` (thecops.ml 1462-1463). -/
def PRINT_TAC : tactic := TheCops.Nanocop.PRINT_TAC
def PRINT_ID_TAC (s : String) : tactic := TheCops.Nanocop.PRINT_ID_TAC s

def NANOCOP (ths : List thm) (tm : term) : IO (Except String thm) :=
  TheCops.Nanocop.NANOCOP B NanocopD ths tm

/-- `Equality.create_eq_axs sym` (thecops.ml 578): equality and congruence
    axioms for the constants in `tms`, with the symmetry axiom if `sym`. -/
def create_eq_axs (sym : Bool) (tms : List term) : IO (Except String (List thm)) :=
  TheCops.Equality.create_eq_axs B NanocopD.E NanocopD.Emeson sym tms
/-- `Nanocop.PREPARE_NANOCOP_TAC` (thecops.ml 1466). -/
def PREPARE_NANOCOP_TAC (ths : List thm) : tactic :=
  TheCops.Nanocop.PREPARE_NANOCOP_TAC B NanocopD ths

end Session
