/- File: SessionCore/Classic.lean
class.ml: classical reasoning, built by `initialize` when this module is
imported, in class.ml's order: its axioms ETA_AX and SELECT_AX and the `@`
binder (`classAxiomLayer`), then the rest of the file, including COND_DEF at
its line, built quietly (`classLayer`, the bundle `C`), and its names as
top-level names.
-/
import SessionCore.IndDefs
import HolCore.Classic

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Theorems HolCore.Classic
open HolCore.Trivia HolCore.Printer

namespace Session

private def ioOk {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")

/-- class.ml's axioms, in class.ml's order: ETA_AX (16), the `@` constant and
    binder (45-47) and SELECT_AX (53).  `setupClass` takes them as
    parameters; COND (315) is defined inside `setupClass`, at its line. -/
private def bootClassAxioms : IO (thm × thm) := do
  let eta ← ioOk "ETA_AX" (do Kernel.new_axiom (← ioOk "ETA_AX parse" (HolCore.Parser.parse_term "!t:A->B. (\\x. t x) = t")))
  let selTy ← ioOk "@ type" (HolCore.Parser.parse_type "(A->bool)->A")
  ioOk "new_constant @" (Kernel.new_constant "@" selTy)
  HolCore.Printer.parse_as_binder "@"
  let sel ← ioOk "SELECT_AX" (do Kernel.new_axiom (← ioOk "SELECT_AX parse" (HolCore.Parser.parse_term "!P (x:A). P x ==> P ((@) P)")))
  pure (eta, sel)

initialize classAxiomLayer : thm × thm ← bootClassAxioms

def ETA_AX : thm := classAxiomLayer.1
def SELECT_AX : thm := classAxiomLayer.2

/-- The rest of class.ml, run quietly (as the old Session did). -/
private def bootClass : IO ClassThms := do
  let verb ← HolCore.Lib.verbose.get
  let tiw ← HolCore.Preterm.type_invention_warning.get
  HolCore.Lib.verbose.set false
  HolCore.Preterm.type_invention_warning.set false
  let c ← ioOk "setupClass" (setupClass B T ETA_AX SELECT_AX).run
  theMonotonicityTheorems.set
    (c.MONO_COND :: [T.MONO_AND, T.MONO_OR, T.MONO_IMP, T.MONO_NOT, T.MONO_EXISTS, T.MONO_FORALL])
  theInductiveTypeStore.set [("bool", (2, c.bool_INDUCT, c.bool_RECURSION))]
  HolCore.Lib.verbose.set verb
  HolCore.Preterm.type_invention_warning.set tiw
  pure c

initialize classLayer : ClassThms ← bootClass

def C : ClassThms := classLayer

/-- `COND_DEF` (class.ml 315), defined by `setupClass` at its line. -/
def COND_DEF : thm := C.COND_DEF

/- class.ml (Session 950-1014). -/
/-- The Bool, Class and Theorem bundles, for the `SessionLibrary` wiring,
    which passes them to the pure `HolLibrary` files. -/
def sessionB : BoolThms := B
def sessionC : ClassThms := C
def sessionT : TheoremThms := T
def EQ_EXT := C.EQ_EXT
def EXISTS_THM := C.EXISTS_THM
def SELECT_REFL := C.SELECT_REFL
def EXCLUDED_MIDDLE := C.EXCLUDED_MIDDLE
def BOOL_CASES_AX := C.BOOL_CASES_AX
def BOOL_CASES_TAC (p : term) : tactic := Classic.BOOL_CASES_TAC B C.BOOL_CASES_AX p
def ASM_CASES_TAC (t : term) : tactic := Classic.ASM_CASES_TAC B C.EXCLUDED_MIDDLE t
def NOT_CLAUSES := C.NOT_CLAUSES
def EXISTS_NOT_THM := C.EXISTS_NOT_THM
def FORALL_NOT_THM := C.FORALL_NOT_THM
def FORALL_BOOL_THM := C.FORALL_BOOL_THM
def EXISTS_BOOL_THM := C.EXISTS_BOOL_THM
/- These fixed proforma variables need no parser state, so they are built
   directly and stay PURE (verified identical to parsing "P:bool" etc.). -/
private def boolP  : term := mk_var "P" bool_ty
def CCONTR (tm : term) (th : thm) : Except String thm :=
  Classic.CCONTR B C.ccontrPth boolP tm th
def CONTRAPOS_CONV (tm : term) : Except String thm :=
  Classic.CONTRAPOS_CONV C.contraposConvPth C.contraposA C.contraposB tm
def LEFT_FORALL_OR_THM := C.LEFT_FORALL_OR_THM
def RIGHT_FORALL_OR_THM := C.RIGHT_FORALL_OR_THM
def LEFT_OR_FORALL_THM := C.LEFT_OR_FORALL_THM
def RIGHT_OR_FORALL_THM := C.RIGHT_OR_FORALL_THM
def LEFT_IMP_FORALL_THM := C.LEFT_IMP_FORALL_THM
def LEFT_EXISTS_IMP_THM := C.LEFT_EXISTS_IMP_THM
def RIGHT_IMP_EXISTS_THM := C.RIGHT_IMP_EXISTS_THM
def RIGHT_EXISTS_IMP_THM := C.RIGHT_EXISTS_IMP_THM
def COND_CLAUSES := C.COND_CLAUSES
def COND_EXPAND := C.COND_EXPAND
def COND_ABS := C.COND_ABS
def MONO_COND := C.MONO_COND
def COND_ELIM_THM := C.COND_ELIM_THM
def COND_CASES_TAC : tactic := Classic.COND_CASES_TAC B C.COND_ELIM_THM C.denegPth
def is_cond := Classic.is_cond
def mk_cond := Classic.mk_cond
def dest_cond := Classic.dest_cond
def SKOLEM_THM_GEN := C.SKOLEM_THM_GEN
def UNIQUE_SKOLEM_ALT := C.UNIQUE_SKOLEM_ALT
def UNIQUE_SKOLEM_THM := C.UNIQUE_SKOLEM_THM
def COND_CONG := C.COND_CONG
def COND_EQ_CLAUSE := C.COND_EQ_CLAUSE
def bool_INDUCT := C.bool_INDUCT
def bool_RECURSION := C.bool_RECURSION

/-- `inductive_type_store := l`. -/
def set_inductive_type_store (l : List (String × (Int × thm × thm))) : IO Unit :=
  theInductiveTypeStore.set l

def TAUT (tm : term) : IO (Except String thm) := Classic.TAUT B C.BOOL_CASES_AX tm

def selP : term := mk_var "P" (.Tyapp "fun" [aty, bool_ty])
def SELECT_RULE (th : thm) : Except String thm := Classic.SELECT_RULE B C.selectRulePth selP th
def SELECT_CONV (tm : term) : Except String thm := Classic.SELECT_CONV C.selectConvPth selP tm

def DE_MORGAN_THM := C.DE_MORGAN_THM
def CONTRAPOS_THM := C.CONTRAPOS_THM
def NOT_EXISTS_THM := C.NOT_EXISTS_THM

end Session
