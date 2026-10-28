/- File: SessionMath/Compute.lean
compute.ml: call-by-value reduction (HOL4's computeLib).  The pure library is
HolMath.Compute; its mutable state (the flags and the global compset
`theCompset`) is created by `initialize` when this module is imported.
-/
import SessionMath.Pair
import HolMath.Compute

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Simp HolCore.Theorems HolCore.Classic

namespace Session

deriving instance Nonempty for HolMath.Compute.compset

private def ioOk' {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")

private def pt (s : String) : IO term := ioOk' s!"parse {s}" (HolCore.Parser.parse_term s)

/- compute.ml : call-by-value reduction of terms (HOL4's computeLib).     -/
/- The pure library lives in `HolMath.Compute`; the module-level mutable  -/
/- state (the flags and the global compset) lives here (Session 2132-2290).-/
/- ---------------------------------------------------------------------- -/

/-- `monitoring`: when `Some p`, the instance of each rewrite rule used to reduce
    a constant satisfying `p` is printed. -/
initialize monitoring : IO.Ref (Option (term → Bool)) ← IO.mkRef none

/-- `stoppers`: when `Some p`, reduction stops at constants satisfying `p`
    (this is how `RESTR_EVAL_CONV` restricts evaluation). -/
initialize stoppers : IO.Ref (Option (term → Bool)) ← IO.mkRef none

/-- The two `compute.ml` module-level flags, bundled for the pure library. -/
def computeFlags : HolMath.Compute.ComputeFlags :=
  { monitoring := monitoring, stoppers := stoppers }

/-- The `t:A->B` witness that `ETA_CONV`/`try_eta` instantiate: compute.ml
    calls class.ml's ETA_CONV, so it is ETA_CONV's own `t`. -/
private def computeEtaT : term := C.etaT

/-- The `COND` constant, whose branches `CBV_CONV` is told to skip.  An action:
    compute.ml parses the quotation in each `bool_compset ()` and
    `basic_compset ()` call. -/
private def condTm : IO term := pt "COND: bool -> A -> A -> A"

/-- The `LET` constant, to which `let_CONV` is attached at arity 2 (parsed in
    each `basic_compset ()` call, as in compute.ml). -/
private def letTm : IO term := pt "LET:(A->B)->A->B"

/-- `lazyfy_thm`: use a lazy rule to avoid computing arguments. -/
def lazyfy_thm : thm → IO (Except String thm) :=
  HolMath.Compute.lazyfy_thm ETA_AX

/-- `strictify_thm`: the converse of `lazyfy_thm`. -/
def strictify_thm : thm → Except String thm :=
  HolMath.Compute.strictify_thm

/-- `new_compset`: a compset built from a list of rewrite theorems. -/
def new_compset (lthm : List thm) : IO (Except String HolMath.Compute.compset) :=
  HolMath.Compute.from_list T.REFL_CLAUSE lthm

/-- `bool_compset ()`: the boolean reductions. -/
def bool_compset : IO (Except String HolMath.Compute.compset) :=
  HolMath.Compute.bool_compset ETA_AX T.REFL_CLAUSE pairAux.LET_DEF C.COND_CLAUSES C.COND_ID
    C.NOT_CLAUSES T.AND_CLAUSES T.OR_CLAUSES T.IMP_CLAUSES T.EQ_CLAUSES condTm

/-- `basic_compset ()`: the boolean reductions plus the basic rewrites and
    conversions, and `let_CONV`. -/
def basic_compset : IO (Except String HolMath.Compute.compset) :=
  HolMath.Compute.basic_compset ETA_AX T.REFL_CLAUSE C.SELECT_REFL T.FORALL_SIMP
    T.EXISTS_SIMP letTm let_CONV condTm

/-- `add_thms`: add rewrite theorems to a compset. -/
def add_thms (lthm : List thm) (cs : HolMath.Compute.compset) :
    IO (Except String Unit) :=
  HolMath.Compute.add_thms lthm cs

/-- `add_conv (cst, arity, conv)`: attach a conversion to a constant. -/
def add_conv (cst : term) (arity : Int) (conv : ioconv)
    (cs : HolMath.Compute.compset) : IO (Except String Unit) :=
  HolMath.Compute.add_conv cst arity conv cs

/-- `set_skip`: mark arguments of a constant as not to be evaluated. -/
def set_skip (cs : HolMath.Compute.compset) (c : term) (opt : Option Int) :
    IO (Except String Unit) :=
  HolMath.Compute.set_skip cs c opt

/-- `scrub_const`: remove all rules attached to a constant. -/
def scrub_const (cs : HolMath.Compute.compset) (c : term) :
    IO (Except String Unit) :=
  HolMath.Compute.scrub_const cs c

/-- `scrub_thms`: remove the rules of the given theorems. -/
def scrub_thms (lthm : List thm) (cs : HolMath.Compute.compset) :
    IO (Except String Unit) :=
  HolMath.Compute.scrub_thms lthm cs

/-- `CBV_CONV rws`: full call-by-value normalization. -/
def CBV_CONV (cs : HolMath.Compute.compset) : term → IO (Except String thm) :=
  HolMath.Compute.CBV_CONV computeFlags C.etaPth computeEtaT cs

/-- `WEAK_CBV_CONV rws`: as `CBV_CONV`, but does not reduce under abstractions. -/
def WEAK_CBV_CONV (cs : HolMath.Compute.compset) : term → IO (Except String thm) :=
  HolMath.Compute.WEAK_CBV_CONV computeFlags cs

/-- `listItems`: the transforms attached to each constant of a compset. -/
def listItems (cs : HolMath.Compute.compset) :
    IO (List (String × List HolMath.Compute.transform)) :=
  HolMath.Compute.deplist cs

/-- The global compset, `the_compset = bool_compset()` (compute.ml 787),
    built when this module loads, as OCaml evaluates it at module
    initialisation. -/
initialize theCompset : HolMath.Compute.compset ← ioOk' "bool_compset" bool_compset

/-- `the_compset`. -/
def the_compset : IO HolMath.Compute.compset := pure theCompset

/-- `add_funs`: add rewrite theorems to the global compset. -/
def add_funs (lthm : List thm) : IO (Except String Unit) := do
  add_thms lthm (← the_compset)

/-- `add_convs`: add conversions to the global compset. -/
def add_convs (l : List (term × Int × ioconv)) : IO (Except String Unit) := do
  let cs ← the_compset
  for (cst, arity, conv) in l do
    match ← add_conv cst arity conv cs with
    | .error e => return .error e
    | .ok _ => pure ()
  return .ok ()

/-- `del_consts`: remove all rules for the given constants from the global
    compset. -/
def del_consts (l : List term) : IO (Except String Unit) := do
  let cs ← the_compset
  for c in l do
    match ← scrub_const cs c with
    | .error e => return .error e
    | .ok _ => pure ()
  return .ok ()

/-- `del_funs`: remove the given theorems' rules from the global compset. -/
def del_funs (lthm : List thm) : IO (Except String Unit) := do
  scrub_thms lthm (← the_compset)

/-- `EVAL_CONV`: call-by-value evaluation with the global compset. -/
def EVAL_CONV : term → IO (Except String thm) :=
  fun t => do CBV_CONV (← the_compset) t

/-- `EVAL_RULE`. -/
def EVAL_RULE : thm → IO (Except String thm) := Simp.convRuleIO EVAL_CONV

/-- `EVAL_TAC`. -/
def EVAL_TAC : tactic := CONV_TAC EVAL_CONV

/-- `OR clist`: does a term match any of the constants in `clist`? -/
def OR : List term → term → Bool := HolMath.Compute.OR

/-- `RESTR_EVAL_CONV clist`: evaluate, but stop at the constants in `clist`. -/
def RESTR_EVAL_CONV (clist : List term) : term → IO (Except String thm) :=
  HolMath.Compute.with_flag stoppers (some (HolMath.Compute.OR clist)) EVAL_CONV

/-- `RESTR_EVAL_TAC`. -/
def RESTR_EVAL_TAC (clist : List term) : tactic :=
  CONV_TAC (RESTR_EVAL_CONV clist)

/-- `RESTR_EVAL_RULE`. -/
def RESTR_EVAL_RULE (clist : List term) : thm → IO (Except String thm) :=
  Simp.convRuleIO (RESTR_EVAL_CONV clist)

end Session
