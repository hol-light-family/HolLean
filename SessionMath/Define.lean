/- File: SessionMath/Define.lean
define.ml, the last file of hol_lib.ml: general recursive definitions and
`define`, each layer built by `initialize` when this module is imported, in
file order.  Also hol_lib.ml's `check_axioms`, and `prioritize_num` and
`prioritize_int` for user code.  The last `initialize` (`endQuietLoad`)
restores the printing switches that SessionCore/Base.lean's
`beginQuietLoad` turned off for the load.
-/
import SessionMath.Cart
import HolMath.Define

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Simp HolCore.Theorems HolCore.Classic HolCore.Trivia

namespace Session

/-- `inductive_type_store` as an `IO` read, threaded into `setupDefineSuite`
    (`theInductiveTypeStore` is a `List` ref, created in SessionCore/Theorems.lean). -/
def get_inductive_type_store : IO (List (String × (Int × thm × thm))) :=
  theInductiveTypeStore.get

/- ====================================================================== -/
/- define.ml.  cart.ml has already loaded (define.ml opens `needs "cart.ml"`);-/
/- every bundle is forced eagerly by an `initialize`, IN FILE ORDER.       -/
/- ====================================================================== -/

/-- `DefineCasewise` (define.ml 10-47): the `CASEWISE` recursive definition and
    its three theorems.  `CASEWISE_DEF` (13) is the file's ONLY
    `new_recursive_definition`, over `list_RECURSION`. -/
initialize DCase : HolMath.Define.DefineCasewise ← do
  ioOkI "setupDefineCasewise" (HolMath.Define.setupDefineCasewise new_recursive_definition
    MESON_TAC ASM_MESON_TAC
    list_RECURSION list_INDUCT
    listDefs.MEM listThms1.ALL_MEM FORALL_PAIR_THM PAIR_EQ).run

/-- `DefineAdmissible` (define.ml 48-78): `admissible`, `tailadmissible`,
    `superadmissible` and `MATCH_SEQPATTERN`.  Runs after `DCase`. -/
initialize DAdm : HolMath.Define.DefineAdmissible ← do
  ioOkI "setupDefineAdmissible" (HolMath.Define.setupDefineAdmissible new_definition
    MESON_TAC pairAux.MATCH pairAux.SEQPATTERN).run

/-- `DefineAdmissibleThms` (define.ml 79-222): the fifteen admissibility
    combinators `ADMISSIBLE_CONST` (82) through `ADMISSIBLE_MATCH_SEQPATTERN`
    (211).  `ADMISSIBLE_NSUM`/`ADMISSIBLE_SUM`/`ADMISSIBLE_MAP` reach into the
    Iterate (`NSUM_EQ_NUMSEG`/`SUM_EQ_NUMSEG`) and Lists (`MAP_EQ`/`ALL_MEM`)
    layers.  Runs after `DAdm`. -/
initialize DAdmT : HolMath.Define.DefineAdmissibleThms ← do
  ioOkI "setupDefineAdmissibleThms" (HolMath.Define.setupDefineAdmissibleThms MESON
    MESON_TAC ASM_MESON_TAC
    DAdm.admissible DAdm.MATCH_SEQPATTERN
    pairAux.MATCH pairAux.SEQPATTERN pairAux.UNGUARDED_PATTERN
    pairAux.GUARDED_PATTERN pairAux.GEQ_DEF
    C.FUN_EQ_THM FORALL_PAIR_THM T.AND_FORALL_THM T.MONO_FORALL
    IN3.NSUM_EQ_NUMSEG IS3.SUM_EQ_NUMSEG
    listThms1.MAP_EQ listThms1.ALL_MEM).run

/-- `DefineSuperadmissibleThms` (define.ml 223-356): the seven superadmissible
    generalizations `ADMISSIBLE_IMP_SUPERADMISSIBLE` (233) through
    `SUPERADMISSIBLE_MATCH_GUARDED_PATTERN` (330).  Runs after `DAdmT`. -/
initialize DSupT : HolMath.Define.DefineSuperadmissibleThms ← do
  ioOkI "setupDefineSuperadmissibleThms" (HolMath.Define.setupDefineSuperadmissibleThms
    ASM_MESON_TAC
    DAdm.admissible DAdm.tailadmissible DAdm.superadmissible
    DAdm.MATCH_SEQPATTERN
    DAdmT.ADMISSIBLE_CONST
    pairAux.MATCH pairAux.UNGUARDED_PATTERN
    pairAux.GUARDED_PATTERN pairAux.GEQ_DEF
    T.LEFT_IMP_EXISTS_THM T.RIGHT_IMP_FORALL_THM
    T.IMP_IMP T.AND_FORALL_THM T.MONO_AND T.MONO_FORALL).run

/-- `DefineWfCasewise` (define.ml 357-463): the WF/tail-recursion-meets-casewise
    theorems, including `RECURSION_CASEWISE` (419) and
    `RECURSION_SUPERADMISSIBLE` (460) - the two theorems define.ml 467-953
    instantiates mechanically.  The primed `WF_REC_TAIL_GENERAL'` is distinct
    from the pre-existing unprimed `Wf.WF_REC_TAIL_GENERAL`.  Runs after
    `DSupT`. -/
initialize DWfC : HolMath.Define.DefineWfCasewise ← do
  ioOkI "setupDefineWfCasewise" (HolMath.Define.setupDefineWfCasewise MESON_TAC ASM_MESON_TAC
    LIST_INDUCT_TAC
    Wf.WF_REC_TAIL_GENERAL
    DCase.CASEWISE DCase.CASEWISE_WORKS
    DAdm.tailadmissible DAdm.superadmissible DAdm.admissible
    listDefs.ALL listDefs.MEM listDefs.PAIRWISE listThms1.ALL_MEM
    FORALL_PAIR_THM list_INDUCT MONO_EXISTS FUN_EQ_THM
    T.IMP_IMP T.CONJ_ASSOC T.LEFT_IMP_EXISTS_THM
    T.RIGHT_IMP_FORALL_THM T.RIGHT_FORALL_IMP_THM T.IMP_CONJ).run

/-- `DefineSuite` (define.ml 467-953): the one binding yielding
    `instantiate_casewise_recursion`, `pure_prove_recursive_function_exists`
    and `prove_general_recursive_function_exists`, with its local helpers and
    lemmas built once.  Runs after `DWfC`. -/
initialize DSuite : HolMath.Define.DefineSuite ← do
  ioOkI "setupDefineSuite" (HolMath.Define.setupDefineSuite MESON_TAC MESON ARITH_RULE ARITH_TAC
    GEN_BETA_CONV FORALL_UNWIND_CONV theBasicRectypeNet.get
    prove_recursive_functions_exist get_inductive_type_store
    (HolMath.Nums.mk_small_numeral Nm.numK) DAdmT DSupT DWfC
    EQ_ADD_RCANCEL EQ_ADD_LCANCEL EQ_ADD_RCANCEL_0 EQ_ADD_LCANCEL_0
    EQ_MULT_RCANCEL EQ_MULT_LCANCEL T.EQ_REFL
    ADD_EQ_0 MULT_EQ_0 MULT_EQ_1 ARITH_EQ
    EVEN_MULT EVEN_ADD ARITH EVEN
    pairAux.UNGUARDED_PATTERN pairAux.GUARDED_PATTERN
    pairAux.GEQ_DEF T.SWAP_EXISTS_THM
    C.FUN_EQ_THM FORALL_PAIR_THM EXISTS_PAIR_THM T.EQ_IMP
    T.AND_CLAUSES T.OR_CLAUSES T.IMP_CLAUSES T.EQ_CLAUSES C.NOT_CLAUSES T.FORALL_SIMP
    listDefs.ALL listDefs.PAIRWISE CONJ_ASSOC EXISTS_REFL pairAux.LET_DEF pairAux.LET_END_DEF
    Wf.WF_LEX ETA_AX Wf.WF_MEASURE_GEN Wf.WF_MEASURE Wf.WF_FALSE
    Wf.MEASURE Wf.MEASURE_LE MONO_EXISTS).run

/-- `SIMPLIFY_WELLDEFINEDNESS_CONV` (define.ml 475-526).  Reads the live
    `basic_rectype_net` on every application. -/
def SIMPLIFY_WELLDEFINEDNESS_CONV : ioconv := fun tm =>
  DSuite.SIMPLIFY_WELLDEFINEDNESS_CONV tm
/-- `EXISTS_PAT_CONV` (define.ml 531-544). -/
def EXISTS_PAT_CONV : ioconv := fun tm => DSuite.EXISTS_PAT_CONV tm
/-- `HACK_PROFORMA` (define.ml 565-579). -/
def HACK_PROFORMA (n : Int) (th : thm) : IO (Except String thm) :=
  DSuite.HACK_PROFORMA n th
/-- `EACK_PROFORMA` (define.ml 580-595). -/
def EACK_PROFORMA (n : Int) (th : thm) : IO (Except String thm) :=
  DSuite.EACK_PROFORMA n th
/-- `APPLY_PROFORMA_TAC` (define.ml 602-605). -/
def APPLY_PROFORMA_TAC (th : thm) : tactic := fun g => DSuite.APPLY_PROFORMA_TAC th g
/-- `SIMPLIFY_MATCH_WELLDEFINED_TAC` (define.ml 612-622). -/
def SIMPLIFY_MATCH_WELLDEFINED_TAC : tactic := fun g =>
  DSuite.SIMPLIFY_MATCH_WELLDEFINED_TAC g
/-- `MAIN_ADMISS_TAC` (define.ml 630-683). -/
def MAIN_ADMISS_TAC : tactic := fun g => DSuite.MAIN_ADMISS_TAC g
/-- `ADMISS_TAC` (define.ml 685-689). -/
def ADMISS_TAC : tactic := fun g => DSuite.ADMISS_TAC g
/-- `instantiate_casewise_recursion` (define.ml 698-808). -/
def instantiate_casewise_recursion : ioconv := fun tm =>
  DSuite.instantiate_casewise_recursion tm
/-- `pure_prove_recursive_function_exists` (define.ml 814-851). -/
def pure_prove_recursive_function_exists : ioconv := fun tm =>
  DSuite.pure_prove_recursive_function_exists tm
/-- `prove_general_recursive_function_exists` (define.ml 857-947).  Reads the
    live `inductive_type_store`. -/
def prove_general_recursive_function_exists : ioconv := fun tm =>
  DSuite.prove_general_recursive_function_exists tm

/-- A no-op: every define.ml bundle is built at import.  Kept for callers of
    the old `ensureDefine`. -/
def ensureDefine : IO Unit := pure ()

/- ---------------------------------------------------------------------- -/
/- define.ml bare theorem re-exports.                                     -/
/- ---------------------------------------------------------------------- -/
-- DefineCasewise (define.ml 10-47)
def CASEWISE_DEF                : thm := DCase.CASEWISE_DEF
def CASEWISE                    : thm := DCase.CASEWISE
def CASEWISE_CASES              : thm := DCase.CASEWISE_CASES
def CASEWISE_WORKS              : thm := DCase.CASEWISE_WORKS

-- DefineAdmissible (define.ml 48-78)
def admissible_DEF              : thm := DAdm.admissible
def tailadmissible_DEF          : thm := DAdm.tailadmissible
def superadmissible_DEF         : thm := DAdm.superadmissible
def MATCH_SEQPATTERN            : thm := DAdm.MATCH_SEQPATTERN

-- DefineAdmissibleThms (define.ml 79-222)
def ADMISSIBLE_CONST            : thm := DAdmT.ADMISSIBLE_CONST
def ADMISSIBLE_BASE             : thm := DAdmT.ADMISSIBLE_BASE
def ADMISSIBLE_COMB             : thm := DAdmT.ADMISSIBLE_COMB
def ADMISSIBLE_RAND             : thm := DAdmT.ADMISSIBLE_RAND
def ADMISSIBLE_LAMBDA           : thm := DAdmT.ADMISSIBLE_LAMBDA
def ADMISSIBLE_NEST             : thm := DAdmT.ADMISSIBLE_NEST
def ADMISSIBLE_COND             : thm := DAdmT.ADMISSIBLE_COND
def ADMISSIBLE_MATCH            : thm := DAdmT.ADMISSIBLE_MATCH
def ADMISSIBLE_SEQPATTERN       : thm := DAdmT.ADMISSIBLE_SEQPATTERN
def ADMISSIBLE_UNGUARDED_PATTERN : thm := DAdmT.ADMISSIBLE_UNGUARDED_PATTERN
def ADMISSIBLE_GUARDED_PATTERN  : thm := DAdmT.ADMISSIBLE_GUARDED_PATTERN
def ADMISSIBLE_NSUM             : thm := DAdmT.ADMISSIBLE_NSUM
def ADMISSIBLE_SUM              : thm := DAdmT.ADMISSIBLE_SUM
def ADMISSIBLE_MAP              : thm := DAdmT.ADMISSIBLE_MAP
def ADMISSIBLE_MATCH_SEQPATTERN : thm := DAdmT.ADMISSIBLE_MATCH_SEQPATTERN

-- DefineSuperadmissibleThms (define.ml 223-356)
def ADMISSIBLE_IMP_SUPERADMISSIBLE : thm := DSupT.ADMISSIBLE_IMP_SUPERADMISSIBLE
def SUPERADMISSIBLE_CONST       : thm := DSupT.SUPERADMISSIBLE_CONST
def SUPERADMISSIBLE_TAIL        : thm := DSupT.SUPERADMISSIBLE_TAIL
def SUPERADMISSIBLE_COND        : thm := DSupT.SUPERADMISSIBLE_COND
def SUPERADMISSIBLE_MATCH_SEQPATTERN : thm := DSupT.SUPERADMISSIBLE_MATCH_SEQPATTERN
def SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN : thm := DSupT.SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN
def SUPERADMISSIBLE_MATCH_GUARDED_PATTERN : thm := DSupT.SUPERADMISSIBLE_MATCH_GUARDED_PATTERN

-- DefineWfCasewise (define.ml 357-463).  NOTE: `WF_REC_TAIL_GENERAL'` (primed)
-- is re-exported as `WF_REC_TAIL_GENERAL_prime`; the UNPRIMED, pre-existing
-- `WF_REC_TAIL_GENERAL` (from `Wf`) is a SEPARATE accessor, left untouched.
def WF_REC_TAIL_GENERAL_prime   : thm := DWfC.WF_REC_TAIL_GENERAL_prime
def WF_REC_CASES                : thm := DWfC.WF_REC_CASES
def WF_REC_CASES_prime          : thm := DWfC.WF_REC_CASES_prime
def RECURSION_CASEWISE          : thm := DWfC.RECURSION_CASEWISE
def RECURSION_CASEWISE_PAIRWISE : thm := DWfC.RECURSION_CASEWISE_PAIRWISE
def SUPERADMISSIBLE_T           : thm := DWfC.SUPERADMISSIBLE_T
def RECURSION_SUPERADMISSIBLE   : thm := DWfC.RECURSION_SUPERADMISSIBLE

-- DefineSuite probe theorems (local lemmas inside the `define` suite).
def DSUITE_eq_refl  : thm := DSuite.eq_refl
def DSUITE_elemma0  : thm := DSuite.elemma0
def DSUITE_elemma1  : thm := DSuite.elemma1
def DHACK_smw_pth0 : thm := DSuite.smw_pth0
def DHACK_smw_pth1 : thm := DSuite.smw_pth1
def DHACK_epa_pth0 : thm := DSuite.epa_pth0
def DHACK_epa_pth1 : thm := DSuite.epa_pth1
def DGUESS_pth_lexleft  : thm := DSuite.pth_lexleft
def DGUESS_pth_lexright : thm := DSuite.pth_lexright
def DGUESS_pth_measure  : thm := DSuite.pth_measure

/- ---------------------------------------------------------------------- -/
/- define.ml 954-1028: the simple `define` function.  THE USER-FACING     -/
/- ENTRY POINT, and the LAST thing `hol_lib.ml` loads - with this, the     -/
/- HOL Light core library is complete.                                    -/
/- ---------------------------------------------------------------------- -/

/-- `define tm` (define.ml 957-1028): accept a general recursive definition,
    written as a conjunction of clauses that may use pattern matching, discharge
    the proof obligations automatically, and introduce the constant.  Calls
    `prove_general_recursive_function_exists`, then `new_specification` and
    `mk_mconst`.

    State: the OCaml's final act is `the_definitions := th3::(!the_definitions)`
    (1028).  The pure HolMath function returns the entry to prepend (`some th3`
    when it defines, `none` on a benign redefinition); this accessor performs
    the ref write.  `the_definitions` is the `List` ref `theDefinitions`
    (created in SessionMath/Pair.lean). -/
def define (tm : term) : IO (Except String thm) := do
  let defs ← theDefinitions.get
  match ← HolMath.Define.define prove_general_recursive_function_exists
            new_specification Basics.mk_mconst defs tm with
  | .error e => return .error e
  | .ok (th, entry) => do
      -- `the_definitions := th3::(!the_definitions)` (define.ml 1028) reads the
      -- ref AFTER the definition is made: proving the recursion can itself add
      -- definitions, which must not be lost.
      match entry with
      | some th3 => theDefinitions.set (th3 :: (← theDefinitions.get))
      | none => pure ()
      return .ok th

/- ---------------------------------------------------------------------- -/
/- check_axioms (hol_lib.ml 105-114): the library's FINAL integrity check. -/
/- ---------------------------------------------------------------------- -/
/-
  hol_lib.ml ends by defining this (it does not call it).  HOL Light rests on
  exactly three axioms (`INFINITY_AX`, `SELECT_AX`, `ETA_AX`); anything else in
  `the_axioms` means an axiom leaked in, most likely via `mk_thm`, which is
  `new_axiom` underneath (drule.ml 24-26).

  `mem` is OCaml structural equality on `thm`, which is `equals_thm` here
  (comparing `dest_thm`, i.e. hypotheses and conclusion).
-/
def check_axioms : IO (Except String Unit) := do
  let basic_axioms := [Nm.INFINITY_AX, SELECT_AX, ETA_AX]
  let l := (← HolCore.Kernel.axioms).filter
             (fun th => !(basic_axioms.any (equals_thm th)))
  if l.isEmpty then return .ok ()
  else
    let strs ← l.mapM HolCore.Printer.string_of_thm
    return .error s!"check_axioms: [{String.intercalate ", " strs}]"

/-- `prioritize_num` (nums.ml): make `:num` the default for overloaded symbols. -/
def prioritize_num : IO Unit := do
  match ← (mk_type "num" []) with
  | .ok ty => prioritize_overload ty
  | .error e => throw (IO.userError s!"prioritize_num: {e}")

/-- `prioritize_int` (int.ml): make `:int` the default for overloaded symbols.
    The `int` theory was built at import (SessionMath/Int.lean). -/
def prioritize_int : IO Unit := do
  match ← (mk_type "int" []) with
  | .ok ty => prioritize_overload ty
  | .error e => throw (IO.userError s!"prioritize_int: {e}")


/-- The end of the load: restore the printing switches turned off by
    `beginQuietLoad` (SessionCore/Base.lean), so the user's own commands print as
    HOL Light's do.  The LAST `initialize` of the session. -/
initialize endQuietLoad : Unit ← do
  HolCore.Lib.verbose.set loadFlags.verbose
  HolCore.Preterm.type_invention_warning.set loadFlags.typeInventionWarning
  HolMath.Grobner.grobner_messages.set loadFlags.grobnerMessages
  HolCore.Lib.report_timing.set loadFlags.reportTiming
  -- HOLLEAN_SHOW_LOAD=2's tracing is for the load only (HOL Light default off).
  if loadFlags.tracing then
    for f in [HolCore.FirstOrder.copverb, HolCore.Metis.metisverb,
              HolCore.Metis.metis_unify_verb] do f.set false
    HolCore.FirstOrder.stdFlush


end Session
