/- File: SessionCore/ImpConv.lean
impconv.ml: implicational rewriting (IMP_REWRITE_TAC and its relatives).
Its variables and dependencies (`Icv`, `Icd`) are built by `initialize` when
this module is imported.  This is the last file of SessionCore: pair.ml, the
first of SessionMath, comes next in hol_lib.ml.
-/
import SessionCore.Quot
import HolCore.ImpConv

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Theorems HolCore.Classic
open HolCore.Trivia HolCore.Printer

namespace Session


/-- The `A/B/C/D/T : bool` instantiation-target constants for `impconv`. -/
initialize Icv : ImpConv.ImpConvVars ← do
  match ← (do
    let and_tm ← parse_term "(/\\)"                    -- impconv.ml 41
    let A_ ← parse_term "A:bool"
    let B_ ← parse_term "B:bool"
    let C_ ← parse_term "C:bool"
    let D_ ← parse_term "D:bool"
    let T_ ← parse_term "T:bool"
    pure ({ and_tm, A_, B_, C_, D_, T_ } : ImpConv.ImpConvVars) : ExceptT String IO ImpConv.ImpConvVars).run with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"ImpConv vars setup failed: {e}")

/-- The pre-proved theorems `impconv.ml` closes over (proved once). -/
initialize Icd : ImpConv.ImpConvDeps ← do
  match ← (do
    let TAUT (s : String) : ExceptT String IO thm := do
      (Classic.TAUT B C.BOOL_CASES_AX (← parse_term s) : IO (Except String thm))
    let imp_refl ← TAUT "A ==> A"
    let imp_swap ← TAUT "(p ==> q ==> r) <=> (q ==> p ==> r)"
    let IMPLY_AND_RDISTRIB ← TAUT "(x ==> y /\\ z) <=> (x==>y) /\\ (x==>z)"
    let mkimp_iff ← TAUT
      "((A ==> B) ==> (C ==> D)) /\\ ((B ==> A) ==> (D ==> C)) ==> (A <=> B) ==> (C <=> D)"
    let mkimp_contra_iff ← TAUT
      "((A ==> B) ==> C) /\\ ((B ==> A) ==> D) ==> (A <=> B) ==> C /\\ D"
    let mkimpl_contra_iff ← TAUT "((A ==> B) ==> C) ==> (A <=> B) ==> C /\\ (B ==> A)"
    let mkimpr_contra_iff ← TAUT "((B ==> A) ==> D) ==> (A <=> B) ==> (A ==> B) /\\ D"
    let mkimp_co_iff ← TAUT
      "(C ==> A ==> B) /\\ (D ==> B ==> A) ==> C /\\ D ==> (A <=> B)"
    let mkimpl_co_iff ← TAUT "(C ==> A ==> B) ==> C /\\ (B ==> A) ==> (A <=> B)"
    let mkimpr_co_iff ← TAUT "(D ==> B ==> A) ==> (A ==> B) /\\ D ==> (A <=> B)"
    let mkimp_imp_contra_ctxt ← TAUT
      "(B==>A) /\\ (A==>B==>C==>D) ==> (A==>C) ==> (B==>D)"
    let mkimp_imp_co_ctxt ← TAUT "(A==>B) /\\ (A==>B==>D==>C) ==> (B==>D) ==> (A==>C)"
    let mkimpr_imp_ctxt ← TAUT "(A==>C==>D) ==> (A==>C) ==> (A==>D)"
    let mkimp_conj_contra_ctxt ← TAUT "(C==>A==>B) /\\ (A==>B==>C==>D) ==> (A/\\C==>B/\\D)"
    let mkimpl_conj_contra_ctxt ← TAUT "(C==>A==>B) ==> (A/\\C==>B/\\C)"
    let mkimpr_conj_contra_ctxt ← TAUT "(A==>C==>D) ==> (A/\\C==>A/\\D)"
    let mkimp_conj_co_ctxt ← TAUT "(B==>A) /\\ (B==>D==>C) ==> (B/\\D==>A/\\C)"
    let mkimpl_conj_co_ctxt ← TAUT "(B==>A) ==> (B/\\C==>A/\\C)"
    let mkimpl_conj_co2_ctxt ← TAUT "(C==>B==>A) ==> (B/\\C==>A/\\C)"
    -- impconv.ml 1346: REWR_IMPCONV_OF_CONV's IMP_SYM.
    let imp_sym ← TAUT "A ==> B ==> C <=> B ==> A ==> C"
    let case_lem1 ← TAUT "(~P ==> Q = R) ==> (Q <=> (~P ==> R) /\\ (P ==> Q))"
    let case_lem2 ← TAUT "(P ==> Q = R) ==> (Q <=> (P ==> R) /\\ (~P ==> Q))"
    -- impconv.ml 1716: REWR_IMPMCONV_OF_MCONV proves its own IMP_SYM.
    let imp_sym' ← TAUT "A ==> B ==> C <=> B ==> A ==> C"
    pure ({ imp_refl, imp_swap, IMP_CONJ := T.IMP_CONJ, IMP_IMP := T.IMP_IMP, IMPLY_AND_RDISTRIB,
            AND_FORALL_THM := T.AND_FORALL_THM, RIGHT_IMP_FORALL_THM := T.RIGHT_IMP_FORALL_THM,
            CONJ_ASSOC := T.CONJ_ASSOC,
            MONO_AND := T.MONO_AND, MONO_OR := T.MONO_OR, MONO_IMP := T.MONO_IMP,
            MONO_NOT := T.MONO_NOT, MONO_FORALL := T.MONO_FORALL, MONO_EXISTS := T.MONO_EXISTS,
            mkimp_iff, mkimp_contra_iff, mkimpl_contra_iff, mkimpr_contra_iff,
            mkimp_co_iff, mkimpl_co_iff, mkimpr_co_iff,
            mkimp_imp_contra_ctxt, mkimp_imp_co_ctxt, mkimpr_imp_ctxt,
            mkimp_conj_contra_ctxt, mkimpl_conj_contra_ctxt, mkimpr_conj_contra_ctxt,
            mkimp_conj_co_ctxt, mkimpl_conj_co_ctxt, mkimpl_conj_co2_ctxt,
            NOT_FORALL_THM := C.NOT_FORALL_THM, NOT_IMP := C.NOT_IMP, imp_sym, imp_sym',
            LEFT_IMP_EXISTS_THM := T.LEFT_IMP_EXISTS_THM,
            LEFT_FORALL_IMP_THM := T.LEFT_FORALL_IMP_THM,
            case_lem1, case_lem2 } : ImpConv.ImpConvDeps)
      : ExceptT String IO ImpConv.ImpConvDeps).run with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"ImpConv deps setup failed: {e}")

/-- `IMP_REWRITE_TAC ths`: implicational rewriting. -/
def IMP_REWRITE_TAC (ths : List thm) : tactic := ImpConv.IMP_REWRITE_TAC B Icd Icv ths
/-- `SEQ_IMP_REWRITE_TAC ths`. -/
def SEQ_IMP_REWRITE_TAC (ths : List thm) : tactic := ImpConv.SEQ_IMP_REWRITE_TAC B Icd Icv ths
/-- `ASM_IMP_REWRITE_TAC ths`. -/
def ASM_IMP_REWRITE_TAC (ths : List thm) : tactic := ImpConv.ASM_IMP_REWRITE_TAC B Icd Icv ths
/-- `CASE_REWRITE_TAC th`. -/
def CASE_REWRITE_TAC (th : thm) : tactic := ImpConv.CASE_REWRITE_TAC B Icd Icv th
/-- `TARGET_REWRITE_TAC sths th`. -/
def TARGET_REWRITE_TAC (sths : List thm) (th : thm) : tactic :=
  ImpConv.TARGET_REWRITE_TAC B Icd Icv sths th
/-- `HINT_EXISTS_TAC`. -/
def HINT_EXISTS_TAC : tactic := ImpConv.HINT_EXISTS_TAC B Icd Icv

end Session
