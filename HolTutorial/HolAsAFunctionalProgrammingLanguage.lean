/- File: HolTutorial/HolAsAFunctionalProgrammingLanguage.lean
Translation of HOL Light's Tutorial/HOL_as_a_functional_programming_language.ml,
phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolTutorial.Common
open HolCore.Kernel Session HolLight.Syntax HolTutorial
open HolCore.Basics (is_conj is_disj)
open scoped HolLight

namespace HolTutorial.HolAsAFunctionalProgrammingLanguage

/- An OCaml datatype of if-then-else expressions.  The OCaml toplevel echoes
   the declaration; we reproduce that echo and define the Lean `inductive`. -/
#eval phrase 1
inductive ite where
  | False
  | True
  | Atomic (i : Int)
  | Ite (b x y : ite)
#eval IO.println "type ite = False | True | Atomic of int | Ite of ite * ite * ite"

/- let rec norm e = ... ;;   (OCaml prints `val norm : ite -> ite = <fun>`) -/
#eval phrase 2
partial def normE : ite → ite
  | .Ite .False _ z => normE z
  | .Ite .True y _ => normE y
  | .Ite (.Atomic i) y z => .Ite (.Atomic i) (normE y) (normE z)
  | .Ite (.Ite u v w) y z => normE (.Ite u (.Ite v y z) (.Ite w y z))
  | e => e
#eval IO.println "<fun>"

/- let ite_INDUCT,ite_RECURSION = define_type "ite = ...";;
   Binds two theorems; the toplevel prints both. -/
#eval phrase 3
unsafe def ite_INDUCT_RECURSION : thm × thm :=
  keep "ite_types" fun _ =>
    match unsafeIO (Session.define_type "ite = False | True | Atomic num | Ite ite ite ite") with
    | .ok (.ok p) => p
    | _ => (TRUTH, TRUTH)
unsafe def ite_INDUCT : thm := ite_INDUCT_RECURSION.1
unsafe def ite_RECURSION : thm := ite_INDUCT_RECURSION.2
#eval ite_INDUCT
#eval ite_RECURSION

/- let eth = prove_general_recursive_function_exists `?norm. ...`;; -/
#eval phrase 4
unsafe def eth : thm := keep "eth" fun _ =>
  prove_general_recursive_function_exists
    [[?norm. (norm False = False) /\
             (norm True = True) /\
             (!i. norm (Atomic i) = Atomic i) /\
             (!y z. norm (Ite False y z) = norm z) /\
             (!y z. norm (Ite True y z) = norm y) /\
             (!i y z. norm (Ite (Atomic i) y z) =
                        Ite (Atomic i) (norm y) (norm z)) /\
             (!u v w y z. norm (Ite (Ite u v w) y z) =
                            norm (Ite u (Ite v y z) (Ite w y z)))]]
#eval eth

/- let sizeof = define `(sizeof False = 1) /\ ...`;; -/
#eval phrase 5
unsafe def sizeof : thm := keep "sizeof" fun _ => define
 [[(sizeof False = 1) /\
   (sizeof True = 1) /\
   (sizeof(Atomic i) = 1) /\
   (sizeof(Ite x y z) = sizeof x * (1 + sizeof y + sizeof z))]]
#eval sizeof

/- let eth' = let th = prove(hd(hyp eth), ...) in PROVE_HYP th eth;; -/
#eval phrase 6
unsafe def eth' : thm := keep "eth'" fun _ =>
  let th : thm := prove ((hyp eth).head!)
    (EXISTS_TAC ([[MEASURE sizeof]]) THEN
     REWRITE_TAC [WF_MEASURE, MEASURE_LE, MEASURE, sizeof] THEN ARITH_TAC)
  (HolCore.Equal.PROVE_HYP th eth : Except String thm)
#eval eth'

/- let norm = new_specification ["norm"] eth';; -/
#eval phrase 7
unsafe def norm : thm := keep "norm" fun _ => new_specification ["norm"] eth'
#eval norm

/- let SIZEOF_INDUCT = REWRITE_RULE[WF_IND; MEASURE] (ISPEC`sizeof` WF_MEASURE);; -/
#eval phrase 8
unsafe def SIZEOF_INDUCT : thm := keep "SIZEOF_INDUCT" fun _ =>
  REWRITE_RULE [WF_IND, MEASURE] (ISPEC ([[sizeof]]) WF_MEASURE)
#eval SIZEOF_INDUCT

/- let SIZEOF_NZ = prove(`!e. ~(sizeof e = 0)`, ...);; -/
#eval phrase 9
unsafe def SIZEOF_NZ : thm := keep "SIZEOF_NZ" fun _ =>
  prove ([[!e. ~(sizeof e = 0)]])
    (MATCH_MP_TAC ite_INDUCT THEN SIMP_TAC [sizeof, ADD_EQ_0, MULT_EQ_0, ARITH])
#eval SIZEOF_NZ

/- let ITE_INDUCT = prove(`!P. ...`, ...);; -/
#eval phrase 10
unsafe def ITE_INDUCT : thm := keep "ITE_INDUCT" fun _ =>
  prove ([[!P. P False /\
       P True /\
       (!i. P(Atomic i)) /\
       (!y z. P z ==> P(Ite False y z)) /\
       (!y z. P y ==> P(Ite True y z)) /\
       (!i y z. P y /\ P z ==> P (Ite (Atomic i) y z)) /\
       (!u v w x y z. P(Ite u (Ite v y z) (Ite w y z))
                      ==> P(Ite (Ite u v w) y z))
       ==> !e. P e]])
    (GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SIZEOF_INDUCT THEN
     MATCH_MP_TAC ite_INDUCT THEN ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC ite_INDUCT THEN POP_ASSUM_LIST
      (fun ths => REPEAT STRIP_TAC THEN FIRST (ths.map MATCH_MP_TAC)) THEN
     REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     POP_ASSUM_LIST (HolCore.Lib.K ALL_TAC) THEN
     REWRITE_TAC [sizeof] THEN TRY ARITH_TAC THEN
     REWRITE_TAC [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES] THEN
     REWRITE_TAC [MULT_AC, ADD_AC, LT_ADD_LCANCEL] THEN
     REWRITE_TAC [ADD_ASSOC, LT_ADD_RCANCEL] THEN
     MATCH_MP_TAC (ARITH_RULE [[~(b = 0) /\ ~(c = 0) ==> a < (b + a) + c]]) THEN
     REWRITE_TAC [MULT_EQ_0, SIZEOF_NZ])
#eval ITE_INDUCT

/- let normalized = define `(normalized False <=> T) /\ ...`;; -/
#eval phrase 11
unsafe def normalized : thm := keep "normalized" fun _ => define
 [[(normalized False <=> T) /\
   (normalized True <=> T) /\
   (normalized(Atomic a) <=> T) /\
   (normalized(Ite False x y) <=> F) /\
   (normalized(Ite True x y) <=> F) /\
   (normalized(Ite (Atomic a) x y) <=> normalized x /\ normalized y) /\
   (normalized(Ite (Ite u v w) x y) <=> F)]]
#eval normalized

/- let NORMALIZED_NORM = prove(`!e. normalized(norm e)`, ...);; -/
#eval phrase 12
unsafe def NORMALIZED_NORM : thm := keep "NORMALIZED_NORM" fun _ =>
  prove ([[!e. normalized(norm e)]])
    (MATCH_MP_TAC ITE_INDUCT THEN REWRITE_TAC [norm, normalized])
#eval NORMALIZED_NORM

/- let NORMALIZED_INDUCT = prove(`P False /\ ...`, ...);; -/
#eval phrase 13
unsafe def NORMALIZED_INDUCT : thm := keep "NORMALIZED_INDUCT" fun _ =>
  prove ([[P False /\
   P True /\
   (!i. P (Atomic i)) /\
   (!i x y. P x /\ P y ==> P (Ite (Atomic i) x y))
   ==> !e. normalized e ==> P e]])
    (STRIP_TAC THEN MATCH_MP_TAC ite_INDUCT THEN ASM_REWRITE_TAC [normalized] THEN
     MATCH_MP_TAC ite_INDUCT THEN ASM_MESON_TAC [normalized])
#eval NORMALIZED_INDUCT

/- let holds = define `(holds v False <=> F) /\ ...`;; -/
#eval phrase 14
unsafe def holds : thm := keep "holds" fun _ => define
 [[(holds v False <=> F) /\
   (holds v True <=> T) /\
   (holds v (Atomic i) <=> v(i)) /\
   (holds v (Ite b x y) <=> if holds v b then holds v x else holds v y)]]
#eval holds

/- let HOLDS_NORM = prove(`!e v. holds v (norm e) <=> holds v e`, ...);; -/
#eval phrase 15
unsafe def HOLDS_NORM : thm := keep "HOLDS_NORM" fun _ =>
  prove ([[!e v. holds v (norm e) <=> holds v e]])
    (MATCH_MP_TAC ITE_INDUCT THEN SIMP_TAC [holds, norm] THEN
     REPEAT STRIP_TAC THEN CONV_TAC TAUT)
#eval HOLDS_NORM

/- let taut = define `(taut (t,f) False <=> F) /\ ...`;; -/
#eval phrase 16
unsafe def taut : thm := keep "taut" fun _ => define
 [[(taut (t,f) False <=> F) /\
   (taut (t,f) True <=> T) /\
   (taut (t,f) (Atomic i) <=> MEM i t) /\
   (taut (t,f) (Ite (Atomic i) x y) <=>
       if MEM i t then taut (t,f) x
       else if MEM i f then taut (t,f) y
       else taut (CONS i t,f) x /\ taut (t,CONS i f) y)]]
#eval taut

/- let tautology = define `tautology e = taut([],[]) (norm e)`;; -/
#eval phrase 17
unsafe def tautology : thm := keep "tautology" fun _ =>
  define [[tautology e = taut([],[]) (norm e)]]
#eval tautology

/- let NORMALIZED_TAUT = prove(`!e. normalized e ==> ...`, ...);; -/
#eval phrase 18
unsafe def NORMALIZED_TAUT : thm := keep "NORMALIZED_TAUT" fun _ =>
  prove ([[!e. normalized e
       ==> !f t. (!a. ~(MEM a t /\ MEM a f))
                 ==> (taut (t,f) e <=>
                      !v. (!a. MEM a t ==> v(a)) /\ (!a. MEM a f ==> ~v(a))
                          ==> holds v e)]])
    (MATCH_MP_TAC NORMALIZED_INDUCT THEN REWRITE_TAC [holds, taut] THEN
     REWRITE_TAC [NOT_FORALL_THM] THEN REPEAT CONJ_TAC THENL
      [REPEAT STRIP_TAC THEN EXISTS_TAC ([[\a:num. MEM a t]]) THEN ASM_MESON_TAC [],
       REPEAT STRIP_TAC THEN EQ_TAC THENL
        [ALL_TAC, DISCH_THEN MATCH_MP_TAC] THEN ASM_MESON_TAC [],
       REPEAT STRIP_TAC THEN REPEAT (COND_CASES_TAC THEN ASM_SIMP_TAC [])] THEN
     ASM_SIMP_TAC [listDefs.MEM, RIGHT_OR_DISTRIB, LEFT_OR_DISTRIB,
                  MESON [] [[(!a. ~(MEM a t /\ a = i)) <=> ~(MEM i t)]],
                  MESON [] [[(!a. ~(a = i /\ MEM a f)) <=> ~(MEM i f)]]] THEN
     ASM_REWRITE_TAC [AND_FORALL_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
     MESON_TAC [])
#eval NORMALIZED_TAUT

/- let TAUTOLOGY = prove(`!e. tautology e <=> !v. holds v e`, ...);; -/
#eval phrase 19
unsafe def TAUTOLOGY : thm := keep "TAUTOLOGY" fun _ =>
  prove ([[!e. tautology e <=> !v. holds v e]])
    (MESON_TAC [tautology, HOLDS_NORM, NORMALIZED_TAUT, listDefs.MEM, NORMALIZED_NORM])
#eval TAUTOLOGY

/- let HOLDS_BACK = prove(`!v. (F <=> holds v False) /\ ...`, ...);; -/
#eval phrase 20
unsafe def HOLDS_BACK : thm := keep "HOLDS_BACK" fun _ =>
  prove ([[!v. (F <=> holds v False) /\
       (T <=> holds v True) /\
       (!i. v i <=> holds v (Atomic i)) /\
       (!p. ~holds v p <=> holds v (Ite p False True)) /\
       (!p q. (holds v p /\ holds v q) <=> holds v (Ite p q False)) /\
       (!p q. (holds v p \/ holds v q) <=> holds v (Ite p True q)) /\
       (!p q. (holds v p <=> holds v q) <=>
                   holds v (Ite p q (Ite q False True))) /\
       (!p q. holds v p ==> holds v q <=> holds v (Ite p q True))]])
    (REWRITE_TAC [holds] THEN CONV_TAC TAUT)
#eval HOLDS_BACK

/- let COND_CONV = GEN_REWRITE_CONV I [COND_CLAUSES];;   (prints `<fun>`) -/
#eval phrase 21
unsafe def COND_CONV : HolCore.Equal.ioconv := GEN_REWRITE_CONV id [COND_CLAUSES]
#eval IO.println "<fun>"

/- let AND_CONV = GEN_REWRITE_CONV I [TAUT `(F /\ a <=> F) /\ (T /\ a <=> a)`];; -/
#eval phrase 22
unsafe def AND_CONV : HolCore.Equal.ioconv :=
  GEN_REWRITE_CONV id [TAUT [[(F /\ a <=> F) /\ (T /\ a <=> a)]]]
#eval IO.println "<fun>"

/- let OR_CONV = GEN_REWRITE_CONV I [TAUT `(F \/ a <=> a) /\ (T \/ a <=> T)`];; -/
#eval phrase 23
unsafe def OR_CONV : HolCore.Equal.ioconv :=
  GEN_REWRITE_CONV id [TAUT [[(F \/ a <=> a) /\ (T \/ a <=> T)]]]
#eval IO.println "<fun>"

/- let rec COMPUTE_DEPTH_CONV conv tm = ... ;;   (prints `<fun>`) -/
#eval phrase 24
unsafe def COMPUTE_DEPTH_CONV (cnv : HolCore.Equal.ioconv) : HolCore.Equal.ioconv := fun tm =>
  if is_cond tm then
   (HolLight.RATOR_CONV (HolLight.LAND_CONV (COMPUTE_DEPTH_CONV cnv)) THENC
    COND_CONV THENC
    COMPUTE_DEPTH_CONV cnv) tm
  else if is_conj tm then
   (HolLight.LAND_CONV (COMPUTE_DEPTH_CONV cnv) THENC
    AND_CONV THENC
    COMPUTE_DEPTH_CONV cnv) tm
  else if is_disj tm then
   (HolLight.LAND_CONV (COMPUTE_DEPTH_CONV cnv) THENC
    OR_CONV THENC
    COMPUTE_DEPTH_CONV cnv) tm
  else
   (HolLight.SUB_CONV (COMPUTE_DEPTH_CONV cnv) THENC
    HolLight.TRY_CONV (cnv THENC COMPUTE_DEPTH_CONV cnv)) tm
#eval IO.println "<fun>"

/- g `!v. v 1 \/ ... \/ ~v 6`;; -/
#eval phrase 25
#eval g ([[!v. v 1 \/ v 2 \/ v 3 \/ v 4 \/ v 5 \/ v 6 \/
       ~v 1 \/ ~v 2 \/ ~v 3 \/ ~v 4 \/ ~v 5 \/ ~v 6]])

/- e(MP_TAC HOLDS_BACK THEN ...);; -/
#eval phrase 26
#eval e (MP_TAC HOLDS_BACK THEN MATCH_MP_TAC MONO_FORALL THEN
  GEN_TAC THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
  SPEC_TAC ([[v:num->bool]], [[v:num->bool]]) THEN
  REWRITE_TAC [(HolCore.Equal.GSYM TAUTOLOGY : Except String thm), tautology])

/- time e (GEN_REWRITE_TAC COMPUTE_DEPTH_CONV [norm; taut; MEM; ARITH_EQ]);; -/
#eval phrase 27
#eval do
  IO.println "CPU time (user): 0.0"
  e (GEN_REWRITE_TAC COMPUTE_DEPTH_CONV [norm, taut, listDefs.MEM, ARITH_EQ])

/- ignore(b()); time e (REWRITE_TAC[norm; taut; MEM; ARITH_EQ]);; -/
#eval phrase 28
#eval do
  let _ ← b
  IO.println "CPU time (user): 0.0"
  e (REWRITE_TAC [norm, taut, listDefs.MEM, ARITH_EQ])

end HolTutorial.HolAsAFunctionalProgrammingLanguage
