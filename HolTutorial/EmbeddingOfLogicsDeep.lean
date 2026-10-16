/- File: HolTutorial/EmbeddingOfLogicsDeep.lean
Translation of HOL Light's Tutorial/Embedding_of_logics_deep.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolTutorial.Common
open HolCore.Kernel HolLight HolLight.Syntax HolTutorial
open HolCore.Tactics (tactic)
open Session (define define_type new_definition parse_as_infix parse_as_prefix
  MESON_TAC ASM_MESON_TAC MONO_FORALL WF_IND ETA_AX FORALL_PAIR_THM)
namespace HolTutorial.EmbeddingOfLogicsDeep

/-- Run `define_type` (an `IO (Except String (thm × thm))`) to its pair,
    panicking with HOL Light's message on failure (as the toplevel throws). -/
unsafe def defType (s : String) : thm × thm :=
  match unsafeIO (define_type s) with
  | .ok (.ok p) => p
  | .ok (.error e) => panic! s!"define_type: {e}"
  | .error e => panic! s!"define_type IO: {e}"

#eval phrase 1
unsafe def string_INDUCT_RECURSION : thm × thm :=
  keep "string_INDUCT_RECURSION" fun _ => defType "string = String num"
unsafe def string_INDUCT : thm := string_INDUCT_RECURSION.1
unsafe def string_RECURSION : thm := string_INDUCT_RECURSION.2
#eval do IO.println string_INDUCT; IO.println string_RECURSION

#eval phrase 2
#eval parse_as_infix ("&&", (16, "right"))

#eval phrase 3
#eval parse_as_infix ("||", (15, "right"))

#eval phrase 4
#eval parse_as_infix ("-->", (14, "right"))

#eval phrase 5
#eval parse_as_infix ("<->", (13, "right"))

#eval phrase 6
#eval parse_as_prefix "Not"

#eval phrase 7
#eval parse_as_prefix "Box"

#eval phrase 8
#eval parse_as_prefix "Diamond"

#eval phrase 9
unsafe def form_INDUCT_RECURSION : thm × thm :=
  keep "form_INDUCT_RECURSION" fun _ =>
    defType "form = False
       | True
       | Atom string
       | Not form
       | && form form
       | || form form
       | --> form form
       | <-> form form
       | Box form
       | Diamond form"
unsafe def form_INDUCT : thm := form_INDUCT_RECURSION.1
unsafe def form_RECURSION : thm := form_INDUCT_RECURSION.2
#eval do IO.println form_INDUCT; IO.println form_RECURSION

#eval phrase 10
unsafe def holds : thm := keep "holds" fun _ => define
 [[(holds (W,R) V False w <=> F) /\
  (holds (W,R) V True w <=> T) /\
  (holds (W,R) V (Atom a) w <=> V a w) /\
  (holds (W,R) V (Not p) w <=> ~(holds (W,R) V p w)) /\
  (holds (W,R) V (p && q) w <=> holds (W,R) V p w /\ holds (W,R) V q w) /\
  (holds (W,R) V (p || q) w <=> holds (W,R) V p w \/ holds (W,R) V q w) /\
  (holds (W,R) V (p --> q) w <=> holds (W,R) V p w ==> holds (W,R) V q w) /\
  (holds (W,R) V (p <-> q) w <=> holds (W,R) V p w <=> holds (W,R) V q w) /\
  (holds (W,R) V (Box p) w <=>
        !w'. w' IN W /\ R w w' ==> holds (W,R) V p w') /\
  (holds (W,R) V (Diamond p) w <=>
        ?w'. w' IN W /\ R w w' /\ holds (W,R) V p w')]]
#eval holds

#eval phrase 11
unsafe def holds_in : thm := keep "holds_in" fun _ => new_definition
 [[holds_in (W,R) p = !V w. w IN W ==> holds (W,R) V p w]]
#eval holds_in

#eval phrase 12
#eval parse_as_infix ("|=", (11, "right"))

#eval phrase 13
unsafe def valid : thm := keep "valid" fun _ => new_definition
 [[L |= p <=> !f. L f ==> holds_in f p]]
#eval valid

#eval phrase 14
unsafe def S4 : thm := keep "S4" fun _ => new_definition
 [[S4(W,R) <=> ~(W = {}) /\ (!x y. R x y ==> x IN W /\ y IN W) /\
              (!x. x IN W ==> R x x) /\
              (!x y z. R x y /\ R y z ==> R x z)]]
#eval S4

#eval phrase 15
unsafe def LTL : thm := keep "LTL" fun _ => new_definition
 [[LTL(W,R) <=> (W = UNIV) /\ !x y:num. R x y <=> x <= y]]
#eval LTL

#eval phrase 16
unsafe def GL : thm := keep "GL" fun _ => new_definition
 [[GL(W,R) <=> ~(W = {}) /\ (!x y. R x y ==> x IN W /\ y IN W) /\
              WF(\x y. R y x) /\ (!x y z:num. R x y /\ R y z ==> R x z)]]
#eval GL

#eval phrase 17
unsafe def MODAL_TAC : tactic :=
  REWRITE_TAC [valid, FORALL_PAIR_THM, holds_in, holds] THEN MESON_TAC []
#eval IO.println "<fun>"

#eval phrase 18
unsafe def MODAL_RULE (tm : term) : IO (Except String thm) := Session.prove tm MODAL_TAC
#eval IO.println "<fun>"

#eval phrase 19
unsafe def TAUT_1 : thm := keep "TAUT_1" fun _ => MODAL_RULE [[L |= Box True]]
#eval TAUT_1

#eval phrase 20
unsafe def TAUT_2 : thm := keep "TAUT_2" fun _ => MODAL_RULE [[L |= Box(A --> B) --> Box A --> Box B]]
#eval TAUT_2

#eval phrase 21
unsafe def TAUT_3 : thm := keep "TAUT_3" fun _ => MODAL_RULE [[L |= Diamond(A --> B) --> Box A --> Diamond B]]
#eval TAUT_3

#eval phrase 22
unsafe def TAUT_4 : thm := keep "TAUT_4" fun _ => MODAL_RULE [[L |= Box(A --> B) --> Diamond A --> Diamond B]]
#eval TAUT_4

#eval phrase 23
unsafe def TAUT_5 : thm := keep "TAUT_5" fun _ => MODAL_RULE [[L |= Box(A && B) --> Box A && Box B]]
#eval TAUT_5

#eval phrase 24
unsafe def TAUT_6 : thm := keep "TAUT_6" fun _ => MODAL_RULE [[L |= Diamond(A || B) --> Diamond A || Diamond B]]
#eval TAUT_6

#eval phrase 25
unsafe def HOLDS_FORALL_LEMMA : thm := keep "HOLDS_FORALL_LEMMA" fun _ => Session.prove
 ([[!W R P. (!A V. P(holds (W,R) V A)) <=> (!p:W->bool. P p)]])
  (tactic_of do
   let atom ← q "Atom a"
   let lam ← q r"\a:string. (p:W->bool)"
   let eta ← GSYM ETA_AX
   pure
    (REPEAT GEN_TAC THEN EQ_TAC THENL [DISCH_TAC THEN GEN_TAC, SIMP_TAC []] THEN
     POP_ASSUM (MP_TAC o SPECL [atom, lam]) THEN
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [eta] THEN
     REWRITE_TAC [holds] THEN REWRITE_TAC [ETA_AX]))
#eval HOLDS_FORALL_LEMMA

#eval phrase 26
unsafe def MODAL_SCHEMA_TAC : tactic :=
  REWRITE_TAC [holds_in, holds] THEN MP_TAC HOLDS_FORALL_LEMMA THEN
  REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN (fun th => REWRITE_TAC [th])
#eval IO.println "<fun>"

#eval phrase 27
unsafe def MODAL_REFL : thm := keep "MODAL_REFL" fun _ => Session.prove
 ([[!W R. (!w:W. w IN W ==> R w w) <=> !A. holds_in (W,R) (Box A --> A)]])
  (MODAL_SCHEMA_TAC THEN MESON_TAC [])
#eval MODAL_REFL

#eval phrase 28
unsafe def MODAL_TRANS : thm := keep "MODAL_TRANS" fun _ => Session.prove
 ([[!W R. (!w w' w'':W. w IN W /\ w' IN W /\ w'' IN W /\
                       R w w' /\ R w' w'' ==> R w w'') <=>
         (!A. holds_in (W,R) (Box A --> Box(Box A)))]])
  (MODAL_SCHEMA_TAC THEN MESON_TAC [])
#eval MODAL_TRANS

#eval phrase 29
unsafe def MODAL_SERIAL : thm := keep "MODAL_SERIAL" fun _ => Session.prove
 ([[!W R. (!w:W. w IN W ==> ?w'. w' IN W /\ R w w') <=>
         (!A. holds_in (W,R) (Box A --> Diamond A))]])
  (MODAL_SCHEMA_TAC THEN MESON_TAC [])
#eval MODAL_SERIAL

#eval phrase 30
unsafe def MODAL_SYM : thm := keep "MODAL_SYM" fun _ => Session.prove
 ([[!W R. (!w w':W. w IN W /\ w' IN W /\ R w w' ==> R w' w) <=>
         (!A. holds_in (W,R) (A --> Box(Diamond A)))]])
  (tactic_of do
   let vw ← q r"\v:W. v = w"
   let w ← q "w:W"
   pure
    (MODAL_SCHEMA_TAC THEN EQ_TAC THENL [MESON_TAC [], REPEAT STRIP_TAC] THEN
     FIRST_X_ASSUM (MP_TAC o SPECL [vw, w]) THEN ASM_MESON_TAC []))
#eval MODAL_SYM

#eval phrase 31
unsafe def MODAL_WFTRANS : thm := keep "MODAL_WFTRANS" fun _ => Session.prove
 ([[!W R. (!x y z:W. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z) /\
         WF(\x y. x IN W /\ y IN W /\ R y x) <=>
         (!A. holds_in (W,R) (Box(Box A --> A) --> Box A))]])
  (tactic_of do
   let w ← q "w:W"
   let lam1 ← q r"\v:W. v IN W /\ R w v /\ !w''. w'' IN W /\ R v w'' ==> R w w''"
   let pw ← q "P:W->bool"
   let lam2 ← q r"\x:W. !w:W. x IN W /\ R w x ==> P x"
   pure
    (MODAL_SCHEMA_TAC THEN REWRITE_TAC [WF_IND] THEN EQ_TAC THEN
     STRIP_TAC THEN REPEAT CONJ_TAC THENL
      [REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC,
       X_GEN_TAC w THEN FIRST_X_ASSUM (MP_TAC o SPECL [lam1, w]),
       X_GEN_TAC pw THEN DISCH_TAC THEN
       FIRST_X_ASSUM (MP_TAC o SPEC lam2) THEN
       MATCH_MP_TAC MONO_FORALL] THEN
     ASM_MESON_TAC []))
#eval MODAL_WFTRANS

end HolTutorial.EmbeddingOfLogicsDeep
