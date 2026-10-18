/- File: HolExamples/Combin.lean
Translation of HOL Light's Examples/combin.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
import HolExamples.Reduct
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionLibrary.RSTC
open HolExamples.Reduct
namespace HolExamples.Combin

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- Run `define_type`, panicking with HOL Light's message on failure. -/
private unsafe def defType (s : String) : thm × thm :=
  match unsafeIO (Session.define_type s) with
  | .ok (.ok p) => p
  | .ok (.error e) => panic! s!"define_type: {e}"
  | .error e => panic! s!"define_type IO: {e}"

/- Run `new_inductive_definition`, panicking with HOL Light's message on
   failure (as the toplevel throws). -/
private unsafe def indDef (tm : term) : thm × thm × thm :=
  match unsafeIO (Session.new_inductive_definition tm) with
  | .ok (.ok t) => t
  | .ok (.error e) => panic! s!"new_inductive_definition: {e}"
  | .error e => panic! s!"new_inductive_definition IO: {e}"

-- ========================================================================= --
-- Church-Rosser property for combinatory logic (S and K combinators).       --
-- ========================================================================= --

#eval phrase 1
-- needs "Examples/reduct.ml";;
#eval HolExamples.Reduct.ensure

#eval phrase 2
-- Definition of confluence.
unsafe def confluent : thm := keep "confluent" fun _ => (do
  ExceptT.mk (define
  [[confluent R <=>
        !x y z. RTC R x y /\ RTC R x z ==> ?u. RTC R y u /\ RTC R z u]])
  : ExceptT String IO thm).run
#eval confluent

#eval phrase 3
unsafe def confluent_diamond_RTC : thm := keep "confluent_diamond_RTC" fun _ => (do
  prove ([[!R. confluent R <=> CR(RTC R)]])
   (REWRITE_TAC [confluent, CR])
  : ExceptT String IO thm).run
#eval confluent_diamond_RTC

#eval phrase 4
-- Basic term structure: S and K combinators and function application ("%").
#eval (parse_as_infix ("%", (20, "left")) : IO Unit)

#eval phrase 5
unsafe def cl_defs : thm × thm :=
  keep "cl_defs" fun _ => defType "cl = S | K | % cl cl"
unsafe def cl_INDUCT : thm := cl_defs.1
unsafe def cl_RECURSION : thm := cl_defs.2
#eval do IO.println (repr cl_INDUCT); IO.println (repr cl_RECURSION)

#eval phrase 6
-- Reduction relation.
#eval (parse_as_infix ("-->", (12, "right")) : IO Unit)

#eval phrase 7
unsafe def redn_defs : thm × thm × thm :=
  keep "redn_defs" fun _ => indDef
    [[(!x y f. x --> y   ==>    f % x --> f % y) /\
      (!f g x. f --> g   ==>    f % x --> g % x) /\
      (!x y.   K % x % y --> x) /\
      (!f g x. S % f % g % x --> (f % x) % (g % x))]]
unsafe def redn_rules : thm := redn_defs.1
unsafe def redn_ind : thm := redn_defs.2.1
unsafe def redn_cases : thm := redn_defs.2.2
#eval do IO.println (repr redn_rules); IO.println (repr redn_ind); IO.println (repr redn_cases)

#eval phrase 8
-- A different, "parallel", reduction relation.
#eval (parse_as_infix ("-||->", (12, "right")) : IO Unit)

#eval phrase 9
unsafe def predn_defs : thm × thm × thm :=
  keep "predn_defs" fun _ => indDef
    [[(!x. x -||-> x) /\
      (!x y u v. x -||-> y /\ u -||-> v ==> x % u -||-> y % v) /\
      (!x y. K % x % y -||-> x) /\
      (!f g x. S % f % g % x -||-> (f % x) % (g % x))]]
unsafe def predn_rules : thm := predn_defs.1
unsafe def predn_ind : thm := predn_defs.2.1
unsafe def predn_cases : thm := predn_defs.2.2
#eval do IO.println (repr predn_rules); IO.println (repr predn_ind); IO.println (repr predn_cases)

#eval phrase 10
-- Abbreviations for their reflexive-transitive closures.
#eval (parse_as_infix ("-->*", (12, "right")) : IO Unit)

#eval phrase 11
#eval (parse_as_infix ("-||->*", (12, "right")) : IO Unit)

#eval phrase 12
unsafe def RTCredn : thm := keep "RTCredn" fun _ => new_definition
  [[(-->*) = RTC(-->)]]
#eval RTCredn

#eval phrase 13
unsafe def RTCpredn : thm := keep "RTCpredn" fun _ => new_definition
  [[(-||->*) = RTC(-||->)]]
#eval RTCpredn

#eval phrase 14
unsafe def RTCredn_rules : thm := keep "RTCredn_rules" fun _ => (do
  let op ← ExceptT.mk (HolCore.Parser.parse_term "(-->)")
  HolLight.REWRITE_RULE [(← HolLight.SYM RTCredn)] (← HolLight.ISPEC op RTC_RULES)
  : ExceptT String IO thm).run
#eval RTCredn_rules

#eval phrase 15
unsafe def RTCredn_ind : thm := keep "RTCredn_ind" fun _ => (do
  let op ← ExceptT.mk (HolCore.Parser.parse_term "(-->)")
  HolLight.REWRITE_RULE [(← HolLight.SYM RTCredn)] (← HolLight.ISPEC op RTC_INDUCT)
  : ExceptT String IO thm).run
#eval RTCredn_ind

#eval phrase 16
unsafe def RTCpredn_rules : thm := keep "RTCpredn_rules" fun _ => (do
  let op ← ExceptT.mk (HolCore.Parser.parse_term "(-||->)")
  HolLight.REWRITE_RULE [(← HolLight.SYM RTCpredn)] (← HolLight.ISPEC op RTC_RULES)
  : ExceptT String IO thm).run
#eval RTCpredn_rules

#eval phrase 17
unsafe def RTCpredn_ind : thm := keep "RTCpredn_ind" fun _ => (do
  let op ← ExceptT.mk (HolCore.Parser.parse_term "(-||->)")
  HolLight.REWRITE_RULE [(← HolLight.SYM RTCpredn)] (← HolLight.ISPEC op RTC_INDUCT)
  : ExceptT String IO thm).run
#eval RTCpredn_ind

#eval phrase 18
-- Prove that the two RTCs are actually the same.
unsafe def RTCredn_RTCpredn : thm := keep "RTCredn_RTCpredn" fun _ => (do
  prove ([[!x y. x -->* y ==> x -||->* y]])
   (REWRITE_TAC [RTCredn, RTCpredn] THEN MATCH_MP_TAC RTC_MONO THEN
    MATCH_MP_TAC redn_ind THEN MESON_TAC [predn_rules])
  : ExceptT String IO thm).run
#eval RTCredn_RTCpredn

#eval phrase 19
unsafe def RTCredn_ap_monotonic : thm := keep "RTCredn_ap_monotonic" fun _ => (do
  prove ([[!x y. x -->* y ==> !z. x % z -->* y % z /\ z % x -->* z % y]])
   (MATCH_MP_TAC RTCredn_ind THEN MESON_TAC [RTCredn_rules, redn_rules])
  : ExceptT String IO thm).run
#eval RTCredn_ap_monotonic

#eval phrase 20
unsafe def predn_RTCredn : thm := keep "predn_RTCredn" fun _ => (do
  prove ([[!x y. x -||-> y ==> x -->* y]])
   (MATCH_MP_TAC predn_ind THEN
    MESON_TAC [RTCredn_rules, redn_rules, RTCredn_ap_monotonic])
  : ExceptT String IO thm).run
#eval predn_RTCredn

#eval phrase 21
unsafe def RTCpredn_RTCredn : thm := keep "RTCpredn_RTCredn" fun _ => (do
  prove ([[!x y. x -||->* y ==> x -->* y]])
   (MATCH_MP_TAC RTCpredn_ind THEN MESON_TAC [predn_RTCredn, RTCredn_rules])
  : ExceptT String IO thm).run
#eval RTCpredn_RTCredn

#eval phrase 22
unsafe def RTCpredn_EQ_RTCredn : thm := keep "RTCpredn_EQ_RTCredn" fun _ => (do
  prove ([[(-||->*) = (-->*)]])
   (REWRITE_TAC [FUN_EQ_THM] THEN MESON_TAC [RTCpredn_RTCredn, RTCredn_RTCpredn])
  : ExceptT String IO thm).run
#eval RTCpredn_EQ_RTCredn

#eval phrase 23
-- Now prove diamond property for "-||->" reduction.
-- let characterise t = SIMP_RULE[...] (SPEC t predn_cases);;
unsafe def characterise (t : term) : ExceptT String IO thm := do
  ExceptT.mk (SIMP_RULE [(← ExceptT.mk (pure (distinctness "cl"))), (← ExceptT.mk (pure (injectivity "cl"))),
             (← HolLight.GSYM EXISTS_REFL),
             RIGHT_EXISTS_AND_THM, (← HolLight.GSYM CONJ_ASSOC), UNWIND_THM1]
   (← HolLight.SPEC t predn_cases))
#eval IO.println "<fun>"

#eval phrase 24
unsafe def Sx_PREDN : thm := keep "Sx_PREDN" fun _ => (do
  prove ([[!x y. S % x -||-> y <=> ?z. y = S % z /\ x -||-> z]])
   (REWRITE_TAC [(← characterise [[S % x]])] THEN
    MESON_TAC [predn_rules, (← characterise [[S]])])
  : ExceptT String IO thm).run
#eval Sx_PREDN

#eval phrase 25
unsafe def Kx_PREDN : thm := keep "Kx_PREDN" fun _ => (do
  prove ([[!x y. K % x -||-> y <=> ?z. y = K % z /\ x -||-> z]])
   (REWRITE_TAC [(← characterise [[K % x]])] THEN
    MESON_TAC [predn_rules, (← characterise [[K]])])
  : ExceptT String IO thm).run
#eval Kx_PREDN

#eval phrase 26
unsafe def Kxy_PREDN : thm := keep "Kxy_PREDN" fun _ => (do
  prove ([[!x y z. K % x % y -||-> z <=>
            (?u v. z = K % u % v /\ x -||-> u /\ y -||-> v) \/ z = x]])
   (REWRITE_TAC [(← characterise [[K % x % y]])] THEN
    MESON_TAC [predn_rules, Kx_PREDN])
  : ExceptT String IO thm).run
#eval Kxy_PREDN

#eval phrase 27
unsafe def Sxy_PREDN : thm := keep "Sxy_PREDN" fun _ => (do
  prove ([[!x y z. S % x % y -||-> z <=>
            ?u v. z = S % u % v /\ x -||-> u /\ y -||-> v]])
   (REWRITE_TAC [(← characterise [[S % x % y]])] THEN
    MESON_TAC [predn_rules, (← characterise [[S]]), Sx_PREDN])
  : ExceptT String IO thm).run
#eval Sxy_PREDN

#eval phrase 28
unsafe def Sxyz_PREDN : thm := keep "Sxyz_PREDN" fun _ => (do
  prove ([[!w x y z. S % w % x % y -||-> z <=>
              (?p q r. z = S % p % q % r /\
                       w -||-> p /\ x -||-> q /\ y -||-> r) \/
              z = (w % y) % (x % y)]])
   (REWRITE_TAC [(← characterise [[S % w % x % y]])] THEN
    MESON_TAC [predn_rules, Sxy_PREDN])
  : ExceptT String IO thm).run
#eval Sxyz_PREDN

#eval phrase 29
unsafe def predn_diamond_lemma : thm := keep "predn_diamond_lemma" fun _ => (do
  prove ([[!x y. x -||-> y ==> !z. x -||-> z ==> ?u. y -||-> u /\ z -||-> u]])
   (ONCE_REWRITE_TAC [(TAUT [[a ==> b <=> a ==> a /\ b]])] THEN
    MATCH_MP_TAC predn_ind THEN SIMP_TAC [predn_rules] THEN REPEAT CONJ_TAC THENL
     [MESON_TAC [predn_rules],
      REPEAT STRIP_TAC THEN UNDISCH_THEN ([[x % u -||-> z]])
       (fun th => HolLight.tactic_of do
         pure (STRIP_ASSUME_TAC (← ExceptT.mk (SIMP_RULE [(← characterise [[x % y]])] th)))) THENL
       [ASM_MESON_TAC [predn_rules],
        ASM_MESON_TAC [predn_rules],
        SUBGOAL_THEN ([[?w. y = K % w /\ z -||-> w]]) MP_TAC,
        SUBGOAL_THEN ([[?p q. y = S % p % q /\ f -||-> p /\ g -||-> q]]) MP_TAC] THEN
      ASM_MESON_TAC [Kx_PREDN, Sxy_PREDN, predn_rules],
      REWRITE_TAC [Kxy_PREDN] THEN MESON_TAC [predn_rules],
      REWRITE_TAC [Sxyz_PREDN] THEN MESON_TAC [predn_rules]])
  : ExceptT String IO thm).run
#eval predn_diamond_lemma

#eval phrase 30
unsafe def predn_diamond : thm := keep "predn_diamond" fun _ => (do
  prove ([[CR (-||->)]])
   (MESON_TAC [CR, predn_diamond_lemma])
  : ExceptT String IO thm).run
#eval predn_diamond

#eval phrase 31
-- Hence we have confluence of the main reduction.
unsafe def confluent_redn : thm := keep "confluent_redn" fun _ => (do
  prove ([[confluent(-->)]])
   (MESON_TAC [confluent_diamond_RTC, RTCpredn_EQ_RTCredn, RTCredn, RTCpredn,
            RTC_CR, predn_diamond])
  : ExceptT String IO thm).run
#eval confluent_redn

end HolExamples.Combin
