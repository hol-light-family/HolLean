/- File: HolLogicArith/Derived.lean
Translation of HOL Light's Arithmetic/derived.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.Godel
open HolCore.Kernel HolCore.Lib HolCore.Basics Session HolLight.Syntax HolLogicArith
open scoped HolLight
-- Names from Arithmetic/fol.ml that derived.ml reuses.
open HolLogicArith.ArithFol (FV FVT FVT_NUMERAL termsubst formsubst valmod VALMOD
  assign ASSIGN ASSIGN_TRIV TERMSUBST_TRIV TERMSUBST_TRIVIAL FORMSUBST_TRIV FORMSUBST_TRIVIAL
  term_INDUCT form_INDUCT form_RECURSION form_DISTINCT form_INJ
  VARIANT NOT_IN_VARIANT VARIANT_FINITE FV_FINITE FVT_FINITE
  VALMOD_BASIC VALMOD_VALMOD_BASIC VALMOD_SWAP VALMOD_TRIVIAL
  FORMSUBST_FV TERMSUBST_FVT FORMSUBST_SAFE_FOR SAFE_FOR_VALMOD SAFE_FOR_ASSIGN
  SAFE_FOR_V safe_for TERMSUBST_TERMSUBST FORMSUBST_EQ TERMSUBST_EQ
  closed SETMAX SETMAX_MEMBER numeral FV_QSUBST qsubst
  proves_RULES axiom_RULES proves_INDUCT)
-- Names from Arithmetic/definability.ml that derived.ml reuses (phrase 114).
open HolLogicArith.Definability (FV_DIVIDES FV_PRIME FV_PRIMEPOW FV_PRIMREC
  FV_PRIMRECSTEP FV_RTC FV_RTCP)
-- Names from Arithmetic/tarski.ml that derived.ml reuses (phrase 114).
open HolLogicArith.Tarski (FV_DIAGONALIZE FV_FIXPOINT FV_GNUMERAL FV_GNUMERAL1 FV_QDIAG)
-- Names from Arithmetic/arithprov.ml that derived.ml reuses (phrase 114).
open HolLogicArith.ArithProv (FV_AXIOM FV_FORM FV_FORM1 FV_FREEFORM FV_FREEFORM1
  FV_FREETERM FV_FREETERM1 FV_PROV FV_PROV1 FV_TERM FV_TERM1)
-- Names from Arithmetic/godel.ml that derived.ml reuses (phrase 114).
open HolLogicArith.Godel (FV_GSENTENCE FV_HSENTENCE)

namespace HolLogicArith.Derived

/- The session's `prove` lifted into `ExceptT String IO`. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- `new_recursive_definition` lifted into `ExceptT String IO`. -/
private unsafe def newRec (ax : thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (Session.new_recursive_definition ax tm)

-- Replay Arithmetic/godel.ml (the one module derived.ml imports).
#eval HolLogicArith.Godel.ensure

#eval phrase 1
unsafe def negativef : thm := keep "negativef" fun _ => new_definition
  [[negativef p = ?q. p = q --> False]]
#eval negativef

#eval phrase 2
unsafe def negatef : thm := keep "negatef" fun _ => new_definition
  [[negatef p = if negativef p then @q. p = q --> False else p --> False]]
#eval negatef

#eval phrase 3
unsafe def axiom_addimp : thm := keep "axiom_addimp" fun _ => (do
  prove ([[!A p q. A |-- p --> (q --> p)]])
   (MESON_TAC [proves_RULES, axiom_RULES])
  : ExceptT String IO thm).run
#eval axiom_addimp

#eval phrase 4
unsafe def axiom_distribimp : thm := keep "axiom_distribimp" fun _ => (do
  prove ([[!A p q r. A |-- (p --> q --> r) --> (p --> q) --> (p --> r)]])
   (MESON_TAC [proves_RULES, axiom_RULES])
  : ExceptT String IO thm).run
#eval axiom_distribimp

#eval phrase 5
unsafe def axiom_doubleneg : thm := keep "axiom_doubleneg" fun _ => (do
  prove ([[!A p. A |-- ((p --> False) --> False) --> p]])
   (MESON_TAC [proves_RULES, axiom_RULES])
  : ExceptT String IO thm).run
#eval axiom_doubleneg

#eval phrase 6
unsafe def axiom_allimp : thm := keep "axiom_allimp" fun _ => (do
  prove ([[!A x p q. A |-- (!!x (p --> q)) --> (!!x p) --> (!!x q)]])
   (MESON_TAC [proves_RULES, axiom_RULES])
  : ExceptT String IO thm).run
#eval axiom_allimp

#eval phrase 7
unsafe def axiom_impall : thm := keep "axiom_impall" fun _ => (do
  prove ([[!A x p. ~(x IN FV p) ==> A |-- p --> !!x p]])
   (MESON_TAC [proves_RULES, axiom_RULES])
  : ExceptT String IO thm).run
#eval axiom_impall

#eval phrase 8
unsafe def axiom_existseq : thm := keep "axiom_existseq" fun _ => (do
  prove ([[!A x t. ~(x IN FVT t) ==> A |-- ??x (V x === t)]])
   (MESON_TAC [proves_RULES, axiom_RULES])
  : ExceptT String IO thm).run
#eval axiom_existseq

#eval phrase 9
unsafe def axiom_eqrefl : thm := keep "axiom_eqrefl" fun _ => (do
  prove ([[!A t. A |-- t === t]])
   (MESON_TAC [proves_RULES, axiom_RULES])
  : ExceptT String IO thm).run
#eval axiom_eqrefl

#eval phrase 10
unsafe def axiom_funcong : thm := keep "axiom_funcong" fun _ => (do
  prove ([[(!A s t. A |-- s === t --> Suc s === Suc t) /\
   (!A s t u v. A |-- s === t --> u === v --> s ++ u === t ++ v) /\
   (!A s t u v. A |-- s === t --> u === v --> s ** u === t ** v)]])
   (MESON_TAC [proves_RULES, axiom_RULES])
  : ExceptT String IO thm).run
#eval axiom_funcong

#eval phrase 11
unsafe def axiom_predcong : thm := keep "axiom_predcong" fun _ => (do
  prove ([[(!A s t u v. A |-- s === t --> u === v --> s === u --> t === v) /\
   (!A s t u v. A |-- s === t --> u === v --> s << u --> t << v) /\
   (!A s t u v. A |-- s === t --> u === v --> s <<= u --> t <<= v)]])
   (MESON_TAC [proves_RULES, axiom_RULES])
  : ExceptT String IO thm).run
#eval axiom_predcong

#eval phrase 12
unsafe def axiom_iffimp1 : thm := keep "axiom_iffimp1" fun _ => (do
  prove ([[!A p q. A |-- (p <-> q) --> p --> q]])
   (MESON_TAC [proves_RULES, axiom_RULES])
  : ExceptT String IO thm).run
#eval axiom_iffimp1

#eval phrase 13
unsafe def axiom_iffimp2 : thm := keep "axiom_iffimp2" fun _ => (do
  prove ([[!A p q. A |-- (p <-> q) --> q --> p]])
   (MESON_TAC [proves_RULES, axiom_RULES])
  : ExceptT String IO thm).run
#eval axiom_iffimp2

#eval phrase 14
unsafe def axiom_impiff : thm := keep "axiom_impiff" fun _ => (do
  prove ([[!A p q. A |-- (p --> q) --> (q --> p) --> (p <-> q)]])
   (MESON_TAC [proves_RULES, axiom_RULES])
  : ExceptT String IO thm).run
#eval axiom_impiff

#eval phrase 15
unsafe def axiom_true : thm := keep "axiom_true" fun _ => (do
  prove ([[A |-- True <-> (False --> False)]])
   (MESON_TAC [proves_RULES, axiom_RULES])
  : ExceptT String IO thm).run
#eval axiom_true

#eval phrase 16
unsafe def axiom_not : thm := keep "axiom_not" fun _ => (do
  prove ([[!A p. A |-- Not p <-> (p --> False)]])
   (MESON_TAC [proves_RULES, axiom_RULES])
  : ExceptT String IO thm).run
#eval axiom_not

#eval phrase 17
unsafe def axiom_and : thm := keep "axiom_and" fun _ => (do
  prove ([[!A p q. A |-- (p && q) <-> (p --> q --> False) --> False]])
   (MESON_TAC [proves_RULES, axiom_RULES])
  : ExceptT String IO thm).run
#eval axiom_and

#eval phrase 18
unsafe def axiom_or : thm := keep "axiom_or" fun _ => (do
  prove ([[!A p q. A |-- (p || q) <-> Not(Not p && Not q)]])
   (MESON_TAC [proves_RULES, axiom_RULES])
  : ExceptT String IO thm).run
#eval axiom_or

#eval phrase 19
unsafe def axiom_exists : thm := keep "axiom_exists" fun _ => (do
  prove ([[!A x p. A |-- (??x p) <-> Not(!!x (Not p))]])
   (MESON_TAC [proves_RULES, axiom_RULES])
  : ExceptT String IO thm).run
#eval axiom_exists

#eval phrase 20
unsafe def «assume» : thm := keep "assume" fun _ => (do
  prove ([[!A p. p IN A ==> A |-- p]])
   (MESON_TAC [proves_RULES])
  : ExceptT String IO thm).run
#eval «assume»

#eval phrase 21
unsafe def modusponens : thm := keep "modusponens" fun _ => (do
  prove ([[!A p. A |-- (p --> q) /\ A |-- p ==> A |-- q]])
   (MESON_TAC [proves_RULES])
  : ExceptT String IO thm).run
#eval modusponens

#eval phrase 22
unsafe def gen : thm := keep "gen" fun _ => (do
  prove ([[!A p x. A |-- p ==> A |-- !!x p]])
   (MESON_TAC [proves_RULES])
  : ExceptT String IO thm).run
#eval gen

#eval phrase 23
unsafe def iff_imp1 : thm := keep "iff_imp1" fun _ => (do
  prove ([[!A p q. A |-- p <-> q ==> A |-- p --> q]])
   (MESON_TAC [modusponens, axiom_iffimp1])
  : ExceptT String IO thm).run
#eval iff_imp1

#eval phrase 24
unsafe def iff_imp2 : thm := keep "iff_imp2" fun _ => (do
  prove ([[!A p q. A |-- p <-> q ==> A |-- q --> p]])
   (MESON_TAC [modusponens, axiom_iffimp2])
  : ExceptT String IO thm).run
#eval iff_imp2

#eval phrase 25
unsafe def imp_antisym : thm := keep "imp_antisym" fun _ => (do
  prove ([[!A p q. A |-- p --> q /\ A |-- q --> p ==> A |-- p <-> q]])
   (MESON_TAC [modusponens, axiom_impiff])
  : ExceptT String IO thm).run
#eval imp_antisym

#eval phrase 26
unsafe def add_assum : thm := keep "add_assum" fun _ => (do
  prove ([[!A p q. A |-- q ==> A |-- p --> q]])
   (MESON_TAC [modusponens, axiom_addimp])
  : ExceptT String IO thm).run
#eval add_assum

#eval phrase 27
unsafe def imp_refl : thm := keep "imp_refl" fun _ => (do
  prove ([[!A p. A |-- p --> p]])
   (MESON_TAC [modusponens, axiom_distribimp, axiom_addimp])
  : ExceptT String IO thm).run
#eval imp_refl

#eval phrase 28
unsafe def imp_add_assum : thm := keep "imp_add_assum" fun _ => (do
  prove ([[!A p q r. A |-- q --> r ==> A |-- (p --> q) --> (p --> r)]])
   (MESON_TAC [modusponens, axiom_distribimp, add_assum])
  : ExceptT String IO thm).run
#eval imp_add_assum

#eval phrase 29
unsafe def imp_unduplicate : thm := keep "imp_unduplicate" fun _ => (do
  prove ([[!A p q. A |-- p --> p --> q ==> A |-- p --> q]])
   (MESON_TAC [modusponens, axiom_distribimp, imp_refl])
  : ExceptT String IO thm).run
#eval imp_unduplicate

#eval phrase 30
unsafe def imp_trans : thm := keep "imp_trans" fun _ => (do
  prove ([[!A p q. A |-- p --> q /\ A |-- q --> r ==> A |-- p --> r]])
   (MESON_TAC [modusponens, imp_add_assum])
  : ExceptT String IO thm).run
#eval imp_trans

#eval phrase 31
unsafe def imp_swap : thm := keep "imp_swap" fun _ => (do
  prove ([[!A p q r. A |-- p --> q --> r ==> A |-- q --> p --> r]])
   (MESON_TAC [imp_trans, axiom_addimp, modusponens, axiom_distribimp])
  : ExceptT String IO thm).run
#eval imp_swap

#eval phrase 32
unsafe def imp_trans_chain_2 : thm := keep "imp_trans_chain_2" fun _ => (do
  prove ([[!A p q1 q2 r. A |-- p --> q1 /\ A |-- p --> q2 /\ A |-- q1 --> q2 --> r
                 ==> A |-- p --> r]])
   (ASM_MESON_TAC [imp_trans, imp_swap, imp_unduplicate])
  : ExceptT String IO thm).run
#eval imp_trans_chain_2

#eval phrase 33
unsafe def imp_trans_th : thm := keep "imp_trans_th" fun _ => (do
  prove ([[!A p q r. A |-- (q --> r) --> (p --> q) --> (p --> r)]])
   (MESON_TAC [imp_trans, axiom_addimp, axiom_distribimp])
  : ExceptT String IO thm).run
#eval imp_trans_th

#eval phrase 34
unsafe def imp_add_concl : thm := keep "imp_add_concl" fun _ => (do
  prove ([[!A p q r. A |-- p --> q ==> A |-- (q --> r) --> (p --> r)]])
   (MESON_TAC [modusponens, imp_swap, imp_trans_th])
  : ExceptT String IO thm).run
#eval imp_add_concl

#eval phrase 35
unsafe def imp_trans2 : thm := keep "imp_trans2" fun _ => (do
  prove ([[!A p q r s. A |-- p --> q --> r /\ A |-- r --> s ==> A |-- p --> q --> s]])
   (MESON_TAC [imp_add_assum, modusponens, imp_trans_th])
  : ExceptT String IO thm).run
#eval imp_trans2

#eval phrase 36
unsafe def imp_swap_th : thm := keep "imp_swap_th" fun _ => (do
  prove ([[!A p q r. A |-- (p --> q --> r) --> (q --> p --> r)]])
   (MESON_TAC [imp_trans, axiom_distribimp, imp_add_concl, axiom_addimp])
  : ExceptT String IO thm).run
#eval imp_swap_th

#eval phrase 37
unsafe def contrapos : thm := keep "contrapos" fun _ => (do
  prove ([[!A p q. A |-- p --> q ==> A |-- Not q --> Not p]])
   (MESON_TAC [imp_trans, iff_imp1, axiom_not, imp_add_concl, iff_imp2])
  : ExceptT String IO thm).run
#eval contrapos

#eval phrase 38
unsafe def imp_truefalse : thm := keep "imp_truefalse" fun _ => (do
  prove ([[!p q. A |-- (q --> False) --> p --> (p --> q) --> False]])
   (MESON_TAC [imp_trans, imp_trans_th, imp_swap_th])
  : ExceptT String IO thm).run
#eval imp_truefalse

#eval phrase 39
unsafe def imp_insert : thm := keep "imp_insert" fun _ => (do
  prove ([[!A p q r. A |-- p --> r ==> A |-- p --> q --> r]])
   (MESON_TAC [imp_trans, axiom_addimp])
  : ExceptT String IO thm).run
#eval imp_insert

#eval phrase 40
unsafe def imp_mono_th : thm := keep "imp_mono_th" fun _ => (do
  prove ([[A |-- (p' --> p) --> (q --> q') --> (p --> q) --> (p' --> q')]])
   (MESON_TAC [imp_trans, imp_swap, imp_trans_th])
  : ExceptT String IO thm).run
#eval imp_mono_th

#eval phrase 41
unsafe def ex_falso : thm := keep "ex_falso" fun _ => (do
  prove ([[!A p. A |-- False --> p]])
   (MESON_TAC [imp_trans, axiom_addimp, axiom_doubleneg])
  : ExceptT String IO thm).run
#eval ex_falso

#eval phrase 42
unsafe def imp_contr : thm := keep "imp_contr" fun _ => (do
  prove ([[!A p q. A |-- (p --> False) --> (p --> r)]])
   (MESON_TAC [imp_add_assum, ex_falso])
  : ExceptT String IO thm).run
#eval imp_contr

#eval phrase 43
unsafe def imp_contrf : thm := keep "imp_contrf" fun _ => (do
  prove ([[!A p r. A |-- p --> negatef p --> r]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [negatef, negativef] THEN
    COND_CASES_TAC THEN POP_ASSUM STRIP_ASSUME_TAC THEN
    ASM_REWRITE_TAC [form_INJ] THEN
    ASM_MESON_TAC [imp_contr, imp_swap])
  : ExceptT String IO thm).run
#eval imp_contrf

#eval phrase 44
unsafe def contrad : thm := keep "contrad" fun _ => (do
  prove ([[!A p. A |-- (p --> False) --> p ==> A |-- p]])
   (MESON_TAC [modusponens, axiom_distribimp, imp_refl, axiom_doubleneg])
  : ExceptT String IO thm).run
#eval contrad

#eval phrase 45
unsafe def bool_cases : thm := keep "bool_cases" fun _ => (do
  prove ([[!p q. A |-- p --> q /\ A |-- (p --> False) --> q ==> A |-- q]])
   (MESON_TAC [contrad, imp_trans, imp_add_concl])
  : ExceptT String IO thm).run
#eval bool_cases

#eval phrase 46
unsafe def imp_false_rule : thm := keep "imp_false_rule" fun _ => (do
  prove ([[!p q r. A |-- (q --> False) --> p --> r
           ==> A |-- ((p --> q) --> False) --> r]])
   (MESON_TAC [imp_add_concl, imp_add_assum, ex_falso, axiom_addimp, imp_swap,
            imp_trans, axiom_doubleneg, imp_unduplicate])
  : ExceptT String IO thm).run
#eval imp_false_rule

#eval phrase 47
unsafe def imp_true_rule : thm := keep "imp_true_rule" fun _ => (do
  prove ([[!A p q r. A |-- (p --> False) --> r /\ A |-- q --> r
             ==> A |-- (p --> q) --> r]])
   (MESON_TAC [imp_insert, imp_swap, modusponens, imp_trans_th, bool_cases])
  : ExceptT String IO thm).run
#eval imp_true_rule

#eval phrase 48
unsafe def truth : thm := keep "truth" fun _ => (do
  prove ([[!A. A |-- True]])
   (MESON_TAC [modusponens, axiom_true, imp_refl, iff_imp2])
  : ExceptT String IO thm).run
#eval truth

#eval phrase 49
unsafe def and_left : thm := keep "and_left" fun _ => (do
  prove ([[!A p q. A |-- p && q --> p]])
   (MESON_TAC [imp_add_assum, axiom_addimp, imp_trans, imp_add_concl,
            axiom_doubleneg, imp_trans, iff_imp1, axiom_and])
  : ExceptT String IO thm).run
#eval and_left

#eval phrase 50
unsafe def and_right : thm := keep "and_right" fun _ => (do
  prove ([[!A p q. A |-- p && q --> q]])
   (MESON_TAC [axiom_addimp, imp_trans, imp_add_concl, axiom_doubleneg,
            iff_imp1, axiom_and])
  : ExceptT String IO thm).run
#eval and_right

#eval phrase 51
unsafe def and_pair : thm := keep "and_pair" fun _ => (do
  prove ([[!A p q. A |-- p --> q --> p && q]])
   (MESON_TAC [iff_imp2, axiom_and, imp_swap_th, imp_add_assum, imp_trans2,
            modusponens, imp_swap, imp_refl])
  : ExceptT String IO thm).run
#eval and_pair

#eval phrase 52
unsafe def META_AND : thm := keep "META_AND" fun _ => (do
  prove ([[!A p q. A |-- p && q <=> A |-- p /\ A |-- q]])
   (MESON_TAC [and_left, and_right, and_pair, modusponens])
  : ExceptT String IO thm).run
#eval META_AND

#eval phrase 53
unsafe def shunt : thm := keep "shunt" fun _ => (do
  prove ([[!A p q r. A |-- p && q --> r ==> A |-- p --> q --> r]])
   (MESON_TAC [modusponens, imp_add_assum, and_pair])
  : ExceptT String IO thm).run
#eval shunt

#eval phrase 54
unsafe def ante_conj : thm := keep "ante_conj" fun _ => (do
  prove ([[!A p q r. A |-- p --> q --> r ==> A |-- p && q --> r]])
   (MESON_TAC [imp_trans_chain_2, and_left, and_right])
  : ExceptT String IO thm).run
#eval ante_conj

#eval phrase 55
unsafe def not_not_false : thm := keep "not_not_false" fun _ => (do
  prove ([[!A p. A |-- (p --> False) --> False <-> p]])
   (MESON_TAC [imp_antisym, axiom_doubleneg, imp_swap, imp_refl])
  : ExceptT String IO thm).run
#eval not_not_false

#eval phrase 56
unsafe def iff_sym : thm := keep "iff_sym" fun _ => (do
  prove ([[!A p q. A |-- p <-> q <=> A |-- q <-> p]])
   (MESON_TAC [iff_imp1, iff_imp2, imp_antisym])
  : ExceptT String IO thm).run
#eval iff_sym

#eval phrase 57
unsafe def iff_trans : thm := keep "iff_trans" fun _ => (do
  prove ([[!A p q r. A |-- p <-> q /\ A |-- q <-> r ==> A |-- p <-> r]])
   (MESON_TAC [iff_imp1, iff_imp2, imp_trans, imp_antisym])
  : ExceptT String IO thm).run
#eval iff_trans

#eval phrase 58
unsafe def not_not : thm := keep "not_not" fun _ => (do
  prove ([[!A p. A |-- Not(Not p) <-> p]])
   (MESON_TAC [iff_trans, not_not_false, axiom_not, imp_antisym, imp_add_concl,
            iff_imp1, iff_imp2])
  : ExceptT String IO thm).run
#eval not_not

#eval phrase 59
unsafe def contrapos_eq : thm := keep "contrapos_eq" fun _ => (do
  prove ([[!A p q. A |-- Not p --> Not q <=> A |-- q --> p]])
   (MESON_TAC [contrapos, not_not, iff_imp1, iff_imp2, imp_trans])
  : ExceptT String IO thm).run
#eval contrapos_eq

#eval phrase 60
unsafe def or_left : thm := keep "or_left" fun _ => (do
  prove ([[!A p q. A |-- q --> p || q]])
   (MESON_TAC [imp_trans, not_not, iff_imp2, and_right, contrapos, axiom_or])
  : ExceptT String IO thm).run
#eval or_left

#eval phrase 61
unsafe def or_right : thm := keep "or_right" fun _ => (do
  prove ([[!A p q. A |-- p --> p || q]])
   (MESON_TAC [imp_trans, not_not, iff_imp2, and_left, contrapos, axiom_or])
  : ExceptT String IO thm).run
#eval or_right

#eval phrase 62
unsafe def ante_disj : thm := keep "ante_disj" fun _ => (do
  prove ([[!A p q r. A |-- p --> r /\ A |-- q --> r
             ==> A |-- p || q --> r]])
   (HolLight.tactic_of do
     let gce ← HolLight.GSYM contrapos_eq
     pure
      (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [gce] THEN
       MESON_TAC [imp_trans, imp_trans_chain_2, and_pair, contrapos_eq, not_not,
                axiom_or, iff_imp1, iff_imp2, imp_trans]))
  : ExceptT String IO thm).run
#eval ante_disj

#eval phrase 63
unsafe def iff_def : thm := keep "iff_def" fun _ => (do
  prove ([[!A p q. A |-- (p <-> q) <-> (p --> q) && (q --> p)]])
   (MESON_TAC [imp_antisym, imp_trans_chain_2, axiom_iffimp1, axiom_iffimp2,
            and_pair, axiom_impiff, imp_trans_chain_2, and_left, and_right])
  : ExceptT String IO thm).run
#eval iff_def

#eval phrase 64
unsafe def iff_refl : thm := keep "iff_refl" fun _ => (do
  prove ([[!A p. A |-- p <-> p]])
   (MESON_TAC [imp_antisym, imp_refl])
  : ExceptT String IO thm).run
#eval do IO.println iff_refl

#eval phrase 65
unsafe def eq_sym : thm := keep "eq_sym" fun _ => (do
  prove ([[!A s t. A |-- s === t --> t === s]])
   (MESON_TAC [axiom_eqrefl, modusponens, imp_swap, axiom_predcong])
  : ExceptT String IO thm).run
#eval eq_sym

#eval phrase 66
unsafe def icongruence_general : thm := keep "icongruence_general" fun _ => (do
  prove ([[!A p x s t tm.
     A |-- s === t -->
           termsubst ((x |-> s) v) tm === termsubst ((x |-> t) v) tm]])
   (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC [termsubst] THEN
    REPEAT CONJ_TAC THENL
     [MESON_TAC [axiom_eqrefl, add_assum],
      GEN_TAC THEN REWRITE_TAC [valmod] THEN
      COND_CASES_TAC THEN REWRITE_TAC [imp_refl] THEN
      MESON_TAC [axiom_eqrefl, add_assum],
      MESON_TAC [imp_trans, axiom_funcong],
      MESON_TAC [imp_trans, axiom_funcong, imp_swap, imp_unduplicate],
      MESON_TAC [imp_trans, axiom_funcong, imp_swap, imp_unduplicate]])
  : ExceptT String IO thm).run
#eval icongruence_general

#eval phrase 67
unsafe def icongruence : thm := keep "icongruence" fun _ => (do
  prove ([[!A x s t tm.
     A |-- s === t --> termsubst (x |=> s) tm === termsubst (x |=> t) tm]])
   (REWRITE_TAC [assign, icongruence_general])
  : ExceptT String IO thm).run
#eval icongruence

#eval phrase 68
unsafe def icongruence_var : thm := keep "icongruence_var" fun _ => (do
  prove ([[!A x t tm.
     A |-- V x === t --> tm === termsubst (x |=> t) tm]])
   (MESON_TAC [icongruence, TERMSUBST_TRIV, ASSIGN_TRIV])
  : ExceptT String IO thm).run
#eval icongruence_var

#eval phrase 69
unsafe def gen_right : thm := keep "gen_right" fun _ => (do
  prove ([[!A x p q. ~(x IN FV(p)) /\ A |-- p --> q
             ==> A |-- p --> !!x q]])
   (MESON_TAC [axiom_allimp, modusponens, gen, imp_trans, axiom_impall])
  : ExceptT String IO thm).run
#eval gen_right

#eval phrase 70
unsafe def genimp : thm := keep "genimp" fun _ => (do
  prove ([[!x p q. A |-- p --> q ==> A |-- (!!x p) --> (!!x q)]])
   (MESON_TAC [modusponens, axiom_allimp, gen])
  : ExceptT String IO thm).run
#eval genimp

#eval phrase 71
unsafe def eximp : thm := keep "eximp" fun _ => (do
  prove ([[!x p q. A |-- p --> q ==> A |-- (??x p) --> (??x q)]])
   (MESON_TAC [contrapos, genimp, contrapos, imp_trans, iff_imp1, iff_imp2,
            axiom_exists])
  : ExceptT String IO thm).run
#eval eximp

#eval phrase 72
unsafe def exists_imp : thm := keep "exists_imp" fun _ => (do
  prove ([[!A x p q. A |-- ??x (p --> q) /\ ~(x IN FV(q)) ==> A |-- (!!x p) --> q]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[A |-- (q --> False) --> !!x (p --> Not(p --> q))]])
    ASSUME_TAC THENL
     [MATCH_MP_TAC gen_right THEN
      ASM_REWRITE_TAC [FV, IN_UNION, NOT_IN_EMPTY] THEN
      ASM_MESON_TAC [iff_imp2, axiom_not, imp_trans2, imp_truefalse],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[A |-- (q --> False) --> !!x p --> !!x (Not(p --> q))]])
    ASSUME_TAC THENL
     [ASM_MESON_TAC [imp_trans, axiom_allimp], ALL_TAC] THEN
    SUBGOAL_THEN ([[A |-- ((q --> False) --> !!x (Not(p --> q)))
                      --> (q --> False) --> False]])
    ASSUME_TAC THENL
     [ASM_MESON_TAC [modusponens, iff_imp1, axiom_exists, axiom_not, imp_trans_th],
      ALL_TAC] THEN
    ASM_MESON_TAC [imp_trans, imp_swap, axiom_doubleneg])
  : ExceptT String IO thm).run
#eval exists_imp

#eval phrase 73
unsafe def subspec : thm := keep "subspec" fun _ => (do
  prove ([[!A x t p q. ~(x IN FVT(t)) /\ ~(x IN FV(q)) /\ A |-- V x === t --> p --> q
               ==> A |-- (!!x p) --> q]])
   (MESON_TAC [exists_imp, modusponens, eximp, axiom_existseq])
  : ExceptT String IO thm).run
#eval subspec

#eval phrase 74
unsafe def subalpha : thm := keep "subalpha" fun _ => (do
  prove ([[!A x y p q. ((x = y) \/ ~(x IN FV(q)) /\ ~(y IN FV(p))) /\
               A |-- V x === V y --> p --> q
               ==> A |-- (!!x p) --> (!!y q)]])
   (REPEAT GEN_TAC THEN ASM_CASES_TAC ([[x = y:num]]) THEN ASM_REWRITE_TAC [] THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_MESON_TAC [genimp, modusponens, axiom_eqrefl],
      ALL_TAC] THEN
    MATCH_MP_TAC gen_right THEN ASM_REWRITE_TAC [FV, IN_DELETE] THEN
    MATCH_MP_TAC subspec THEN EXISTS_TAC ([[V y]]) THEN
    ASM_REWRITE_TAC [FVT, IN_SING])
  : ExceptT String IO thm).run
#eval subalpha

#eval phrase 75
unsafe def complexity : thm := keep "complexity" fun _ => (do
  newRec form_RECURSION
    [[(complexity False = 1) /\
   (complexity True = 1) /\
   (!s t. complexity (s === t) = 1) /\
   (!s t. complexity (s << t) = 1) /\
   (!s t. complexity (s <<= t) = 1) /\
   (!p. complexity (Not p) = complexity p + 3) /\
   (!p q. complexity (p && q) = complexity p + complexity q + 6) /\
   (!p q. complexity (p || q) = complexity p + complexity q + 16) /\
   (!p q. complexity (p --> q) = complexity p + complexity q + 1) /\
   (!p q. complexity (p <-> q) = 2 * (complexity p + complexity q) + 9) /\
   (!x p. complexity (!!x p) = complexity p + 1) /\
   (!x p. complexity (??x p) = complexity p + 8)]]
  : ExceptT String IO thm).run
#eval complexity

#eval phrase 76
unsafe def COMPLEXITY_FORMSUBST : thm := keep "COMPLEXITY_FORMSUBST" fun _ => (do
  prove ([[!p i. complexity(formsubst i p) = complexity p]])
   (MATCH_MP_TAC form_INDUCT THEN
    SIMP_TAC [formsubst, complexity, LET_DEF, LET_END_DEF])
  : ExceptT String IO thm).run
#eval COMPLEXITY_FORMSUBST

#eval phrase 77
unsafe def isubst_general : thm := keep "isubst_general" fun _ => (do
  prove ([[!A p x v s t. A |-- s === t
                       --> formsubst ((x |-> s) v) p
                           --> formsubst ((x |-> t) v) p]])
   (HolLight.tactic_of do
     let ar1 ← ExceptT.mk (ARITH_RULE [[p < p + q + 1 /\ q < p + q + 1]])
     let ar2 ← ExceptT.mk (ARITH_RULE [[a < b + 1 <=> a <= b]])
     pure
      (GEN_TAC THEN GEN_TAC THEN WF_INDUCT_TAC [[complexity p]] THEN
       POP_ASSUM MP_TAC THEN SPEC_TAC ([[p:form]], [[p:form]]) THEN
       MATCH_MP_TAC form_INDUCT THEN REWRITE_TAC [formsubst, complexity] THEN
       REPEAT CONJ_TAC THENL
        [MESON_TAC [imp_refl, add_assum],
         MESON_TAC [imp_refl, add_assum],
         MESON_TAC [imp_trans_chain_2, axiom_predcong, icongruence_general],
         MESON_TAC [imp_trans_chain_2, axiom_predcong, icongruence_general],
         MESON_TAC [imp_trans_chain_2, axiom_predcong, icongruence_general],
         X_GEN_TAC ([[p:form]]) THEN DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
         DISCH_THEN (MP_TAC oTIO HolLight.SPEC [[p --> False]]) THEN
         REWRITE_TAC [complexity] THEN ANTS_TAC THENL [ARITH_TAC, ALL_TAC] THEN
         REWRITE_TAC [formsubst] THEN
         MESON_TAC [axiom_not, iff_imp1, iff_imp2, imp_swap, imp_trans, imp_trans2],
         MAP_EVERY X_GEN_TAC [ [[p:form]], [[q:form]] ] THEN DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
         DISCH_THEN (MP_TAC oTIO HolLight.SPEC [[(p --> q --> False) --> False]]) THEN
         REWRITE_TAC [complexity] THEN ANTS_TAC THENL [ARITH_TAC, ALL_TAC] THEN
         REWRITE_TAC [formsubst] THEN
         MESON_TAC [axiom_and, iff_imp1, iff_imp2, imp_swap, imp_trans, imp_trans2],
         MAP_EVERY X_GEN_TAC [ [[p:form]], [[q:form]] ] THEN DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
         DISCH_THEN (MP_TAC oTIO HolLight.SPEC [[Not(Not p && Not q)]]) THEN
         REWRITE_TAC [complexity] THEN ANTS_TAC THENL [ARITH_TAC, ALL_TAC] THEN
         REWRITE_TAC [formsubst] THEN
         MESON_TAC [axiom_or, iff_imp1, iff_imp2, imp_swap, imp_trans, imp_trans2],
         MAP_EVERY X_GEN_TAC [ [[p:form]], [[q:form]] ] THEN DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
         DISCH_THEN (fun th => HolLight.tactic_of do
           let sp ← HolLight.SPEC ([[p:form]]) th
           let sq ← HolLight.SPEC ([[q:form]]) th
           pure (MP_TAC sp THEN MP_TAC sq)) THEN
         REWRITE_TAC [ar1] THEN
         MESON_TAC [imp_mono_th, eq_sym, imp_trans, imp_trans_chain_2],
         MAP_EVERY X_GEN_TAC [ [[p:form]], [[q:form]] ] THEN DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
         DISCH_THEN (MP_TAC oTIO HolLight.SPEC [[(p --> q) && (q --> p)]]) THEN
         REWRITE_TAC [complexity] THEN ANTS_TAC THENL [ARITH_TAC, ALL_TAC] THEN
         REWRITE_TAC [formsubst] THEN
         MESON_TAC [iff_def, iff_imp1, iff_imp2, imp_swap, imp_trans, imp_trans2],
         ALL_TAC,
         MAP_EVERY X_GEN_TAC [ [[x:num]], [[p:form]] ] THEN DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
         DISCH_THEN (MP_TAC oTIO HolLight.SPEC [[Not(!!x (Not p))]]) THEN
         REWRITE_TAC [complexity] THEN ANTS_TAC THENL [ARITH_TAC, ALL_TAC] THEN
         REWRITE_TAC [formsubst] THEN
         REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
         REWRITE_TAC [FV] THEN REPEAT LET_TAC THEN
         ASM_MESON_TAC [axiom_exists, iff_imp1, iff_imp2, imp_swap, imp_trans,
                    imp_trans2]] THEN
       MAP_EVERY X_GEN_TAC [ [[u:num]], [[p:form]] ] THEN DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
       REWRITE_TAC [ar2] THEN DISCH_TAC THEN
       MAP_EVERY X_GEN_TAC [ [[v:num]], [[i:num->term]], [[s:term]], [[t:term]] ] THEN
       MAP_EVERY ABBREV_TAC
        [ [[x = if ?y. y IN FV (!! u p) /\ u IN FVT ((v |-> s) i y)
         then VARIANT (FV (formsubst ((u |-> V u) ((v |-> s) i)) p))
         else u]],
          [[y = if ?y. y IN FV (!! u p) /\ u IN FVT ((v |-> t) i y)
         then VARIANT (FV (formsubst ((u |-> V u) ((v |-> t) i)) p))
         else u]] ] THEN
       REWRITE_TAC [LET_DEF, LET_END_DEF] THEN
       SUBGOAL_THEN ([[~(x IN FV(formsubst ((v |-> s) i) (!!u p))) /\
                ~(y IN FV(formsubst ((v |-> t) i) (!!u p)))]])
       STRIP_ASSUME_TAC THENL
        [MAP_EVERY EXPAND_TAC ["x", "y"] THEN CONJ_TAC THEN
         (COND_CASES_TAC THENL
            [ALL_TAC, ASM_REWRITE_TAC [FORMSUBST_FV, IN_ELIM_THM]] THEN
           MATCH_MP_TAC NOT_IN_VARIANT THEN REWRITE_TAC [FV_FINITE] THEN
           REWRITE_TAC [SUBSET, FORMSUBST_FV, IN_ELIM_THM, FV, IN_DELETE] THEN
           REWRITE_TAC [valmod] THEN MESON_TAC [FVT, IN_SING]),
         ALL_TAC] THEN
       ASM_CASES_TAC ([[v:num = u]]) THENL
        [ASM_REWRITE_TAC [VALMOD_VALMOD_BASIC] THEN
         MATCH_MP_TAC add_assum THEN MATCH_MP_TAC subalpha THEN
         ASM_SIMP_TAC [LE_REFL] THEN
         ASM_CASES_TAC ([[y:num = x]]) THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
          [UNDISCH_TAC [[~(x IN FV (formsubst ((v |-> s) i) (!! u p)))]],
           UNDISCH_TAC [[~(y IN FV (formsubst ((v |-> t) i) (!! u p)))]]] THEN
         ASM_REWRITE_TAC [FORMSUBST_FV, FV, IN_ELIM_THM, IN_DELETE] THEN
         MATCH_MP_TAC MONO_NOT THEN MATCH_MP_TAC MONO_EXISTS THEN
         X_GEN_TAC ([[w:num]]) THEN ASM_CASES_TAC ([[w:num = u]]) THEN
         ASM_REWRITE_TAC [VALMOD_BASIC, FVT, IN_SING] THEN
         ASM_REWRITE_TAC [valmod, FVT, IN_SING],
         ALL_TAC] THEN
       SUBGOAL_THEN
        ([[?z. ~(z IN FVT s) /\ ~(z IN FVT t) /\
        A |-- !!x (formsubst ((u |-> V x) ((v |-> s) i)) p)
              --> !!z (formsubst ((u |-> V z) ((v |-> s) i)) p) /\
        A |-- !!z (formsubst ((u |-> V z) ((v |-> t) i)) p)
              --> !!y (formsubst ((u |-> V y) ((v |-> t) i)) p)]])
       MP_TAC THENL
        [ALL_TAC,
         DISCH_THEN (X_CHOOSE_THEN ([[z:num]]) STRIP_ASSUME_TAC) THEN
         MATCH_MP_TAC imp_trans THEN
         EXISTS_TAC ([[(!!z (formsubst ((v |-> s) ((u |-> V z) i)) p))
                     --> (!!z (formsubst ((v |-> t) ((u |-> V z) i)) p))]]) THEN
         CONJ_TAC THENL
          [MATCH_MP_TAC imp_trans THEN
           EXISTS_TAC ([[!!z (formsubst ((v |-> s) ((u |-> V z) i)) p
                       --> formsubst ((v |-> t) ((u |-> V z) i)) p)]]) THEN
           REWRITE_TAC [axiom_allimp] THEN
           ASM_SIMP_TAC [complexity, LE_REFL, FV, IN_UNION, gen_right],
           ALL_TAC] THEN
         FIRST_ASSUM (fun th => HolLight.tactic_of do
           let sw ← HolLight.MATCH_MP VALMOD_SWAP th
           pure (ONCE_REWRITE_TAC [sw])) THEN
         ASM_MESON_TAC [imp_mono_th, modusponens]] THEN
       (HolLight.tactic_of do
         let vf ← HolLight.SPEC
          ([[FVT(s) UNION FVT(t) UNION
    FV(formsubst ((u |-> V x) ((v |-> s) i)) p) UNION
    FV(formsubst ((u |-> V y) ((v |-> t) i)) p)]]) VARIANT_FINITE
         pure (MP_TAC vf)) THEN
       REWRITE_TAC [FINITE_UNION, FV_FINITE, FVT_FINITE] THEN
       HolCore.Lib.W (fun g => HolLight.tactic_of do
         let w := HolLight.snd g
         let a ← liftExcept (do HolCore.Equal.lhand (← rand (← HolCore.Equal.lhand w)))
         let e ← liftExcept (HolCore.Kernel.mk_comb (← HolCore.Parser.parse_term "(=) (z:num)") a)
         pure (ABBREV_TAC e)) THEN
       REWRITE_TAC [IN_UNION, DE_MORGAN_THM] THEN STRIP_TAC THEN
       EXISTS_TAC ([[z:num]]) THEN ASM_REWRITE_TAC [] THEN
       CONJ_TAC THEN MATCH_MP_TAC subalpha THEN ASM_SIMP_TAC [LE_REFL] THENL
        [ASM_CASES_TAC ([[z:num = x]]) THEN ASM_REWRITE_TAC [] THEN
         UNDISCH_TAC [[~(x IN FV (formsubst ((v |-> s) i) (!! u p)))]],
         ASM_CASES_TAC ([[z:num = y]]) THEN ASM_REWRITE_TAC [] THEN
         UNDISCH_TAC [[~(y IN FV (formsubst ((v |-> t) i) (!! u p)))]]] THEN
       ASM_REWRITE_TAC [FORMSUBST_FV, FV, IN_ELIM_THM, IN_DELETE] THEN
       MATCH_MP_TAC MONO_NOT THEN MATCH_MP_TAC MONO_EXISTS THEN
       X_GEN_TAC ([[w:num]]) THEN ASM_CASES_TAC ([[w:num = u]]) THEN
       ASM_REWRITE_TAC [VALMOD_BASIC, FVT, IN_SING] THEN
       ASM_REWRITE_TAC [valmod, FVT, IN_SING]))
  : ExceptT String IO thm).run
#eval isubst_general

#eval phrase 78
unsafe def isubst : thm := keep "isubst" fun _ => (do
  prove ([[!A p x s t. A |-- s === t
                     --> formsubst (x |=> s) p --> formsubst (x |=> t) p]])
   (REWRITE_TAC [assign, isubst_general])
  : ExceptT String IO thm).run
#eval isubst

#eval phrase 79
unsafe def isubst_var : thm := keep "isubst_var" fun _ => (do
  prove ([[!A p x t. A |-- V x === t --> p --> formsubst (x |=> t) p]])
   (MESON_TAC [FORMSUBST_TRIV, ASSIGN_TRIV, isubst])
  : ExceptT String IO thm).run
#eval isubst_var

#eval phrase 80
unsafe def alpha : thm := keep "alpha" fun _ => (do
  prove ([[!A x z p. ~(z IN FV p) ==> A |-- (!!x p) --> !!z (formsubst (x |=> V z) p)]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC subalpha THEN CONJ_TAC THENL
     [ALL_TAC, MESON_TAC [isubst_var]] THEN
    REWRITE_TAC [FORMSUBST_FV, IN_ELIM_THM, ASSIGN] THEN
    ASM_MESON_TAC [IN_SING, FVT])
  : ExceptT String IO thm).run
#eval alpha

#eval phrase 81
unsafe def VARS : thm := keep "VARS" fun _ => (do
  newRec form_RECURSION
   [[(VARS False = {}) /\
  (VARS True = {}) /\
  (VARS (s === t) = FVT s UNION FVT t) /\
  (VARS (s << t) = FVT s UNION FVT t) /\
  (VARS (s <<= t) = FVT s UNION FVT t) /\
  (VARS (Not p) = VARS p) /\
  (VARS (p && q) = VARS p UNION VARS q) /\
  (VARS (p || q) = VARS p UNION VARS q) /\
  (VARS (p --> q) = VARS p UNION VARS q) /\
  (VARS (p <-> q) = VARS p UNION VARS q) /\
  (VARS (!! x p) = x INSERT VARS p) /\
  (VARS (?? x p) = x INSERT VARS p)]]
  : ExceptT String IO thm).run
#eval VARS

#eval phrase 82
unsafe def VARS_FINITE : thm := keep "VARS_FINITE" fun _ => (do
  prove ([[!p. FINITE(VARS p)]])
   (MATCH_MP_TAC form_INDUCT THEN
    ASM_SIMP_TAC [VARS, FINITE_RULES, FVT_FINITE, FINITE_UNION, FINITE_DELETE])
  : ExceptT String IO thm).run
#eval VARS_FINITE

#eval phrase 83
unsafe def FV_SUBSET_VARS : thm := keep "FV_SUBSET_VARS" fun _ => (do
  prove ([[!p. FV(p) SUBSET VARS(p)]])
   (REWRITE_TAC [SUBSET] THEN
    MATCH_MP_TAC form_INDUCT THEN REWRITE_TAC [FV, VARS] THEN
    REWRITE_TAC [IN_INSERT, IN_UNION, IN_DELETE] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval FV_SUBSET_VARS

#eval phrase 84
unsafe def TERMSUBST_TWICE_GENERAL : thm := keep "TERMSUBST_TWICE_GENERAL" fun _ => (do
  prove ([[!x z t v s. ~(z IN FVT s)
               ==> (termsubst ((x |-> t) v) s =
                    termsubst ((z |-> t) v) (termsubst (x |=> V z) s))]])
   (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC term_INDUCT THEN
    REWRITE_TAC [termsubst, ASSIGN, valmod, FVT, IN_SING, IN_UNION] THEN
    MESON_TAC [termsubst, ASSIGN])
  : ExceptT String IO thm).run
#eval TERMSUBST_TWICE_GENERAL

#eval phrase 85
unsafe def TERMSUBST_TWICE : thm := keep "TERMSUBST_TWICE" fun _ => (do
  prove ([[!x z t s. ~(z IN FVT s)
             ==> (termsubst (x |=> t) s =
                  termsubst (z |=> t) (termsubst (x |=> V z) s))]])
   (MESON_TAC [assign, TERMSUBST_TWICE_GENERAL])
  : ExceptT String IO thm).run
#eval TERMSUBST_TWICE

#eval phrase 86
unsafe def FORMSUBST_TWICE_GENERAL : thm := keep "FORMSUBST_TWICE_GENERAL" fun _ => (do
  prove ([[!p i j.
        (!x. x IN VARS p ==> safe_for x i)
        ==> formsubst j (formsubst i p) = formsubst (termsubst j o i) p]])
   (HolLight.tactic_of do
     let taut1 ← ExceptT.mk (TAUT [[p \/ q ==> r <=> (p ==> r) /\ (q ==> r)]])
     pure
      (MATCH_MP_TAC form_INDUCT THEN
       REWRITE_TAC [VARS, FORALL_IN_INSERT, IN_UNION, NOT_IN_EMPTY, FORALL_AND_THM,
                  taut1] THEN
       SIMP_TAC [FORMSUBST_SAFE_FOR] THEN
       REWRITE_TAC [formsubst, TERMSUBST_TERMSUBST] THEN SIMP_TAC [] THEN
       CONJ_TAC THEN MAP_EVERY X_GEN_TAC [ [[x:num]], [[p:form]] ] THEN
       STRIP_TAC THEN MAP_EVERY X_GEN_TAC [ [[i:num->term]], [[j:num->term]] ] THEN
       STRIP_TAC THEN
       REWRITE_TAC [FV, FORMSUBST_FV, TERMSUBST_FVT, o_THM,
                  IN_ELIM_THM, IN_DELETE] THEN
      (SUBGOAL_THEN
        ([[(?y. ((?y'. y' IN FV p /\ y IN FVT ((x |-> V x) i y')) /\ ~(y = x)) /\
          x IN FVT (j y)) <=>
    (?y. (y IN FV p /\ ~(y = x)) /\
         (?y'. y' IN FVT (i y) /\ x IN FVT (j y')))]])
        (fun th => REWRITE_TAC [th])
       THENL
        [REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
         ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
         AP_TERM_TAC THEN GEN_REWRITE_TAC HolCore.Lib.I [FUN_EQ_THM] THEN
         X_GEN_TAC ([[y:num]]) THEN
         ASM_CASES_TAC ([[y IN FV p]]) THEN ASM_REWRITE_TAC [] THEN
         ASM_CASES_TAC ([[y:num = x]]) THEN ASM_REWRITE_TAC [] THENL
          [ASM_REWRITE_TAC [VALMOD, FVT, IN_SING] THEN MESON_TAC [], ALL_TAC] THEN
         AP_TERM_TAC THEN GEN_REWRITE_TAC HolCore.Lib.I [FUN_EQ_THM] THEN
         X_GEN_TAC ([[z:num]]) THEN
         ASM_CASES_TAC ([[x IN FVT(j(z:num))]]) THEN ASM_REWRITE_TAC [] THEN
         ASM_REWRITE_TAC [VALMOD] THEN ASM_MESON_TAC [safe_for],
         ALL_TAC] THEN
       CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN
       COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
        [SUBGOAL_THEN
          ([[{x' | ?y. (?y'. y' IN FV p /\ y IN FVT ((x |-> V x) i y')) /\
                x' IN FVT ((x |-> V x) j y)} =
      {x' | ?y. y IN FV p /\ x' IN FVT ((x |-> V x) (termsubst j o i) y)}]])
          (fun th => REWRITE_TAC [th])
         THENL
          [REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC ([[z:num]]) THEN
           REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
           ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
           AP_TERM_TAC THEN GEN_REWRITE_TAC HolCore.Lib.I [FUN_EQ_THM] THEN
           X_GEN_TAC ([[y:num]]) THEN
           ASM_CASES_TAC ([[y IN FV p]]) THEN ASM_REWRITE_TAC [] THEN
           ASM_CASES_TAC ([[y:num = x]]) THEN ASM_REWRITE_TAC [] THEN
           ASM_REWRITE_TAC [VALMOD, FVT, IN_SING, UNWIND_THM2] THEN
           REWRITE_TAC [o_THM, TERMSUBST_FVT, IN_ELIM_THM] THEN
           ASM_MESON_TAC [safe_for],
           ABBREV_TAC [[z = VARIANT
       {x' | ?y. y IN FV p /\ x' IN FVT ((x |-> V x) (termsubst j o i) y)}]] ],
          ALL_TAC]) THEN
       AP_TERM_TAC THEN FIRST_X_ASSUM (fun th => HolCore.Lib.W (fun g => HolLight.tactic_of do
         let pm ← Session.PART_MATCH (fun t => do HolCore.Equal.lhs (← rand t)) th (← HolCore.Equal.lhs (HolLight.snd g))
         pure (MP_TAC pm))) THEN
       ASM_SIMP_TAC [SAFE_FOR_VALMOD, FVT, IN_SING] THEN
       DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC FORMSUBST_EQ THEN
       X_GEN_TAC ([[y:num]]) THEN DISCH_TAC THEN
       REWRITE_TAC [VALMOD, o_THM] THEN
       COND_CASES_TAC THEN ASM_REWRITE_TAC [termsubst, VALMOD] THEN
       MATCH_MP_TAC TERMSUBST_EQ THEN
       X_GEN_TAC ([[w:num]]) THEN REWRITE_TAC [VALMOD] THEN
       COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [safe_for]))
  : ExceptT String IO thm).run
#eval FORMSUBST_TWICE_GENERAL

#eval phrase 87
unsafe def FORMSUBST_TWICE : thm := keep "FORMSUBST_TWICE" fun _ => (do
  prove ([[!z p x t. ~(z IN VARS p)
             ==> (formsubst (z |=> t) (formsubst (x |=> V z) p) =
                  formsubst (x |=> t) p)]])
   (REPEAT STRIP_TAC THEN
    HolCore.Lib.W (fun g => HolLight.tactic_of do
      let pm ← Session.PART_MATCH (fun t => do HolCore.Equal.lhs (← rand t)) FORMSUBST_TWICE_GENERAL (← HolCore.Equal.lhs (HolLight.snd g))
      pure (MP_TAC pm)) THEN
    REWRITE_TAC [SAFE_FOR_ASSIGN, FVT, IN_SING] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC FORMSUBST_EQ THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [o_THM, VALMOD, ASSIGN] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [termsubst, ASSIGN] THEN
    ASM_MESON_TAC [FV_SUBSET_VARS, SUBSET])
  : ExceptT String IO thm).run
#eval FORMSUBST_TWICE

#eval phrase 88
unsafe def ispec_lemma : thm := keep "ispec_lemma" fun _ => (do
  prove ([[!A x p t. ~(x IN FVT(t)) ==> A |-- !!x p --> formsubst (x |=> t) p]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC subspec THEN
    EXISTS_TAC ([[t:term]]) THEN ASM_REWRITE_TAC [isubst_var] THEN
    ASM_REWRITE_TAC [FORMSUBST_FV, IN_ELIM_THM, ASSIGN] THEN
    ASM_MESON_TAC [FVT, IN_SING])
  : ExceptT String IO thm).run
#eval ispec_lemma

#eval phrase 89
unsafe def ispec : thm := keep "ispec" fun _ => (do
  prove ([[!A x p t. A |-- !!x p --> formsubst (x |=> t) p]])
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC ([[x IN FVT(t)]]) THEN
    ASM_SIMP_TAC [ispec_lemma] THEN
    ABBREV_TAC [[z = VARIANT (FVT t UNION VARS p)]] THEN
    MATCH_MP_TAC imp_trans THEN
    EXISTS_TAC ([[!!z (formsubst (x |=> V z) p)]]) THEN CONJ_TAC THENL
     [MATCH_MP_TAC alpha THEN EXPAND_TAC "z" THEN
      MATCH_MP_TAC NOT_IN_VARIANT THEN
      REWRITE_TAC [FINITE_UNION, SUBSET, IN_UNION] THEN
      MESON_TAC [SUBSET, FVT_FINITE, VARS_FINITE, FV_SUBSET_VARS],
      SUBGOAL_THEN
       ([[formsubst (x |=> t) p =
      formsubst (z |=> t) (formsubst (x |=> V z) p)]])
      SUBST1_TAC THENL
       [MATCH_MP_TAC (← HolLight.GSYM FORMSUBST_TWICE), MATCH_MP_TAC ispec_lemma] THEN
      EXPAND_TAC "z" THEN MATCH_MP_TAC NOT_IN_VARIANT THEN
      REWRITE_TAC [VARS_FINITE, FVT_FINITE, FINITE_UNION] THEN
      SIMP_TAC [SUBSET, IN_UNION]])
  : ExceptT String IO thm).run
#eval ispec

#eval phrase 90
unsafe def spec : thm := keep "spec" fun _ => (do
  prove ([[!A x p t. A |-- !!x p ==> A |-- formsubst (x |=> t) p]])
   (MESON_TAC [ispec, modusponens])
  : ExceptT String IO thm).run
#eval spec

#eval phrase 91
unsafe def spec_var : thm := keep "spec_var" fun _ => (do
  prove ([[!A x p. A |-- !!x p ==> A |-- p]])
   (REPEAT GEN_TAC THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
      let th1 ← HolLight.MATCH_MP spec th
      let th2 ← HolLight.SPEC ([[V x]]) th1
      pure (MP_TAC th2)) THEN
    SIMP_TAC [ASSIGN_TRIV, FORMSUBST_TRIVIAL])
  : ExceptT String IO thm).run
#eval spec_var

#eval phrase 92
unsafe def instantiation : thm := keep "instantiation" fun _ => (do
  prove ([[!A v p. A |-- p ==> A |-- formsubst v p]])
   (HolLight.tactic_of do
     let lemma ← prove ([[!A p v. (!x y. x IN FV p /\ y IN FV p /\ x IN FVT(v y)
                    ==> x = y /\ v x = V x) /\
             A |-- p
             ==> A |-- formsubst v p]])
      (REPEAT GEN_TAC THEN
          WF_INDUCT_TAC [[CARD {x | x IN FV(p) /\ ~(v x = V x)}]] THEN
          ASM_CASES_TAC ([[!x. x IN FV p ==> v x = V x]]) THEN
          ASM_SIMP_TAC [FORMSUBST_TRIVIAL] THEN
          FIRST_X_ASSUM (MP_TAC oTIO HolLight.GEN_REWRITE_RULE HolCore.Lib.I [NOT_FORALL_THM]) THEN
          REWRITE_TAC [NOT_IMP, LEFT_IMP_EXISTS_THM] THEN
          X_GEN_TAC ([[x:num]]) THEN REPEAT STRIP_TAC THEN
          FIRST_X_ASSUM (fun th => HolLight.tactic_of do
            let sp ← HolLight.SPECL [ [[p:form]], [[(x |-> V x) v]] ] th
            pure (MP_TAC sp)) THEN
          ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
           [MATCH_MP_TAC CARD_PSUBSET THEN SIMP_TAC [FINITE_RESTRICT, FV_FINITE] THEN
            REWRITE_TAC [PSUBSET_ALT] THEN CONJ_TAC THENL
             [REWRITE_TAC [SUBSET, VALMOD, IN_ELIM_THM] THEN ASM_MESON_TAC [],
              EXISTS_TAC ([[x:num]]) THEN ASM_REWRITE_TAC [VALMOD, IN_ELIM_THM] THEN
              ASM_MESON_TAC []],
            ALL_TAC] THEN
          ANTS_TAC THENL
           [REPEAT GEN_TAC THEN REWRITE_TAC [VALMOD] THEN
            COND_CASES_TAC THEN ASM_SIMP_TAC [FVT, IN_SING] THEN ASM_MESON_TAC [],
            ALL_TAC] THEN
          SUBGOAL_THEN
           ([[formsubst v p = formsubst ((x |-> v x) v) p]])
          SUBST1_TAC THENL [SIMP_TAC [VALMOD_TRIVIAL], ALL_TAC] THEN
          DISCH_THEN (fun th => HolLight.tactic_of do
            let gth ← HolLight.MATCH_MP gen th
            let sth ← HolLight.SPEC ([[x:num]]) gth
            pure (MP_TAC sth)) THEN
          MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ] modusponens) THEN
          MATCH_MP_TAC exists_imp THEN CONJ_TAC THENL
           [ALL_TAC,
            REWRITE_TAC [FORMSUBST_FV, IN_ELIM_THM, NOT_EXISTS_THM, VALMOD] THEN
            ASM SET_TAC []] THEN
          MATCH_MP_TAC modusponens THEN EXISTS_TAC ([[??x (V x === v x)]]) THEN
          SIMP_TAC [eximp, isubst_general] THEN ASM_MESON_TAC [axiom_existseq])
     let ar2 ← ExceptT.mk (ARITH_RULE [[~(x + n:num < n)]])
     let ar3 ← ExceptT.mk (ARITH_RULE [[x < n /\ y < n ==> ~(x = y + n)]])
     let setr ← ExceptT.mk (Session.SET_RULE [[{x | ?y. y IN s /\ x = f y} = IMAGE f s]])
     pure
      (REPEAT STRIP_TAC THEN
       SUBGOAL_THEN
        ([[?n. !x. x IN VARS p \/ x IN FV(formsubst v p) ==> x < n]])
       STRIP_ASSUME_TAC THENL
        [EXISTS_TAC ([[SUC(SETMAX(VARS p UNION FV(formsubst v p)))]]) THEN
         REWRITE_TAC [(← HolLight.GSYM IN_UNION), LT_SUC_LE] THEN MATCH_MP_TAC SETMAX_MEMBER THEN
         REWRITE_TAC [FINITE_UNION, VARS_FINITE, FV_FINITE],
         ALL_TAC] THEN
       SUBGOAL_THEN
        ([[formsubst v p =
    formsubst (\i. v(i - n)) (formsubst (\i. V(i + n)) p)]])
       SUBST1_TAC THENL
        [HolCore.Lib.W (fun g => HolLight.tactic_of do
           let pm ← Session.PART_MATCH (fun t => do HolCore.Equal.lhs (← rand t)) FORMSUBST_TWICE_GENERAL (← rand (HolLight.snd g))
           pure (MP_TAC pm)) THEN
         REWRITE_TAC [safe_for, FVT, IN_SING] THEN ANTS_TAC THENL
          [ASM_MESON_TAC [ar2],
           DISCH_THEN SUBST1_TAC THEN
           REWRITE_TAC [o_DEF, termsubst, ADD_SUB, ETA_AX]],
         MATCH_MP_TAC lemma THEN REWRITE_TAC [FVT] THEN CONJ_TAC THENL
          [REWRITE_TAC [FORMSUBST_FV, FVT, IN_SING] THEN
           REWRITE_TAC [setr] THEN
           REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE] THEN
           X_GEN_TAC ([[x:num]]) THEN DISCH_TAC THEN REWRITE_TAC [ADD_SUB, FVT] THEN
           X_GEN_TAC ([[y:num]]) THEN REPEAT DISCH_TAC THEN
           FIRST_X_ASSUM (MP_TAC oTIO HolLight.SPEC [[x + n:num]]) THEN
           MATCH_MP_TAC (← TAUT [[~p /\ q ==> (r \/ q ==> p) ==> s]]) THEN
           CONJ_TAC THENL [ARITH_TAC, REWRITE_TAC [FORMSUBST_FV, IN_ELIM_THM]] THEN
           ASM_MESON_TAC [],
           MATCH_MP_TAC lemma THEN REWRITE_TAC [FVT, IN_SING] THEN
           ASM_MESON_TAC [ar3, FV_SUBSET_VARS, SUBSET]]]))
  : ExceptT String IO thm).run
#eval instantiation

#eval phrase 93
unsafe def PROVES_MONO : thm := keep "PROVES_MONO" fun _ => (do
  prove ([[!A B p. A SUBSET B /\ A |-- p ==> B |-- p]])
   (GEN_TAC THEN GEN_TAC THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC proves_INDUCT THEN  ASM_MESON_TAC [proves_RULES, SUBSET])
  : ExceptT String IO thm).run
#eval PROVES_MONO

#eval phrase 94
unsafe def DEDUCTION_LEMMA : thm := keep "DEDUCTION_LEMMA" fun _ => (do
  prove ([[!A p q. p INSERT A |-- q /\ closed p ==> A |-- p --> q]])
   (GEN_TAC THEN ONCE_REWRITE_TAC [CONJ_SYM] THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC proves_INDUCT THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC ([[r:form]]) THENL
     [REWRITE_TAC [IN_INSERT] THEN MESON_TAC [proves_RULES, add_assum, imp_refl],
      MESON_TAC [modusponens, axiom_distribimp],
      ASM_MESON_TAC [gen_right, closed, NOT_IN_EMPTY]])
  : ExceptT String IO thm).run
#eval DEDUCTION_LEMMA

#eval phrase 95
unsafe def DEDUCTION : thm := keep "DEDUCTION" fun _ => (do
  prove ([[!A p q. closed p ==> (A |-- p --> q <=> p INSERT A |-- q)]])
   (MESON_TAC [DEDUCTION_LEMMA, modusponens, IN_INSERT, proves_RULES,
            PROVES_MONO, SUBSET])
  : ExceptT String IO thm).run
#eval DEDUCTION

#eval phrase 96
unsafe def eq_trans : thm := keep "eq_trans" fun _ => (do
  prove ([[!A s t u. A |-- s === t --> t === u --> s === u]])
   (MESON_TAC [axiom_predcong, modusponens, imp_swap, axiom_eqrefl, imp_trans,
            eq_sym])
  : ExceptT String IO thm).run
#eval eq_trans

#eval phrase 97
unsafe def spec_right : thm := keep "spec_right" fun _ => (do
  prove ([[!A p q x. A |-- p --> !!x q ==> A |-- p --> formsubst (x |=> t) q]])
   (MESON_TAC [imp_trans, ispec])
  : ExceptT String IO thm).run
#eval spec_right

#eval phrase 98
unsafe def eq_trans_rule : thm := keep "eq_trans_rule" fun _ => (do
  prove ([[!A s t u. A |-- s === t /\ A |-- t === u ==> A |-- s === u]])
   (MESON_TAC [modusponens, eq_trans])
  : ExceptT String IO thm).run
#eval eq_trans_rule

#eval phrase 99
unsafe def eq_sym_rule : thm := keep "eq_sym_rule" fun _ => (do
  prove ([[!A s t. A |-- s === t <=> A |-- t === s]])
   (MESON_TAC [modusponens, eq_sym])
  : ExceptT String IO thm).run
#eval eq_sym_rule

#eval phrase 100
unsafe def allimp : thm := keep "allimp" fun _ => (do
  prove ([[!A x p q. A |-- p --> q ==> A |-- !!x p --> !!x q]])
   (MESON_TAC [axiom_allimp, modusponens, gen])
  : ExceptT String IO thm).run
#eval allimp

#eval phrase 101
unsafe def alliff : thm := keep "alliff" fun _ => (do
  prove ([[!A x p q. A |-- p <-> q ==> A |-- !!x p <-> !!x q]])
   (MESON_TAC [allimp, iff_imp1, iff_imp2, imp_antisym])
  : ExceptT String IO thm).run
#eval alliff

#eval phrase 102
unsafe def exiff : thm := keep "exiff" fun _ => (do
  prove ([[!A x p q. A |-- p <-> q ==> A |-- ??x p <-> ??x q]])
   (MESON_TAC [eximp, iff_imp1, iff_imp2, imp_antisym])
  : ExceptT String IO thm).run
#eval exiff

#eval phrase 103
unsafe def cong_suc : thm := keep "cong_suc" fun _ => (do
  prove ([[!A s t. A |-- s === t ==> A |-- Suc s === Suc t]])
   (MESON_TAC [modusponens, axiom_funcong])
  : ExceptT String IO thm).run
#eval cong_suc

#eval phrase 104
unsafe def cong_add : thm := keep "cong_add" fun _ => (do
  prove ([[!A s t u v. A |-- s === t /\ A |-- u === v ==> A |-- s ++ u === t ++ v]])
   (MESON_TAC [modusponens, axiom_funcong])
  : ExceptT String IO thm).run
#eval cong_add

#eval phrase 105
unsafe def cong_mul : thm := keep "cong_mul" fun _ => (do
  prove ([[!A s t u v. A |-- s === t /\ A |-- u === v ==> A |-- s ** u === t ** v]])
   (MESON_TAC [modusponens, axiom_funcong])
  : ExceptT String IO thm).run
#eval cong_mul

#eval phrase 106
unsafe def cong_eq : thm := keep "cong_eq" fun _ => (do
  prove ([[!A s t u v. A |-- s === t /\ A |-- u === v ==> A |-- s === u <-> t === v]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC imp_antisym THEN
    ASM_MESON_TAC [modusponens, axiom_predcong, eq_sym])
  : ExceptT String IO thm).run
#eval cong_eq

#eval phrase 107
unsafe def cong_le : thm := keep "cong_le" fun _ => (do
  prove ([[!A s t u v. A |-- s === t /\ A |-- u === v ==> A |-- s <<= u <-> t <<= v]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC imp_antisym THEN
    ASM_MESON_TAC [modusponens, axiom_predcong, eq_sym])
  : ExceptT String IO thm).run
#eval cong_le

#eval phrase 108
unsafe def cong_lt : thm := keep "cong_lt" fun _ => (do
  prove ([[!A s t u v. A |-- s === t /\ A |-- u === v ==> A |-- s << u <-> t << v]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC imp_antisym THEN
    ASM_MESON_TAC [modusponens, axiom_predcong, eq_sym])
  : ExceptT String IO thm).run
#eval cong_lt

#eval phrase 109
unsafe def iexists : thm := keep "iexists" fun _ => (do
  prove ([[!A x t p. A |-- formsubst (x |=> t) p --> ??x p]])
   (REPEAT GEN_TAC THEN TRANS_TAC imp_trans ([[Not(!!x (Not p))]]) THEN
    CONJ_TAC THENL [ALL_TAC, MESON_TAC [axiom_exists, iff_imp2]] THEN
    TRANS_TAC imp_trans ([[Not(formsubst (x |=> t) (Not p))]]) THEN
    REWRITE_TAC [contrapos_eq, ispec] THEN REWRITE_TAC [formsubst] THEN
    MESON_TAC [not_not, iff_imp2])
  : ExceptT String IO thm).run
#eval iexists

#eval phrase 110
unsafe def exists_intro : thm := keep "exists_intro" fun _ => (do
  prove ([[!A x t p. A |-- formsubst (x |=> t) p ==> A |-- ??x p]])
   (MESON_TAC [iexists, modusponens])
  : ExceptT String IO thm).run
#eval exists_intro

#eval phrase 111
unsafe def impex : thm := keep "impex" fun _ => (do
  prove ([[!A x p. ~(x IN FV p) ==> A |-- (??x p) --> p]])
   (REPEAT STRIP_TAC THEN TRANS_TAC imp_trans ([[Not(Not p)]]) THEN
    CONJ_TAC THENL [ALL_TAC, MESON_TAC [not_not, iff_imp1]] THEN
    TRANS_TAC imp_trans ([[Not(!!x (Not p))]]) THEN
    ASM_SIMP_TAC [contrapos_eq, axiom_impall, FV] THEN
    MESON_TAC [axiom_exists, iff_imp1])
  : ExceptT String IO thm).run
#eval impex

#eval phrase 112
unsafe def ichoose : thm := keep "ichoose" fun _ => (do
  prove ([[!A x p q. A |-- !!x (p --> q) /\ ~(x IN FV q) ==> A |-- (??x p) --> q]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP spec_var) THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
      let mth ← HolLight.MATCH_MP eximp th
      let sth ← HolLight.SPEC ([[x:num]]) mth
      pure (MP_TAC sth)) THEN
    MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ_ALT] imp_trans) THEN
    ASM_SIMP_TAC [impex])
  : ExceptT String IO thm).run
#eval ichoose

#eval phrase 113
unsafe def eq_trans_imp : thm := keep "eq_trans_imp" fun _ => (do
  prove ([[A |-- s === s' /\ A |-- t === t' ==> A |-- s === t --> s' === t']])
   (MESON_TAC [axiom_predcong, modusponens])
  : ExceptT String IO thm).run
#eval eq_trans_imp

#eval phrase 114
unsafe def fv_theorems : IO.Ref (List thm) :=
  keep "fv_theorems" fun _ => unsafeBaseIO (IO.mkRef
   [FV, FV_AXIOM, FV_DIAGONALIZE, FV_DIVIDES, FV_FINITE, FV_FIXPOINT, FV_FORM,
  FV_FORM1, FV_FREEFORM, FV_FREEFORM1, FV_FREETERM, FV_FREETERM1,
  FV_GNUMERAL, FV_GNUMERAL1, Tarski.«FV_GNUMERAL1'», FV_GSENTENCE,
  FV_HSENTENCE, FV_PRIME, FV_PRIMEPOW, FV_PRIMREC, FV_PRIMRECSTEP, FV_PROV,
  FV_PROV1, FV_QDIAG, FV_QSUBST, FV_RTC, FV_RTCP, FV_SUBSET_VARS, FV_TERM,
  FV_TERM1, FVT, FVT_NUMERAL])
#eval do
  let l ← fv_theorems.get
  IO.println ("{contents = [" ++ "; ".intercalate (l.map toString) ++ "]}")

#eval phrase 115
/- let IN_FV_RULE ths tm = try EQT_ELIM(...) with Failure _ -> ASSUME tm -/
unsafe def IN_FV_RULE (ths : List thm) (tm : term) : IO thm := do
  let fvts ← fv_theorems.get
  let conv := (HolLight.GEN_REWRITE_CONV HolLight.TOP_DEPTH_CONV
                ([IN_UNION, IN_DELETE, NOT_IN_EMPTY, IN_INSERT] ++ ths ++ fvts) THENC
               Session.NUM_REDUCE_CONV)
  match ← (do liftExcept (Session.EQT_ELIM (← ExceptT.mk (conv tm))) : ExceptT String IO thm).run with
  | .ok th => pure th
  | .error _ => match HolCore.Kernel.ASSUME tm with
                | .ok th => pure th
                | .error e => throw (IO.userError e)
#eval do IO.println "<fun>"

#eval phrase 116
/- let rec SAFE_FOR_RULE tm = ... (three PART_MATCH attempts) -/
unsafe def SAFE_FOR_RULE (tm : term) : IO thm := do
  let ioE {α : Type} (e : Except String α) : IO α :=
    match e with | .ok v => pure v | .error m => throw (IO.userError m)
  match ← (Session.PART_MATCH pure SAFE_FOR_V tm) with
  | .ok th => pure th
  | .error _ =>
  match ← (Session.PART_MATCH HolCore.Equal.lhand SAFE_FOR_ASSIGN tm) with
    | .ok th1 => do
        let th2 ← IN_FV_RULE [] (← ioE (rand (HolCore.Kernel.concl th1)))
        let sth ← ioE (HolCore.Equal.SYM th1)
        ioE (HolCore.Kernel.EQ_MP sth th2)
    | .error _ => do
        let th1 ← match ← (Session.PART_MATCH rand SAFE_FOR_VALMOD tm) with
                  | .ok t => pure t | .error e => throw (IO.userError e)
        let (l, r) ← ioE (do HolCore.Basics.dest_conj (← HolCore.Equal.lhand (HolCore.Kernel.concl th1)))
        let sl ← SAFE_FOR_RULE l
        let sr ← IN_FV_RULE [] r
        let th2 ← ioE (Session.CONJ sl sr)
        ioE (Session.MP th1 th2)
#eval do IO.println "<fun>"

#eval phrase 117
/- let VALMOD_CONV = GEN_REWRITE_CONV TOP_DEPTH_CONV [ASSIGN; VALMOD] THENC NUM_REDUCE_CONV -/
unsafe def VALMOD_CONV : HolCore.Equal.ioconv :=
  HolLight.GEN_REWRITE_CONV HolLight.TOP_DEPTH_CONV [ASSIGN, VALMOD] THENC Session.NUM_REDUCE_CONV
#eval do IO.println "<fun>"

#eval phrase 118
unsafe def TERMSUBST_NUMERAL : thm := keep "TERMSUBST_NUMERAL" fun _ => (do
  prove ([[!v n. termsubst v (numeral n) = numeral n]])
   (SIMP_TAC [TERMSUBST_TRIVIAL, FVT_NUMERAL, NOT_IN_EMPTY])
  : ExceptT String IO thm).run
#eval TERMSUBST_NUMERAL

#eval phrase 119
/- let rec TERMSUBST_CONV tm = ... -/
unsafe def TERMSUBST_CONV : HolCore.Equal.ioconv := fun tm => ((do
  let cj1 ← liftExcept (Session.CONJUNCT1 termsubst)
  let c1 ← liftExcept (Session.CONJ TERMSUBST_NUMERAL cj1)
  let e1 ← liftExcept (HolCore.Lib.el 1 (Session.CONJUNCTS termsubst))
  let e2 ← liftExcept (HolCore.Lib.el 2 (Session.CONJUNCTS termsubst))
  let e3 ← liftExcept (HolCore.Lib.funpowM 3 Session.CONJUNCT2 termsubst)
  ExceptT.mk ((HolLight.GEN_REWRITE_CONV HolCore.Lib.I [c1] ORELSEC
    (HolLight.GEN_REWRITE_CONV HolCore.Lib.I [e1] THENC VALMOD_CONV) ORELSEC
    (HolLight.GEN_REWRITE_CONV HolCore.Lib.I [e2] THENC
     HolLight.RAND_CONV TERMSUBST_CONV) ORELSEC
    (HolLight.GEN_REWRITE_CONV HolCore.Lib.I [e3] THENC
     HolLight.BINOP_CONV TERMSUBST_CONV)) tm) : ExceptT String IO thm).run)
#eval do IO.println "<fun>"

#eval phrase 120
/- let rec FORMSUBST_CONV tm = ... -/
unsafe def FORMSUBST_CONV : HolCore.Equal.ioconv := fun tm => ((do
  let f0 ← liftExcept (HolCore.Lib.el 0 (Session.CONJUNCTS formsubst))
  let f1 ← liftExcept (HolCore.Lib.el 1 (Session.CONJUNCTS formsubst))
  let f2 ← liftExcept (HolCore.Lib.el 2 (Session.CONJUNCTS formsubst))
  let f3 ← liftExcept (HolCore.Lib.el 3 (Session.CONJUNCTS formsubst))
  let f4 ← liftExcept (HolCore.Lib.el 4 (Session.CONJUNCTS formsubst))
  let f5 ← liftExcept (HolCore.Lib.el 5 (Session.CONJUNCTS formsubst))
  let f6 ← liftExcept (HolCore.Lib.el 6 (Session.CONJUNCTS formsubst))
  let f7 ← liftExcept (HolCore.Lib.el 7 (Session.CONJUNCTS formsubst))
  let f8 ← liftExcept (HolCore.Lib.el 8 (Session.CONJUNCTS formsubst))
  let f9 ← liftExcept (HolCore.Lib.el 9 (Session.CONJUNCTS formsubst))
  let safeConv : HolCore.Equal.ioconv := fun tm => ((do
    let c1 ← liftExcept (Session.CONJUNCT1 FORMSUBST_SAFE_FOR)
    let c2 ← liftExcept (Session.CONJUNCT2 FORMSUBST_SAFE_FOR)
    let th ← ((Session.PART_MATCH (fun t => do HolCore.Equal.lhand (← rand t)) c1 tm : ExceptT String IO thm) <|>
              (Session.PART_MATCH (fun t => do HolCore.Equal.lhand (← rand t)) c2 tm : ExceptT String IO thm))
    let lh ← liftExcept (HolCore.Equal.lhand (HolCore.Kernel.concl th))
    let sfr ← (ExceptT.lift (SAFE_FOR_RULE lh) : ExceptT String IO thm)
    liftExcept (Session.MP th sfr) : ExceptT String IO thm).run)
  ExceptT.mk ((HolLight.GEN_REWRITE_CONV HolCore.Lib.I [f0, f1] ORELSEC
    (HolLight.GEN_REWRITE_CONV HolCore.Lib.I [f2, f3, f4] THENC HolLight.BINOP_CONV TERMSUBST_CONV) ORELSEC
    (HolLight.GEN_REWRITE_CONV HolCore.Lib.I [f5] THENC HolLight.RAND_CONV FORMSUBST_CONV) ORELSEC
    (HolLight.GEN_REWRITE_CONV HolCore.Lib.I [f6, f7, f8, f9] THENC HolLight.BINOP_CONV FORMSUBST_CONV) ORELSEC
    (safeConv THENC HolLight.RAND_CONV FORMSUBST_CONV)) tm) : ExceptT String IO thm).run)
#eval do IO.println "<fun>"

#eval phrase 121
/- let spec_var_rule th = MATCH_MP spec_var th -/
unsafe def spec_var_rule (th : thm) : ExceptT String IO thm := HolLight.MATCH_MP spec_var th
#eval do IO.println "<fun>"

#eval phrase 122
/- let spec_all_rule = repeat spec_var_rule -/
unsafe def spec_all_rule (th : thm) : ExceptT String IO thm := ExceptT.mk do
  match ← (spec_var_rule th).run with
  | .ok th' => (spec_all_rule th').run
  | .error _ => pure (.ok th)
#eval do IO.println "<fun>"

#eval phrase 123
/- let instantiate_rule ilist th = ... -/
unsafe def instantiate_rule (ilist : List (term × Nat)) (th : thm) : ExceptT String IO thm := do
  let v_tm ← (HolCore.Parser.parse_term "(|->):num->term->(num->term)->(num->term)")
  let Vtm ← (HolCore.Parser.parse_term "V")
  let v ← liftExcept (HolCore.Lib.itlistM (fun (tx : term × Nat) (v : term) => do
      let (t, x) := tx
      let n ← Session.mk_small_numeral (x : Int)
      HolCore.Kernel.mk_comb (← HolCore.Kernel.mk_comb (← HolCore.Kernel.mk_comb v_tm n) t) v)
    ilist Vtm)
  let inst ← HolLight.MATCH_MP instantiation th
  let sp ← HolLight.SPEC v inst
  HolLight.CONV_RULE (HolLight.RAND_CONV FORMSUBST_CONV) sp
#eval do IO.println "<fun>"

#eval phrase 124
/- let specl_rule tms th = ... -/
unsafe def specl_rule (tms : List term) (th : thm) : ExceptT String IO thm := do
  let bop ← (HolCore.Parser.parse_term "(!!):num->form->form")
  let rhsTh ← liftExcept (rand (HolCore.Kernel.concl th))
  let avs := HolCore.Lib.striplist (fun t => HolCore.Basics.dest_binop bop t) rhsTh
  let vs ← liftExcept (do pure ((← HolCore.Lib.chop_list tms.length avs).1))
  let ilist ← liftExcept ((tms.zip vs).mapM (fun (t, v) => do
      let n ← Session.dest_small_numeral v
      pure (t, n.toNat)))
  let th' ← vs.foldlM (fun t _ => HolLight.MATCH_MP spec_var t) th
  instantiate_rule ilist th'
#eval do IO.println "<fun>"

#eval phrase 125
/- let spec_rule t th = specl_rule [t] th -/
unsafe def spec_rule (t : term) (th : thm) : ExceptT String IO thm := specl_rule [t] th
#eval do IO.println "<fun>"

#eval phrase 126
/- let gen_rule t th = SPEC (mk_small_numeral t) (MATCH_MP gen th) -/
unsafe def gen_rule (t : Nat) (th : thm) : ExceptT String IO thm := do
  let g ← HolLight.MATCH_MP gen th
  let n ← liftExcept (Session.mk_small_numeral (t : Int))
  HolLight.SPEC n g
#eval do IO.println "<fun>"

#eval phrase 127
/- let gens_tac ns (asl,w) = ... -/
unsafe def gens_tac (ns : List Nat) : HolCore.Tactics.tactic := fun g =>
  HolLight.tactic_of (do
    let w := HolLight.snd g
    let (avs, bod) ← liftExcept (HolCore.Lib.nsplit HolCore.Basics.dest_forall ns w)
    let Vtm ← (HolCore.Parser.parse_term "V")
    let nvs ← liftExcept (ns.mapM (fun (n : Nat) => do
        let num ← Session.mk_small_numeral (n : Int)
        HolCore.Kernel.mk_comb Vtm num))
    let substf ← ExceptT.mk (HolCore.Basics.subst (nvs.zip avs))
    let bod' ← ExceptT.mk (substf bod)
    let asm ← liftExcept (HolCore.Kernel.ASSUME bod')
    let inst ← instantiate_rule (avs.zip ns) asm
    let gth ← HolLight.GENL avs inst
    let dth ← Session.DISCH_ALL gth
    pure (MATCH_MP_TAC dth)) g
#eval do IO.println "<fun>"

#eval phrase 128
/- let gen_tac n = gens_tac [n] -/
unsafe def gen_tac (n : Nat) : HolCore.Tactics.tactic := gens_tac [n]
#eval do IO.println "<fun>"

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.Derived" do
  replay (
          HolLogicArith.Godel.ensure)
  replay (
          negativef)
  replay (
          negatef)
  replay (
          axiom_addimp)
  replay (
          axiom_distribimp)
  replay (
          axiom_doubleneg)
  replay (
          axiom_allimp)
  replay (
          axiom_impall)
  replay (
          axiom_existseq)
  replay (
          axiom_eqrefl)
  replay (
          axiom_funcong)
  replay (
          axiom_predcong)
  replay (
          axiom_iffimp1)
  replay (
          axiom_iffimp2)
  replay (
          axiom_impiff)
  replay (
          axiom_true)
  replay (
          axiom_not)
  replay (
          axiom_and)
  replay (
          axiom_or)
  replay (
          axiom_exists)
  replay (
          «assume»)
  replay (
          modusponens)
  replay (
          gen)
  replay (
          iff_imp1)
  replay (
          iff_imp2)
  replay (
          imp_antisym)
  replay (
          add_assum)
  replay (
          imp_refl)
  replay (
          imp_add_assum)
  replay (
          imp_unduplicate)
  replay (
          imp_trans)
  replay (
          imp_swap)
  replay (
          imp_trans_chain_2)
  replay (
          imp_trans_th)
  replay (
          imp_add_concl)
  replay (
          imp_trans2)
  replay (
          imp_swap_th)
  replay (
          contrapos)
  replay (
          imp_truefalse)
  replay (
          imp_insert)
  replay (
          imp_mono_th)
  replay (
          ex_falso)
  replay (
          imp_contr)
  replay (
          imp_contrf)
  replay (
          contrad)
  replay (
          bool_cases)
  replay (
          imp_false_rule)
  replay (
          imp_true_rule)
  replay (
          truth)
  replay (
          and_left)
  replay (
          and_right)
  replay (
          and_pair)
  replay (
          META_AND)
  replay (
          shunt)
  replay (
          ante_conj)
  replay (
          not_not_false)
  replay (
          iff_sym)
  replay (
          iff_trans)
  replay (
          not_not)
  replay (
          contrapos_eq)
  replay (
          or_left)
  replay (
          or_right)
  replay (
          ante_disj)
  replay (
          iff_def)
  replay (
          do IO.println iff_refl)
  replay (
          eq_sym)
  replay (
          icongruence_general)
  replay (
          icongruence)
  replay (
          icongruence_var)
  replay (
          gen_right)
  replay (
          genimp)
  replay (
          eximp)
  replay (
          exists_imp)
  replay (
          subspec)
  replay (
          subalpha)
  replay (
          complexity)
  replay (
          COMPLEXITY_FORMSUBST)
  replay (
          isubst_general)
  replay (
          isubst)
  replay (
          isubst_var)
  replay (
          alpha)
  replay (
          VARS)
  replay (
          VARS_FINITE)
  replay (
          FV_SUBSET_VARS)
  replay (
          TERMSUBST_TWICE_GENERAL)
  replay (
          TERMSUBST_TWICE)
  replay (
          FORMSUBST_TWICE_GENERAL)
  replay (
          FORMSUBST_TWICE)
  replay (
          ispec_lemma)
  replay (
          ispec)
  replay (
          spec)
  replay (
          spec_var)
  replay (
          instantiation)
  replay (
          PROVES_MONO)
  replay (
          DEDUCTION_LEMMA)
  replay (
          DEDUCTION)
  replay (
          eq_trans)
  replay (
          spec_right)
  replay (
          eq_trans_rule)
  replay (
          eq_sym_rule)
  replay (
          allimp)
  replay (
          alliff)
  replay (
          exiff)
  replay (
          cong_suc)
  replay (
          cong_add)
  replay (
          cong_mul)
  replay (
          cong_eq)
  replay (
          cong_le)
  replay (
          cong_lt)
  replay (
          iexists)
  replay (
          exists_intro)
  replay (
          impex)
  replay (
          ichoose)
  replay (
          eq_trans_imp)
  replay (
          do
      let l ← fv_theorems.get
      IO.println ("{contents = [" ++ "; ".intercalate (l.map toString) ++ "]}"))
  replay (
          do IO.println "<fun>")
  replay (
          do IO.println "<fun>")
  replay (
          do IO.println "<fun>")
  replay (
          TERMSUBST_NUMERAL)
  replay (
          do IO.println "<fun>")
  replay (
          do IO.println "<fun>")
  replay (
          do IO.println "<fun>")
  replay (
          do IO.println "<fun>")
  replay (
          do IO.println "<fun>")
  replay (
          do IO.println "<fun>")
  replay (
          do IO.println "<fun>")
  replay (
          do IO.println "<fun>")
  replay (
          do IO.println "<fun>")
  replay (
          do IO.println "<fun>")
-- @@ENSURE END

end HolLogicArith.Derived
