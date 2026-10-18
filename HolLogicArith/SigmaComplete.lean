/- File: HolLogicArith/SigmaComplete.lean
Translation of HOL Light's Arithmetic/sigmacomplete.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.Derived
open HolCore.Kernel HolCore.Lib HolCore.Basics Session HolLight.Syntax HolLogicArith
open scoped HolLight
-- Names from Arithmetic/fol.ml that sigmacomplete.ml reuses.
open HolLogicArith.ArithFol (FV FVT FVT_NUMERAL termsubst formsubst valmod VALMOD
  assign ASSIGN ASSIGN_TRIV TERMSUBST_TRIV TERMSUBST_TRIVIAL FORMSUBST_TRIV FORMSUBST_TRIVIAL
  term_INDUCT form_INDUCT form_RECURSION form_DISTINCT form_INJ
  VARIANT NOT_IN_VARIANT VARIANT_FINITE FV_FINITE FVT_FINITE
  VALMOD_BASIC VALMOD_VALMOD_BASIC VALMOD_TRIVIAL VALMOD_REPEAT
  FORMSUBST_FV TERMSUBST_FVT FORMSUBST_SAFE_FOR SAFE_FOR_VALMOD SAFE_FOR_ASSIGN
  safe_for TERMSUBST_TERMSUBST
  closed numeral termval holds arithtrue
  TERMVAL_NUMERAL HOLDS_FORMSUBST HOLDS_VALUATION TERMVAL_VALMOD_OTHER)
-- Names from Arithmetic/godel.ml that sigmacomplete.ml reuses.
open HolLogicArith.Godel (SIGMAPI_CLAUSES SIGMAPI_FORMSUBST SIGMA PI
  complete_for sound_for consistent CONSISTENT_ALT G1_TRAD)
-- Names from Arithmetic/tarski.ml that sigmacomplete.ml reuses.
open HolLogicArith.Tarski (definable definable_by)

namespace HolLogicArith.SigmaComplete
-- Names from Arithmetic/derived.ml (the module sigmacomplete.ml imports).
open HolLogicArith.Derived

/- The session's `prove` lifted into `ExceptT String IO`. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- Local, corrected `FORMSUBST_CONV` and specialization rules.

   Derived.FORMSUBST_CONV is faithful to derived.ml but hits a HolLean bug:
   its `safeConv` combines the two `FORMSUBST_SAFE_FOR` PART_MATCH attempts with
   ExceptT's `<|>`, and `<|>` does NOT recover from the `.error` returned by the
   coerced `Session.PART_MATCH` (the first, `!!`, attempt), so a `formsubst v (??x p)`
   term — which only arises here, not in derived.ml — fails with `term_pmatch`
   instead of falling through to the `??` clause.  derived.ml never applies
   FORMSUBST_CONV to an existential, so the bug is invisible there; sigmacomplete.ml
   does (via `spec_rule`/`specl_rule` on `le_def`, whose body contains `??`).  We
   reproduce derived.ml's algorithm exactly, replacing only the broken `<|>` with an
   explicit match, and build the specialization rules on top of it. -/
private unsafe def FORMSUBST_CONV : HolCore.Equal.ioconv := fun tm => ((do
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
    let th ← ExceptT.mk (do
      match ← Session.PART_MATCH (fun t => do HolCore.Equal.lhand (← rand t)) c1 tm with
      | .ok t => pure (.ok t)
      | .error _ => Session.PART_MATCH (fun t => do HolCore.Equal.lhand (← rand t)) c2 tm)
    let lh ← liftExcept (HolCore.Equal.lhand (HolCore.Kernel.concl th))
    let sfr ← (ExceptT.lift (SAFE_FOR_RULE lh) : ExceptT String IO thm)
    liftExcept (Session.MP th sfr) : ExceptT String IO thm).run)
  ExceptT.mk ((HolLight.GEN_REWRITE_CONV HolCore.Lib.I [f0, f1] ORELSEC
    (HolLight.GEN_REWRITE_CONV HolCore.Lib.I [f2, f3, f4] THENC HolLight.BINOP_CONV TERMSUBST_CONV) ORELSEC
    (HolLight.GEN_REWRITE_CONV HolCore.Lib.I [f5] THENC HolLight.RAND_CONV FORMSUBST_CONV) ORELSEC
    (HolLight.GEN_REWRITE_CONV HolCore.Lib.I [f6, f7, f8, f9] THENC HolLight.BINOP_CONV FORMSUBST_CONV) ORELSEC
    (safeConv THENC HolLight.RAND_CONV FORMSUBST_CONV)) tm) : ExceptT String IO thm).run)

/- `instantiate_rule`/`specl_rule`/`spec_rule` as in derived.ml, over the local
   (corrected) FORMSUBST_CONV. -/
private unsafe def instantiate_rule (ilist : List (term × Nat)) (th : thm) : ExceptT String IO thm := do
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

private unsafe def specl_rule (tms : List term) (th : thm) : ExceptT String IO thm := do
  let bop ← (HolCore.Parser.parse_term "(!!):num->form->form")
  let rhsTh ← liftExcept (rand (HolCore.Kernel.concl th))
  let avs := HolCore.Lib.striplist (fun t => HolCore.Basics.dest_binop bop t) rhsTh
  let vs ← liftExcept (do pure ((← HolCore.Lib.chop_list tms.length avs).1))
  let ilist ← liftExcept ((tms.zip vs).mapM (fun (t, v) => do
      let n ← Session.dest_small_numeral v
      pure (t, n.toNat)))
  let th' ← vs.foldlM (fun t _ => HolLight.MATCH_MP spec_var t) th
  instantiate_rule ilist th'

private unsafe def spec_rule (t : term) (th : thm) : ExceptT String IO thm := specl_rule [t] th

private unsafe def ITLIST : thm := Session.listDefs.ITLIST

-- Replay Arithmetic/derived.ml (the one module sigmacomplete.ml imports).
#eval HolLogicArith.Derived.ensure

#eval phrase 1
unsafe def robinson : thm := keep "robinson" fun _ => new_definition
  [[robinson =
        (!!0 (!!1 (Suc(V 0) === Suc(V 1) --> V 0 === V 1))) &&
        (!!1 (Not(V 1 === Z) <-> ??0 (V 1 === Suc(V 0)))) &&
        (!!1 (Z ++ V 1 === V 1)) &&
        (!!0 (!!1 (Suc(V 0) ++ V 1 === Suc(V 0 ++ V 1)))) &&
        (!!1 (Z ** V 1 === Z)) &&
        (!!0 (!!1 (Suc(V 0) ** V 1 === V 1 ++ V 0 ** V 1))) &&
        (!!0 (!!1 (V 0 <<= V 1 <-> ??2 (V 0 ++ V 2 === V 1)))) &&
        (!!0 (!!1 (V 0 << V 1 <-> Suc(V 0) <<= V 1)))]]
#eval robinson

#eval phrase 2
/- let [suc_inj; num_cases; add_0; add_suc; mul_0; mul_suc; le_def; lt_def] =
     CONJUNCTS(REWRITE_RULE[META_AND] (GEN_REWRITE_RULE RAND_CONV [robinson]
     (MATCH_MP assume (SET_RULE `robinson IN {robinson}`)))) -/
private unsafe def robinson_axioms : thm := keep "robinson_axioms" fun _ => (do
  let setr ← ExceptT.mk (Session.SET_RULE [[robinson IN {robinson}]])
  let asm ← HolLight.MATCH_MP «assume» setr
  let gr ← HolLight.GEN_REWRITE_RULE HolLight.RAND_CONV [robinson] asm
  HolLight.REWRITE_RULE [META_AND] gr
  : ExceptT String IO thm).run
unsafe def suc_inj : thm := keep "suc_inj" fun _ => (Session.CONJUNCTS robinson_axioms)[0]!
unsafe def num_cases : thm := keep "num_cases" fun _ => (Session.CONJUNCTS robinson_axioms)[1]!
unsafe def add_0 : thm := keep "add_0" fun _ => (Session.CONJUNCTS robinson_axioms)[2]!
unsafe def add_suc : thm := keep "add_suc" fun _ => (Session.CONJUNCTS robinson_axioms)[3]!
unsafe def mul_0 : thm := keep "mul_0" fun _ => (Session.CONJUNCTS robinson_axioms)[4]!
unsafe def mul_suc : thm := keep "mul_suc" fun _ => (Session.CONJUNCTS robinson_axioms)[5]!
unsafe def le_def : thm := keep "le_def" fun _ => (Session.CONJUNCTS robinson_axioms)[6]!
unsafe def lt_def : thm := keep "lt_def" fun _ => (Session.CONJUNCTS robinson_axioms)[7]!
#eval do IO.println suc_inj; IO.println num_cases; IO.println add_0; IO.println add_suc; IO.println mul_0; IO.println mul_suc; IO.println le_def; IO.println lt_def

#eval phrase 3
unsafe def «suc_inj'» : thm := keep "suc_inj'" fun _ => (do
  prove ([[!s t. {robinson} |-- Suc(s) === Suc(t) --> s === t]])
   (REWRITE_TAC [← specl_rule [ [[s:term]], [[t:term]] ] suc_inj])
  : ExceptT String IO thm).run
#eval «suc_inj'»

#eval phrase 4
unsafe def «num_cases'» : thm := keep "num_cases'" fun _ => (do
  prove ([[!t z. ~(z IN FVT t)
           ==> {robinson} |--  (Not(t === Z) <-> ??z (t === Suc(V z)))]])
   (HolLight.tactic_of do
     -- OCaml evaluates the tactic tree's embedded rule calls right-to-left, so the
     -- MESON[imp_refl] lemma (rightmost, deepest) is elaborated early; force it and
     -- the two SET_RULEs in that order so the "inventing type variables" warning and
     -- the solve traces land where HOL Light prints them.
     let mlem ← MESON [imp_refl] [[p = q ==> A |-- p --> q]]
     let setr2 ← Session.SET_RULE [[a IN s ==> s UNION {a} = s]]
     let itrans ← HolLight.REWRITE_RULE [IMP_CONJ_ALT] iff_trans
     let caj ← HolLight.GSYM CONJ_ASSOC
     let setr1 ← Session.SET_RULE [[({1} UNION {0}) DELETE 0 = {1} DIFF {0}]]
     pure
      (REPEAT STRIP_TAC THEN
       MP_TAC (← ((do
         let sp ← HolLight.MATCH_MP spec num_cases
         HolLight.SPEC ([[t:term]]) sp) : ExceptT String IO thm)) THEN
       REWRITE_TAC [formsubst] THEN
       CONV_TAC (HolLight.ONCE_DEPTH_CONV TERMSUBST_CONV) THEN
       REWRITE_TAC [FV, FVT, setr1] THEN
       REWRITE_TAC [IN_DIFF, IN_SING, UNWIND_THM2, caj, ASSIGN] THEN
       REWRITE_TAC [ARITH_EQ] THEN LET_TAC THEN
       MATCH_MP_TAC itrans THEN
       SUBGOAL_THEN ([[~(z' IN FVT t)]]) ASSUME_TAC THENL
        [EXPAND_TAC "z'" THEN COND_CASES_TAC THEN
         ASM_SIMP_TAC [setr2, VARIANT_FINITE, FVT_FINITE],
         MATCH_MP_TAC imp_antisym THEN
         ASM_CASES_TAC ([[z':num = z]]) THEN ASM_REWRITE_TAC [imp_refl] THEN
         CONJ_TAC THEN MATCH_MP_TAC ichoose THEN
         ASM_REWRITE_TAC [FV, IN_DELETE, IN_UNION, IN_SING, FVT] THEN
         MATCH_MP_TAC gen THEN MATCH_MP_TAC imp_trans THENL
          [EXISTS_TAC ([[formsubst (z |=> V z') (t === Suc(V z))]]),
           EXISTS_TAC ([[formsubst (z' |=> V z) (t === Suc(V z'))]])] THEN
         REWRITE_TAC [iexists] THEN REWRITE_TAC [formsubst] THEN
         ASM_REWRITE_TAC [termsubst, ASSIGN] THEN
         MATCH_MP_TAC mlem THEN
         AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC HolLight.SYM_CONV THEN
         MATCH_MP_TAC TERMSUBST_TRIVIAL THEN REWRITE_TAC [ASSIGN] THEN
         ASM_MESON_TAC []]))
  : ExceptT String IO thm).run
#eval «num_cases'»

#eval phrase 5
unsafe def «add_0'» : thm := keep "add_0'" fun _ => (do
  prove ([[!t. {robinson} |--  Z ++ t === t]])
   (REWRITE_TAC [← spec_rule ([[t:term]]) add_0])
  : ExceptT String IO thm).run
#eval «add_0'»

#eval phrase 6
unsafe def «add_suc'» : thm := keep "add_suc'" fun _ => (do
  prove ([[!s t. {robinson} |--  Suc(s) ++ t === Suc(s ++ t)]])
   (REWRITE_TAC [← specl_rule [ [[s:term]], [[t:term]] ] add_suc])
  : ExceptT String IO thm).run
#eval «add_suc'»

#eval phrase 7
unsafe def «mul_0'» : thm := keep "mul_0'" fun _ => (do
  prove ([[!t. {robinson} |--  Z ** t === Z]])
   (REWRITE_TAC [← spec_rule ([[t:term]]) mul_0])
  : ExceptT String IO thm).run
#eval «mul_0'»

#eval phrase 8
unsafe def «mul_suc'» : thm := keep "mul_suc'" fun _ => (do
  prove ([[!s t. {robinson} |--  Suc(s) ** t === t ++ s ** t]])
   (REWRITE_TAC [← specl_rule [ [[s:term]], [[t:term]] ] mul_suc])
  : ExceptT String IO thm).run
#eval «mul_suc'»

#eval phrase 9
unsafe def «lt_def'» : thm := keep "lt_def'" fun _ => (do
  prove ([[!s t. {robinson} |--  (s << t <-> Suc(s) <<= t)]])
   (REWRITE_TAC [← specl_rule [ [[s:term]], [[t:term]] ] lt_def])
  : ExceptT String IO thm).run
#eval «lt_def'»

#eval phrase 10
unsafe def SIGMA1_COMPLETE_ADD : thm := keep "SIGMA1_COMPLETE_ADD" fun _ => (do
  prove ([[!m n. {robinson} |-- numeral m ++ numeral n === numeral(m + n)]])
   (INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, numeral] THEN
    ASM_MESON_TAC [«add_0'», «add_suc'», axiom_funcong, eq_trans, modusponens])
  : ExceptT String IO thm).run
#eval SIGMA1_COMPLETE_ADD

#eval phrase 11
unsafe def SIGMA1_COMPLETE_MUL : thm := keep "SIGMA1_COMPLETE_MUL" fun _ => (do
  prove ([[!m n. {robinson} |-- (numeral m ** numeral n === numeral(m * n))]])
   (INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES, numeral] THENL
     [ASM_MESON_TAC [«mul_0'»], ALL_TAC] THEN
    GEN_TAC THEN MATCH_MP_TAC eq_trans_rule THEN
    EXISTS_TAC ([[numeral(n) ++ numeral(m * n)]]) THEN CONJ_TAC THENL
     [ASM_MESON_TAC [«mul_suc'», eq_trans_rule, axiom_funcong, imp_trans,
                    modusponens, imp_swap, add_assum, axiom_eqrefl],
      ASM_MESON_TAC [SIGMA1_COMPLETE_ADD, ADD_SYM, eq_trans_rule]])
  : ExceptT String IO thm).run
#eval SIGMA1_COMPLETE_MUL

#eval phrase 12
unsafe def SIGMA1_COMPLETE_TERM : thm := keep "SIGMA1_COMPLETE_TERM" fun _ => (do
  prove ([[!v t n. FVT t = {} /\ termval v t = n
           ==> {robinson} |-- (t === numeral n)]])
   (HolLight.tactic_of do
     let lemma ← prove ([[(!n. p /\ (x = n) ==> P n) <=> p ==> P x]]) (MESON_TAC [])
     pure
      (GEN_TAC THEN MATCH_MP_TAC term_INDUCT THEN
       REWRITE_TAC [termval, FVT, NOT_INSERT_EMPTY] THEN CONJ_TAC THENL
        [GEN_TAC THEN DISCH_THEN (SUBST1_TAC oTIO HolLight.SYM) THEN REWRITE_TAC [numeral] THEN
         MESON_TAC [axiom_eqrefl, add_assum],
         ALL_TAC] THEN
       REWRITE_TAC [lemma] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
       DISCH_THEN (fun th => REPEAT STRIP_TAC THEN MP_TAC th) THEN
       RULE_ASSUM_TAC (HolLight.REWRITE_RULE [EMPTY_UNION]) THEN ASM_REWRITE_TAC [numeral] THEN
       MESON_TAC [SIGMA1_COMPLETE_ADD, SIGMA1_COMPLETE_MUL,
                 cong_suc, cong_add, cong_mul, eq_trans_rule]))
  : ExceptT String IO thm).run
#eval SIGMA1_COMPLETE_TERM

#eval phrase 13
/- let canonize_clauses = ... and false_imp = ... and true_imp = ... -/
unsafe def canonize_clauses : thm := keep "canonize_clauses" fun _ => (do
  let lemma0 ← ExceptT.mk (MESON [imp_refl, imp_swap, modusponens, axiom_doubleneg]
    [[!A p. A |-- (p --> False) --> False <=> A |-- p]])
  let lemma1 ← ExceptT.mk (MESON [iff_imp1, iff_imp2, modusponens, imp_trans]
   [[A |-- p <-> q
    ==> (A |-- p <=> A |-- q) /\ (A |-- p --> False <=> A |-- q --> False)]])
  let ths ← pure [axiom_true, axiom_not, axiom_and, axiom_or, iff_def, axiom_exists]
  ths.foldrM (fun th acc => do
      let sa ← liftExcept (Session.SPEC_ALL th)
      let mm ← HolLight.MATCH_MP lemma1 sa
      liftExcept (Session.CONJ mm acc))
    lemma0
  : ExceptT String IO thm).run
unsafe def false_imp : thm := keep "false_imp" fun _ => (ExceptT.mk (MESON [imp_truefalse, modusponens]
    [[A |-- p /\ A |-- q --> False ==> A |-- (p --> q) --> False]]) : ExceptT String IO thm).run
unsafe def true_imp : thm := keep "true_imp" fun _ => (ExceptT.mk (MESON [axiom_addimp, modusponens, ex_falso, imp_trans]
   [[A |-- p --> False \/ A |-- q ==> A |-- p --> q]]) : ExceptT String IO thm).run
#eval do
  let a ← pure canonize_clauses
  let b ← pure false_imp
  let c ← pure true_imp
  IO.println a; IO.println b; IO.println c

#eval phrase 14
unsafe def CANONIZE_TAC : HolCore.Tactics.tactic :=
  REWRITE_TAC [canonize_clauses, imp_refl] THEN
  REPEAT ((MATCH_MP_TAC false_imp THEN CONJ_TAC) ORELSE
         MATCH_MP_TAC true_imp THEN
         REWRITE_TAC [canonize_clauses, imp_refl])
#eval do IO.println "<fun>"

#eval phrase 15
unsafe def suc_inj_eq : thm := keep "suc_inj_eq" fun _ => (do
  prove ([[!s t. {robinson} |-- Suc s === Suc t <-> s === t]])
   (MESON_TAC [«suc_inj'», axiom_funcong, imp_antisym])
  : ExceptT String IO thm).run
#eval suc_inj_eq

#eval phrase 16
unsafe def suc_le_eq : thm := keep "suc_le_eq" fun _ => (do
  prove ([[!s t. {robinson} |-- Suc s <<= Suc t <-> s <<= t]])
   (gens_tac [0,1] THEN
    TRANS_TAC iff_trans ([[??2 (Suc(V 0) ++ V 2 === Suc(V 1))]]) THEN
    REWRITE_TAC [← ([ ([[Suc(V 1)]]:term), ([[Suc(V 0)]]:term) ].foldrM spec_rule le_def)] THEN
    TRANS_TAC iff_trans ([[??2 (V 0 ++ V 2 === V 1)]]) THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [iff_sym] THEN
    REWRITE_TAC [← ([ ([[V 1]]:term), ([[V 0]]:term) ].foldrM spec_rule le_def)] THEN
    MATCH_MP_TAC exiff THEN
    TRANS_TAC iff_trans ([[Suc(V 0 ++ V 2) === Suc(V 1)]]) THEN
    REWRITE_TAC [suc_inj_eq] THEN MATCH_MP_TAC cong_eq THEN
    REWRITE_TAC [axiom_eqrefl, «add_suc'»])
  : ExceptT String IO thm).run
#eval suc_le_eq

#eval phrase 17
unsafe def le_iff_lt : thm := keep "le_iff_lt" fun _ => (do
  prove ([[!s t. {robinson} |-- s <<= t <-> s << Suc t]])
   (REPEAT GEN_TAC THEN TRANS_TAC iff_trans ([[Suc s <<= Suc t]]) THEN
    ONCE_REWRITE_TAC [iff_sym] THEN
    REWRITE_TAC [suc_le_eq, «lt_def'»])
  : ExceptT String IO thm).run
#eval le_iff_lt

#eval phrase 18
unsafe def suc_lt_eq : thm := keep "suc_lt_eq" fun _ => (do
  prove ([[!s t. {robinson} |-- Suc s << Suc t <-> s << t]])
   (MESON_TAC [iff_sym, iff_trans, le_iff_lt, «lt_def'»])
  : ExceptT String IO thm).run
#eval suc_lt_eq

#eval phrase 19
unsafe def not_suc_eq_0 : thm := keep "not_suc_eq_0" fun _ => (do
  prove ([[!t. {robinson} |-- Suc t === Z --> False]])
   (gen_tac 1 THEN
    SUBGOAL_THEN ([[{robinson} |-- Not(Suc(V 1) === Z)]]) MP_TAC THENL
     [ALL_TAC, REWRITE_TAC [canonize_clauses]] THEN
    SUBGOAL_THEN ([[{robinson} |-- ?? 0 (Suc(V 1) === Suc(V 0))]]) MP_TAC THENL
     [MATCH_MP_TAC exists_intro THEN EXISTS_TAC ([[V 1]]) THEN
      CONV_TAC (HolLight.RAND_CONV FORMSUBST_CONV) THEN REWRITE_TAC [axiom_eqrefl],
      MESON_TAC [iff_imp2, modusponens, ← spec_rule ([[Suc(V 1)]]) num_cases]])
  : ExceptT String IO thm).run
#eval not_suc_eq_0

#eval phrase 20
unsafe def not_suc_le_0 : thm := keep "not_suc_le_0" fun _ => (do
  prove ([[!t. {robinson} |-- Suc t <<= Z --> False]])
   (X_GEN_TAC ([[s:term]]) THEN
    SUBGOAL_THEN ([[{robinson} |-- !!0 (Suc(V 0) <<= Z --> False)]]) MP_TAC THENL
     [ALL_TAC, DISCH_THEN (fun th => HolLight.tactic_of do
        let sp ← spec_rule ([[s:term]]) th
        pure (ACCEPT_TAC sp))] THEN
    MATCH_MP_TAC gen THEN
    SUBGOAL_THEN ([[{robinson} |-- ?? 2 (Suc (V 0) ++ V 2 === Z) --> False]])
    MP_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ] imp_trans) THEN
      MATCH_MP_TAC iff_imp1 THEN
      ACCEPT_TAC (← ([ ([[Z]]:term), ([[Suc(V 0)]]:term) ].foldrM spec_rule le_def))] THEN
    MATCH_MP_TAC ichoose THEN REWRITE_TAC [FV, NOT_IN_EMPTY] THEN
    MATCH_MP_TAC gen THEN TRANS_TAC imp_trans ([[Suc(V 0 ++ V 2) === Z]]) THEN
    REWRITE_TAC [not_suc_eq_0] THEN MATCH_MP_TAC iff_imp1 THEN
    MATCH_MP_TAC cong_eq THEN REWRITE_TAC [axiom_eqrefl] THEN
    REWRITE_TAC [«add_suc'»])
  : ExceptT String IO thm).run
#eval not_suc_le_0

#eval phrase 21
unsafe def not_lt_0 : thm := keep "not_lt_0" fun _ => (do
  prove ([[!t. {robinson} |-- t << Z --> False]])
   (MESON_TAC [not_suc_le_0, «lt_def'», imp_trans, iff_imp1])
  : ExceptT String IO thm).run
#eval not_lt_0

#eval phrase 22
unsafe def add_0_right : thm := keep "add_0_right" fun _ => (do
  prove ([[!n. {robinson} |-- numeral n ++ Z === numeral n]])
   (GEN_TAC THEN MP_TAC (← ExceptT.mk (HolLight.ISPECL [ [[n:num]], [[0]] ] SIGMA1_COMPLETE_ADD)) THEN
    REWRITE_TAC [numeral, ADD_CLAUSES])
  : ExceptT String IO thm).run
#eval add_0_right

#eval phrase 23
unsafe def ATOM_EQ_FALSE : thm := keep "ATOM_EQ_FALSE" fun _ => (do
  prove ([[!m n. ~(m = n) ==> {robinson} |-- numeral m === numeral n --> False]])
   (ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC [] THEN CONJ_TAC THENL
     [MESON_TAC [eq_sym, imp_trans], ALL_TAC] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    INDUCT_TAC THEN REWRITE_TAC [(← HolLight.CONJUNCT1 LT)] THEN INDUCT_TAC THEN
    REWRITE_TAC [numeral, not_suc_eq_0, LT_SUC, SUC_INJ] THEN
    ASM_MESON_TAC [suc_inj_eq, imp_trans, iff_imp1, iff_imp2])
  : ExceptT String IO thm).run
#eval ATOM_EQ_FALSE

#eval phrase 24
unsafe def ATOM_LE_FALSE : thm := keep "ATOM_LE_FALSE" fun _ => (do
  prove ([[!m n. n < m ==> {robinson} |-- numeral m <<= numeral n --> False]])
   (INDUCT_TAC THEN REWRITE_TAC [(← HolLight.CONJUNCT1 LT)] THEN
    INDUCT_TAC THEN REWRITE_TAC [numeral, not_suc_le_0, LT_SUC] THEN
    ASM_MESON_TAC [suc_le_eq, imp_trans, iff_imp1, iff_imp2])
  : ExceptT String IO thm).run
#eval ATOM_LE_FALSE

#eval phrase 25
unsafe def ATOM_LT_FALSE : thm := keep "ATOM_LT_FALSE" fun _ => (do
  prove ([[!m n. n <= m ==> {robinson} |-- numeral m << numeral n --> False]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [(← HolLight.GSYM LT_SUC_LE)] THEN
    DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP ATOM_LE_FALSE) THEN
    REWRITE_TAC [numeral] THEN
    ASM_MESON_TAC [«lt_def'», imp_trans, iff_imp1, iff_imp2])
  : ExceptT String IO thm).run
#eval ATOM_LT_FALSE

#eval phrase 26
unsafe def ATOM_EQ_TRUE : thm := keep "ATOM_EQ_TRUE" fun _ => (do
  prove ([[!m n. m = n ==> {robinson} |-- numeral m === numeral n]])
   (MESON_TAC [axiom_eqrefl])
  : ExceptT String IO thm).run
#eval ATOM_EQ_TRUE

#eval phrase 27
unsafe def ATOM_LE_TRUE : thm := keep "ATOM_LE_TRUE" fun _ => (do
  prove ([[!m n. m <= n ==> {robinson} |-- numeral m <<= numeral n]])
   (SUBGOAL_THEN ([[!m n. {robinson} |-- numeral m <<= numeral(m + n)]])
    MP_TAC THENL [ALL_TAC, MESON_TAC [LE_EXISTS]] THEN
    REPEAT GEN_TAC THEN MATCH_MP_TAC modusponens THEN
    EXISTS_TAC ([[?? 2 (numeral m ++ V 2 === numeral(m + n))]]) THEN
    CONJ_TAC THENL
     [MP_TAC (← ([ ([[numeral(m + n)]]:term), ([[numeral m]]:term) ].foldrM spec_rule le_def)) THEN
      MESON_TAC [iff_imp2],
      MATCH_MP_TAC exists_intro THEN EXISTS_TAC ([[numeral n]]) THEN
      CONV_TAC (HolLight.RAND_CONV FORMSUBST_CONV) THEN
      REWRITE_TAC [SIGMA1_COMPLETE_ADD]])
  : ExceptT String IO thm).run
#eval ATOM_LE_TRUE

#eval phrase 28
unsafe def ATOM_LT_TRUE : thm := keep "ATOM_LT_TRUE" fun _ => (do
  prove ([[!m n. m < n ==> {robinson} |-- numeral m << numeral n]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [(← HolLight.GSYM LE_SUC_LT)] THEN
    DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP ATOM_LE_TRUE) THEN
    REWRITE_TAC [numeral] THEN
    ASM_MESON_TAC [«lt_def'», modusponens, iff_imp1, iff_imp2])
  : ExceptT String IO thm).run
#eval ATOM_LT_TRUE

#eval phrase 29
unsafe def FORMSUBST_FORMSUBST_SAME_NONE : thm := keep "FORMSUBST_FORMSUBST_SAME_NONE" fun _ => (do
  prove ([[!s t x p.
        FVT t = {x} /\ FVT s = {}
        ==> formsubst (x |=> s) (formsubst (x |=> t) p) =
            formsubst (x |=> termsubst (x |=> s) t) p]])
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[!y. safe_for y (x |=> termsubst (x |=> s) t)]]) ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [SAFE_FOR_ASSIGN, TERMSUBST_FVT, ASSIGN] THEN
      ASM SET_TAC [FVT],
      ALL_TAC] THEN
    MATCH_MP_TAC form_INDUCT THEN
    ASM_SIMP_TAC [FORMSUBST_SAFE_FOR, SAFE_FOR_ASSIGN, IN_SING, NOT_IN_EMPTY] THEN
    SIMP_TAC [formsubst] THEN
    MATCH_MP_TAC (← TAUT [[(p /\ q /\ r) /\ s ==> p /\ q /\ r /\ s]]) THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN BINOP_TAC THEN
      REWRITE_TAC [TERMSUBST_TERMSUBST] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [o_DEF, FUN_EQ_THM] THEN X_GEN_TAC ([[y:num]]) THEN
      REWRITE_TAC [ASSIGN] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC [termsubst, ASSIGN],
      CONJ_TAC THEN MAP_EVERY X_GEN_TAC [ [[y:num]], [[p:form]] ] THEN DISCH_TAC THEN
      (ASM_CASES_TAC ([[y:num = x]]) THENL
       [ASM_REWRITE_TAC [assign, VALMOD_VALMOD_BASIC] THEN
        SIMP_TAC [VALMOD_TRIVIAL, FORMSUBST_TRIV],
        SUBGOAL_THEN ([[!u. (y |-> V y) (x |=> u) = (x |=> u)]])
         (fun th => ASM_REWRITE_TAC [th]) THEN
        GEN_TAC THEN MATCH_MP_TAC VALMOD_TRIVIAL THEN
        ASM_REWRITE_TAC [ASSIGN]])])
  : ExceptT String IO thm).run
#eval FORMSUBST_FORMSUBST_SAME_NONE

#eval phrase 30
unsafe def num_cases_rule : thm := keep "num_cases_rule" fun _ => (do
  prove ([[!p x. {robinson} |-- formsubst (x |=> Z) p /\
         {robinson} |-- formsubst (x |=> Suc(V x)) p
         ==> {robinson} |-- p]])
   (HolLight.tactic_of do
     let lemma ← prove
      ([[!A p x t. A |-- formsubst (x |=> t) p ==> A |-- V x === t --> p]])
      (REPEAT GEN_TAC THEN
       MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ] modusponens) THEN
       MATCH_MP_TAC imp_swap THEN
       GEN_REWRITE_TAC (funpow 3 HolLight.RAND_CONV) [(← HolLight.GSYM FORMSUBST_TRIV)] THEN
       CONV_TAC (funpow 3 HolLight.RAND_CONV (HolCore.Equal.SUBS_CONV [(← HolLight.SYM (← HolLight.SPEC ([[x:num]]) ASSIGN_TRIV))])) THEN
       TRANS_TAC imp_trans ([[t === V x]]) THEN REWRITE_TAC [isubst, eq_sym])
     pure
      (REPEAT GEN_TAC THEN
       GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.RAND_CONV) [(← HolLight.GSYM FORMSUBST_TRIV)] THEN
       CONV_TAC (HolLight.RAND_CONV (HolCore.Equal.SUBS_CONV [(← HolLight.SYM (← HolLight.SPEC ([[x:num]]) ASSIGN_TRIV))])) THEN
       SUBGOAL_THEN ([[?z. ~(z = x) /\ ~(z IN VARS p)]]) STRIP_ASSUME_TAC THENL
        [EXISTS_TAC ([[VARIANT(x INSERT VARS p)]]) THEN
         REWRITE_TAC [(← HolLight.GSYM DE_MORGAN_THM), (← HolLight.GSYM IN_INSERT)] THEN
         MATCH_MP_TAC NOT_IN_VARIANT THEN
         SIMP_TAC [VARS_FINITE, FINITE_INSERT, SUBSET_REFL],
         ALL_TAC] THEN
       FIRST_X_ASSUM (fun th => HolLight.tactic_of do
         let ft ← HolLight.MATCH_MP FORMSUBST_TWICE th
         let gft ← HolLight.GSYM ft
         pure (ONCE_REWRITE_TAC [gft])) THEN
       SUBGOAL_THEN ([[~(x IN FV(formsubst (x |=> V z) p))]]) MP_TAC THENL
        [REWRITE_TAC [FORMSUBST_FV, IN_ELIM_THM, ASSIGN, NOT_EXISTS_THM] THEN
         GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [FVT] THEN
         ASM SET_TAC [],
         ALL_TAC] THEN
       SPEC_TAC ([[formsubst (x |=> V z) p]], [[p:form]]) THEN
       REPEAT STRIP_TAC THEN MATCH_MP_TAC spec THEN MATCH_MP_TAC gen THEN
       FIRST_X_ASSUM (MP_TAC oTIO HolLight.MATCH_MP lemma) THEN
       DISCH_THEN (fun th => HolLight.tactic_of do
         let gth ← HolLight.MATCH_MP gen th
         let sp ← HolLight.SPEC ([[x:num]]) gth
         pure (MP_TAC sp)) THEN
       DISCH_THEN (fun th => HolLight.tactic_of do
         let rr ← HolLight.REWRITE_RULE [IMP_CONJ] ichoose
         let mm ← HolLight.MATCH_MP rr th
         pure (MP_TAC mm)) THEN
       FIRST_X_ASSUM (MP_TAC oTIO HolLight.MATCH_MP lemma) THEN ASM_REWRITE_TAC [IMP_IMP] THEN
       DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP ante_disj) THEN
       MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ_ALT] modusponens) THEN
       MP_TAC (← ExceptT.mk (HolLight.ISPECL [ [[V z]], [[x:num]] ] «num_cases'»)) THEN
       ASM_REWRITE_TAC [FVT, IN_SING] THEN
       DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP iff_imp1) THEN
       REWRITE_TAC [canonize_clauses] THEN
       MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ_ALT] imp_trans) THEN
       MESON_TAC [imp_swap, axiom_not, iff_imp1, imp_trans]))
  : ExceptT String IO thm).run
#eval num_cases_rule

#eval phrase 31
unsafe def SIGMAPI1_COMPLETE : thm := keep "SIGMAPI1_COMPLETE" fun _ => (do
  prove ([[!v p b. sigmapi b 1 p /\ closed p
           ==> (b /\ holds v p ==> {robinson} |-- p) /\
               (~b /\ ~holds v p ==> {robinson} |-- p --> False)]])
   (HolLight.tactic_of do
     let lemma1 ← prove
      ([[!x n p. (!m. m < n ==> {robinson} |-- formsubst (x |=> numeral m) p)
             ==> {robinson} |-- !!x (V x << numeral n --> p)]])
      (GEN_TAC THEN INDUCT_TAC THEN X_GEN_TAC ([[p:form]]) THEN DISCH_TAC THEN
       REWRITE_TAC [numeral] THENL
        [ASM_MESON_TAC [gen, imp_trans, ex_falso, not_lt_0], ALL_TAC] THEN
       MATCH_MP_TAC gen THEN MATCH_MP_TAC num_cases_rule THEN
       EXISTS_TAC ([[x:num]]) THEN CONJ_TAC THENL
        [ONCE_REWRITE_TAC [formsubst] THEN MATCH_MP_TAC add_assum THEN
         REWRITE_TAC [(← HolLight.GSYM numeral)] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC,
         ALL_TAC] THEN
       REWRITE_TAC [formsubst, termsubst, TERMSUBST_NUMERAL, ASSIGN] THEN
       TRANS_TAC imp_trans ([[V x << numeral n]]) THEN
       CONJ_TAC THENL [MESON_TAC [suc_lt_eq, iff_imp1], ALL_TAC] THEN
       MATCH_MP_TAC spec_var THEN EXISTS_TAC ([[x:num]]) THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       X_GEN_TAC ([[m:num]]) THEN DISCH_TAC THEN
       FIRST_X_ASSUM (MP_TAC oTIO HolLight.SPEC ([[SUC m]])) THEN
       ASM_REWRITE_TAC [LT_SUC] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
       HolCore.Lib.W (fun gl => HolLight.tactic_of do
           let pm ← Session.PART_MATCH (fun t => do HolCore.Equal.lhs (← rand t))
                      FORMSUBST_FORMSUBST_SAME_NONE (← rand (HolLight.snd gl))
           pure (MP_TAC pm)) THEN
       REWRITE_TAC [FVT, FVT_NUMERAL] THEN DISCH_THEN SUBST1_TAC THEN
       REWRITE_TAC [termsubst, ASSIGN, numeral])
     let lemma2 ← prove
      ([[!x n p. (!m. m <= n ==> {robinson} |-- formsubst (x |=> numeral m) p)
             ==> {robinson} |-- !!x (V x <<= numeral n --> p)]])
      (REPEAT STRIP_TAC THEN
       MP_TAC (← ExceptT.mk (HolLight.ISPECL [ [[x:num]], [[SUC n]], [[p:form]] ] lemma1)) THEN
       ASM_REWRITE_TAC [LT_SUC_LE] THEN DISCH_TAC THEN MATCH_MP_TAC gen THEN
       FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP spec_var) THEN REWRITE_TAC [numeral] THEN
       MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ] imp_trans) THEN
       MESON_TAC [iff_imp1, le_iff_lt])
     let lemma3 ← prove
      ([[!v x t p.
          FVT t = {} /\
          (!m. m < termval v t
               ==> {robinson} |-- formsubst (x |=> numeral m) p)
          ==> {robinson} |-- !!x (V x << t --> p)]])
      (REPEAT STRIP_TAC THEN MATCH_MP_TAC gen THEN
       FIRST_ASSUM (fun th => HolLight.tactic_of do
         let m1 ← HolLight.MATCH_MP lemma1 th
         let m2 ← HolLight.MATCH_MP spec_var m1
         pure (MP_TAC m2)) THEN
       MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ] imp_trans) THEN
       MATCH_MP_TAC iff_imp1 THEN MATCH_MP_TAC cong_lt THEN
       REWRITE_TAC [axiom_eqrefl] THEN MATCH_MP_TAC SIGMA1_COMPLETE_TERM THEN
       ASM_MESON_TAC [])
     let lemma4 ← prove
      ([[!v x t p.
          FVT t = {} /\
          (!m. m <= termval v t
               ==> {robinson} |-- formsubst (x |=> numeral m) p)
          ==> {robinson} |-- !!x (V x <<= t --> p)]])
      (REPEAT STRIP_TAC THEN MATCH_MP_TAC gen THEN
       FIRST_ASSUM (fun th => HolLight.tactic_of do
         let m1 ← HolLight.MATCH_MP lemma2 th
         let m2 ← HolLight.MATCH_MP spec_var m1
         pure (MP_TAC m2)) THEN
       MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ] imp_trans) THEN
       MATCH_MP_TAC iff_imp1 THEN MATCH_MP_TAC cong_le THEN
       REWRITE_TAC [axiom_eqrefl] THEN MATCH_MP_TAC SIGMA1_COMPLETE_TERM THEN
       ASM_MESON_TAC [])
     let lemma5 ← prove
      ([[!A x p q. A |-- !!x (p --> Not q) ==> A |-- !!x (Not(p && q))]])
      (REPEAT STRIP_TAC THEN MATCH_MP_TAC gen THEN
       FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP spec_var) THEN
       REWRITE_TAC [canonize_clauses] THEN
       MESON_TAC [imp_trans, axiom_not, iff_imp1, iff_imp2])
     pure
      (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [closed] THEN
       WF_INDUCT_TAC ([[complexity p]]) THEN
       POP_ASSUM MP_TAC THEN SPEC_TAC ([[p:form]], [[p:form]]) THEN
       MATCH_MP_TAC form_INDUCT THEN
       REWRITE_TAC [SIGMAPI_CLAUSES, complexity, ARITH] THEN
       REWRITE_TAC [(← MESON [] [[(if p then q else F) <=> p /\ q]])] THEN
       ONCE_REWRITE_TAC
        [(← TAUT [[a /\ b /\ c /\ d /\ e /\ f /\ g /\ h /\ i /\ j /\ k /\ l <=>
          (a /\ b) /\ (c /\ d /\ e) /\ f /\ (g /\ h /\ i /\ j) /\ (k /\ l)]])] THEN
       CONJ_TAC THENL
        [CONJ_TAC THEN DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN REWRITE_TAC [holds] THEN
         MESON_TAC [imp_refl, truth],
         ALL_TAC] THEN
       CONJ_TAC THENL
        [REPEAT CONJ_TAC THEN MAP_EVERY X_GEN_TAC [ [[s:term]], [[t:term]] ] THEN
         DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN X_GEN_TAC ([[b:bool]]) THEN
         REWRITE_TAC [FV, EMPTY_UNION] THEN STRIP_TAC THEN
         MP_TAC (← ExceptT.mk (HolLight.ISPECL [ [[v:num->num]], [[t:term]], [[termval v t]] ]
             SIGMA1_COMPLETE_TERM)) THEN
         MP_TAC (← ExceptT.mk (HolLight.ISPECL [ [[v:num->num]], [[s:term]], [[termval v s]] ]
             SIGMA1_COMPLETE_TERM)) THEN
         ASM_REWRITE_TAC [IMP_IMP] THENL
          [DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP cong_eq),
           DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP cong_lt),
           DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP cong_le)] THEN
         STRIP_TAC THEN REWRITE_TAC [holds, NOT_LE, NOT_LT] THEN
         (REPEAT STRIP_TAC THENL
           [FIRST_X_ASSUM (fun th => HolLight.tactic_of do
              let mm ← HolLight.MATCH_MP iff_imp2 th
              let rr ← HolLight.REWRITE_RULE [IMP_CONJ] modusponens
              let m2 ← HolLight.MATCH_MP rr mm
              pure (MATCH_MP_TAC m2)),
            FIRST_X_ASSUM (fun th => HolLight.tactic_of do
              let mm ← HolLight.MATCH_MP iff_imp1 th
              let rr ← HolLight.REWRITE_RULE [IMP_CONJ] imp_trans
              let m2 ← HolLight.MATCH_MP rr mm
              pure (MATCH_MP_TAC m2))]) THEN
         ASM_SIMP_TAC [ATOM_EQ_FALSE, ATOM_EQ_TRUE, ATOM_LT_FALSE, ATOM_LT_TRUE,
                      ATOM_LE_FALSE, ATOM_LE_TRUE],
         ALL_TAC] THEN
       CONJ_TAC THENL
        [X_GEN_TAC ([[p:form]]) THEN DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
         DISCH_THEN (MP_TAC oTIO HolLight.SPEC ([[p:form]])) THEN
         ANTS_TAC THENL [ARITH_TAC, DISCH_TAC] THEN
         X_GEN_TAC ([[b:bool]]) THEN REWRITE_TAC [FV] THEN STRIP_TAC THEN
         FIRST_X_ASSUM (MP_TAC oTIO HolLight.SPEC ([[~b]])) THEN ASM_REWRITE_TAC [holds] THEN
         BOOL_CASES_TAC ([[b:bool]]) THEN CANONIZE_TAC THEN ASM_MESON_TAC [],
         ALL_TAC] THEN
       CONJ_TAC THENL
        [REPEAT CONJ_TAC THEN
         MAP_EVERY X_GEN_TAC [ [[p:form]], [[q:form]] ] THEN DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
         DISCH_TAC THEN X_GEN_TAC ([[b:bool]]) THEN REWRITE_TAC [FV, EMPTY_UNION] THEN
         STRIP_TAC THEN FIRST_X_ASSUM (fun th => HolLight.tactic_of do
           let sp ← HolLight.SPEC ([[p:form]]) th
           let sq ← HolLight.SPEC ([[q:form]]) th
           pure (MP_TAC sp THEN MP_TAC sq)) THEN
         (ANTS_TAC THENL [ARITH_TAC, ALL_TAC]) THEN
         ONCE_REWRITE_TAC [(← TAUT [[p ==> q ==> r <=> q ==> p ==> r]])] THEN
         (ANTS_TAC THENL [ARITH_TAC, ASM_REWRITE_TAC [IMP_IMP]]) THEN
         ASM_REWRITE_TAC [holds, canonize_clauses] THENL
          [DISCH_THEN (CONJUNCTS_THEN (MP_TAC oTIO HolLight.SPEC ([[b:bool]]))),
           DISCH_THEN (CONJUNCTS_THEN (MP_TAC oTIO HolLight.SPEC ([[b:bool]]))),
           DISCH_THEN (CONJUNCTS_THEN2
            (MP_TAC oTIO HolLight.SPEC ([[~b]])) (MP_TAC oTIO HolLight.SPEC ([[b:bool]]))),
           DISCH_THEN (CONJUNCTS_THEN (fun th => HolLight.tactic_of do
             let sb ← HolLight.SPEC ([[~b]]) th
             let sb2 ← HolLight.SPEC ([[b:bool]]) th
             pure (MP_TAC sb THEN MP_TAC sb2)))] THEN
         ASM_REWRITE_TAC [] THEN BOOL_CASES_TAC ([[b:bool]]) THEN
         ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN CANONIZE_TAC THEN
         TRY (FIRST_X_ASSUM (fun th => HolLight.tactic_of do
                let t1 ← TAUT [[~(p <=> q) ==> (p /\ ~q ==> r) /\ (~p /\ q ==> s) ==> r \/ s]]
                let mm ← HolLight.MATCH_MP t1 th
                pure (MATCH_MP_TAC mm THEN REPEAT STRIP_TAC THEN CANONIZE_TAC)) ) THEN
         ASM_MESON_TAC [],
         ALL_TAC] THEN
       CONJ_TAC THEN MAP_EVERY X_GEN_TAC [ [[x:num]], [[p:form]] ] THEN
       DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN REWRITE_TAC [canonize_clauses, holds] THEN
       DISCH_TAC THEN X_GEN_TAC ([[b:bool]]) THENL
        [BOOL_CASES_TAC ([[b:bool]]) THEN ASM_REWRITE_TAC [] THENL
          [REWRITE_TAC [IMP_IMP, (← HolLight.GSYM CONJ_ASSOC), FV] THEN
           ONCE_REWRITE_TAC [IMP_CONJ] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
           MAP_EVERY X_GEN_TAC [ [[q:form]], [[t:term]] ] THEN DISCH_THEN
            (CONJUNCTS_THEN2 (DISJ_CASES_THEN SUBST_ALL_TAC) ASSUME_TAC) THEN
           REWRITE_TAC [SIGMAPI_CLAUSES, FV, holds] THEN
           (ASM_CASES_TAC ([[FVT t = {}]]) THENL [ALL_TAC, ASM SET_TAC []]) THEN
           (ASM_CASES_TAC ([[FV(q) SUBSET {x}]]) THENL [ALL_TAC, ASM SET_TAC []]) THEN
           DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o Session.CONJUNCT2)) THEN
           ABBREV_TAC ([[n = termval v t]]) THEN
           ASM_SIMP_TAC [TERMVAL_VALMOD_OTHER, termval, VALMOD] THENL
            [DISCH_TAC THEN MATCH_MP_TAC lemma3,
             DISCH_TAC THEN MATCH_MP_TAC lemma4] THEN
           EXISTS_TAC ([[v:num->num]]) THEN
           ASM_REWRITE_TAC [] THEN X_GEN_TAC ([[m:num]]) THEN DISCH_TAC THEN
           FIRST_X_ASSUM (MP_TAC oTIO HolLight.SPEC ([[formsubst (x |=> numeral m) q]])) THEN
           REWRITE_TAC [complexity, COMPLEXITY_FORMSUBST] THEN
           (ANTS_TAC THENL [ARITH_TAC, DISCH_THEN (MP_TAC oTIO HolLight.SPEC ([[T]]))]) THEN
           REWRITE_TAC [IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
           ASM_SIMP_TAC [SIGMAPI_FORMSUBST] THEN
           REWRITE_TAC [FORMSUBST_FV, ASSIGN] THEN
           REPLICATE_TAC 2 (ONCE_REWRITE_TAC [COND_RAND]) THEN
           REWRITE_TAC [FVT_NUMERAL, NOT_IN_EMPTY, FVT, IN_SING] THEN
           (CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC]) THEN
           FIRST_X_ASSUM (MP_TAC oTIO HolLight.SPEC ([[m:num]])) THEN ASM_REWRITE_TAC [] THEN
           REWRITE_TAC [HOLDS_FORMSUBST] THEN
           MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC HOLDS_VALUATION THEN
           X_GEN_TAC ([[y:num]]) THEN
           (ASM_CASES_TAC ([[y:num = x]]) THENL [ALL_TAC, ASM SET_TAC []]) THEN
           ASM_REWRITE_TAC [o_DEF, ASSIGN, VALMOD, TERMVAL_NUMERAL],
           STRIP_TAC THEN REWRITE_TAC [NOT_FORALL_THM, LEFT_IMP_EXISTS_THM] THEN
           X_GEN_TAC ([[n:num]]) THEN DISCH_TAC THEN MATCH_MP_TAC imp_trans THEN
           EXISTS_TAC ([[formsubst (x |=> numeral n) p]]) THEN REWRITE_TAC [ispec] THEN
           FIRST_X_ASSUM (MP_TAC oTIO HolLight.SPEC ([[formsubst (x |=> numeral n) p]])) THEN
           REWRITE_TAC [COMPLEXITY_FORMSUBST, (← ARITH_RULE [[n < n + 1]])] THEN
           DISCH_THEN (MP_TAC oTIO HolLight.SPEC ([[F]])) THEN
           ASM_SIMP_TAC [SIGMAPI_FORMSUBST, IMP_IMP] THEN
           DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
            [UNDISCH_TAC ([[FV (!! x p) = {}]]) THEN
             REWRITE_TAC [FV, FORMSUBST_FV, (← Session.SET_RULE
              [[s DELETE a = {} <=> s = {} \/ s = {a}]])] THEN STRIP_TAC THEN
             ASM_REWRITE_TAC [NOT_IN_EMPTY, IN_SING, EMPTY_GSPEC,
                             ASSIGN, UNWIND_THM2, FVT_NUMERAL],
             UNDISCH_TAC ([[~holds((x |-> n) v) p]]) THEN
             REWRITE_TAC [HOLDS_FORMSUBST, CONTRAPOS_THM] THEN
             MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC HOLDS_VALUATION THEN
             RULE_ASSUM_TAC (HolLight.REWRITE_RULE [FV]) THEN X_GEN_TAC ([[y:num]]) THEN
             ASM_CASES_TAC ([[y:num = x]]) THENL [ALL_TAC, ASM SET_TAC []] THEN
             ASM_REWRITE_TAC [o_THM, ASSIGN, VALMOD, TERMVAL_NUMERAL]]],
         BOOL_CASES_TAC ([[b:bool]]) THEN ASM_REWRITE_TAC [] THENL
          [REWRITE_TAC [FV] THEN STRIP_TAC THEN
           DISCH_THEN (X_CHOOSE_TAC ([[n:num]])) THEN
           FIRST_X_ASSUM (MP_TAC oTIO HolLight.SPEC ([[formsubst (x |=> numeral n) (Not p)]])) THEN
           REWRITE_TAC [COMPLEXITY_FORMSUBST, complexity] THEN
           ANTS_TAC THENL [ASM_ARITH_TAC, DISCH_THEN (MP_TAC oTIO HolLight.SPEC ([[F]]))] THEN
           ASM_SIMP_TAC [IMP_IMP, SIGMAPI_CLAUSES, SIGMAPI_FORMSUBST] THEN
           ANTS_TAC THENL
            [REWRITE_TAC [FORMSUBST_FV, ASSIGN] THEN
             REPLICATE_TAC 2 (ONCE_REWRITE_TAC [COND_RAND]) THEN
             REWRITE_TAC [FVT_NUMERAL, NOT_IN_EMPTY, FVT, FV, IN_SING] THEN
             (CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC]) THEN
             UNDISCH_TAC ([[holds ((x |-> n) v) p]]) THEN
             REWRITE_TAC [formsubst, holds, HOLDS_FORMSUBST] THEN
             MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC HOLDS_VALUATION THEN
             RULE_ASSUM_TAC (HolLight.REWRITE_RULE [FV]) THEN X_GEN_TAC ([[y:num]]) THEN
             ASM_CASES_TAC ([[y:num = x]]) THENL [ALL_TAC, ASM SET_TAC []] THEN
             ASM_REWRITE_TAC [o_THM, ASSIGN, VALMOD, TERMVAL_NUMERAL],
             MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ] imp_trans) THEN
             REWRITE_TAC [ispec]],
           REWRITE_TAC [IMP_IMP, (← HolLight.GSYM CONJ_ASSOC), FV] THEN
           ONCE_REWRITE_TAC [IMP_CONJ] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
           MAP_EVERY X_GEN_TAC [ [[q:form]], [[t:term]] ] THEN DISCH_THEN
            (CONJUNCTS_THEN2 (DISJ_CASES_THEN SUBST_ALL_TAC) ASSUME_TAC) THEN
           REWRITE_TAC [SIGMAPI_CLAUSES, FV, holds] THEN
           (ASM_CASES_TAC ([[FVT t = {}]]) THENL [ALL_TAC, ASM SET_TAC []]) THEN
           (ASM_CASES_TAC ([[FV(q) SUBSET {x}]]) THENL [ALL_TAC, ASM SET_TAC []]) THEN
           DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o Session.CONJUNCT2)) THEN
           ABBREV_TAC ([[n = termval v t]]) THEN
           ASM_SIMP_TAC [TERMVAL_VALMOD_OTHER, termval, VALMOD] THEN
           REWRITE_TAC [NOT_EXISTS_THM, (← TAUT [[~(p /\ q) <=> p ==> ~q]])] THEN
           DISCH_TAC THEN MATCH_MP_TAC lemma5 THENL
            [MATCH_MP_TAC lemma3, MATCH_MP_TAC lemma4] THEN
           EXISTS_TAC ([[v:num->num]]) THEN
           ASM_REWRITE_TAC [] THEN X_GEN_TAC ([[m:num]]) THEN DISCH_TAC THEN
           FIRST_X_ASSUM (MP_TAC oTIO HolLight.SPEC ([[formsubst (x |=> numeral m) (Not q)]])) THEN
           REWRITE_TAC [complexity, COMPLEXITY_FORMSUBST] THEN
           (ANTS_TAC THENL [ARITH_TAC, DISCH_THEN (MP_TAC oTIO HolLight.SPEC ([[T]]))]) THEN
           REWRITE_TAC [IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
           ASM_SIMP_TAC [SIGMAPI_FORMSUBST, SIGMAPI_CLAUSES] THEN
           REWRITE_TAC [FORMSUBST_FV, FV, ASSIGN] THEN
           REPLICATE_TAC 2 (ONCE_REWRITE_TAC [COND_RAND]) THEN
           REWRITE_TAC [FVT_NUMERAL, NOT_IN_EMPTY, FVT, IN_SING] THEN
           (CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC]) THEN
           FIRST_X_ASSUM (MP_TAC oTIO HolLight.SPEC ([[m:num]])) THEN ASM_REWRITE_TAC [] THEN
           REWRITE_TAC [HOLDS_FORMSUBST, holds, CONTRAPOS_THM] THEN
           MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC HOLDS_VALUATION THEN
           X_GEN_TAC ([[y:num]]) THEN
           (ASM_CASES_TAC ([[y:num = x]]) THENL [ALL_TAC, ASM SET_TAC []]) THEN
           ASM_REWRITE_TAC [o_DEF, ASSIGN, VALMOD, TERMVAL_NUMERAL]]]))
  : ExceptT String IO thm).run
#eval SIGMAPI1_COMPLETE

#eval phrase 32
unsafe def G1_ROBINSON : thm := keep "G1_ROBINSON" fun _ => (do
  prove ([[!A. definable_by (SIGMA 1) (IMAGE gform A) /\
       consistent A /\ A |-- robinson
       ==> ?G. PI 1 G /\
               closed G /\
               arithtrue G /\
               ~(A |-- G) /\
               (sound_for (SIGMA 1 INTER closed) A ==> ~(A |-- Not G))]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC G1_TRAD THEN
    ASM_REWRITE_TAC [complete_for, INTER, IN_ELIM_THM] THEN
    X_GEN_TAC ([[p:form]]) THEN REWRITE_TAC [IN, arithtrue] THEN STRIP_TAC THEN
    MATCH_MP_TAC modusponens THEN EXISTS_TAC ([[robinson]]) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC PROVES_MONO THEN
    EXISTS_TAC ([[{}:form->bool]]) THEN REWRITE_TAC [EMPTY_SUBSET] THEN
    HolCore.Lib.W (fun gl => HolLight.tactic_of do
        let pm ← Session.PART_MATCH (fun t => do HolCore.Equal.lhs (← rand t)) DEDUCTION (HolLight.snd gl)
        pure (MP_TAC pm)) THEN
    MP_TAC (← ExceptT.mk (HolLight.ISPECL [ [[I:num->num]], [[p:form]], [[T]] ] SIGMAPI1_COMPLETE)) THEN
    ASM_REWRITE_TAC [(← HolLight.GSYM SIGMA)] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [robinson, closed, FV, FVT] THEN
    SET_TAC [])
  : ExceptT String IO thm).run
#eval G1_ROBINSON

#eval phrase 33
unsafe def complete : thm := keep "complete" fun _ => new_definition
  [[complete A <=> !p. closed p ==> A |-- p \/ A |-- Not p]]
#eval complete

#eval phrase 34
unsafe def sound : thm := keep "sound" fun _ => new_definition
  [[sound A <=> !p. A |-- p ==> arithtrue p]]
#eval sound

#eval phrase 35
unsafe def semcomplete : thm := keep "semcomplete" fun _ => new_definition
  [[semcomplete A <=> !p. arithtrue p ==> A |-- p]]
#eval semcomplete

#eval phrase 36
unsafe def generalize : thm := keep "generalize" fun _ => new_definition
  [[generalize vs p = ITLIST (!!) vs p]]
#eval generalize

#eval phrase 37
unsafe def closure : thm := keep "closure" fun _ => new_definition
  [[closure p = generalize (list_of_set(FV p)) p]]
#eval closure

#eval phrase 38
unsafe def TRUE_GENERALIZE : thm := keep "TRUE_GENERALIZE" fun _ => (do
  prove ([[!vs p. arithtrue(generalize vs p) <=> arithtrue p]])
   (REWRITE_TAC [generalize, arithtrue] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [ITLIST, holds] THEN GEN_TAC THEN
    FIRST_X_ASSUM (fun th => HolLight.tactic_of do
      let gth ← HolLight.GSYM th
      pure (GEN_REWRITE_TAC HolLight.RAND_CONV [gth])) THEN
    MESON_TAC [VALMOD_REPEAT])
  : ExceptT String IO thm).run
#eval TRUE_GENERALIZE

#eval phrase 39
unsafe def PROVABLE_GENERALIZE : thm := keep "PROVABLE_GENERALIZE" fun _ => (do
  prove ([[!A p vs. A |-- generalize vs p <=> A |-- p]])
   (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [generalize] THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [ITLIST] THEN FIRST_X_ASSUM (SUBST1_TAC oTIO HolLight.SYM) THEN
    MESON_TAC [spec, gen, FORMSUBST_TRIV, ASSIGN_TRIV])
  : ExceptT String IO thm).run
#eval PROVABLE_GENERALIZE

#eval phrase 40
unsafe def FV_GENERALIZE : thm := keep "FV_GENERALIZE" fun _ => (do
  prove ([[!p vs. FV(generalize vs p) = FV(p) DIFF (set_of_list vs)]])
   (GEN_TAC THEN REWRITE_TAC [generalize] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [set_of_list, DIFF_EMPTY, ITLIST] THEN
    ASM_REWRITE_TAC [FV] THEN SET_TAC [])
  : ExceptT String IO thm).run
#eval FV_GENERALIZE

#eval phrase 41
unsafe def CLOSED_CLOSURE : thm := keep "CLOSED_CLOSURE" fun _ => (do
  prove ([[!p. closed(closure p)]])
   (REWRITE_TAC [closed, closure, FV_GENERALIZE] THEN
    SIMP_TAC [SET_OF_LIST_OF_SET, FV_FINITE, DIFF_EQ_EMPTY])
  : ExceptT String IO thm).run
#eval CLOSED_CLOSURE

#eval phrase 42
unsafe def TRUE_CLOSURE : thm := keep "TRUE_CLOSURE" fun _ => (do
  prove ([[!p. arithtrue(closure p) <=> arithtrue p]])
   (REWRITE_TAC [closure, TRUE_GENERALIZE])
  : ExceptT String IO thm).run
#eval TRUE_CLOSURE

#eval phrase 43
unsafe def PROVABLE_CLOSURE : thm := keep "PROVABLE_CLOSURE" fun _ => (do
  prove ([[!A p. A |-- closure p <=> A |-- p]])
   (REWRITE_TAC [closure, PROVABLE_GENERALIZE])
  : ExceptT String IO thm).run
#eval PROVABLE_CLOSURE

#eval phrase 44
unsafe def DEFINABLE_DEFINABLE_BY : thm := keep "DEFINABLE_DEFINABLE_BY" fun _ => (do
  prove ([[definable = definable_by (\x. T)]])
   (REWRITE_TAC [FUN_EQ_THM, definable, definable_by])
  : ExceptT String IO thm).run
#eval DEFINABLE_DEFINABLE_BY

#eval phrase 45
unsafe def DEFINABLE_ONEVAR : thm := keep "DEFINABLE_ONEVAR" fun _ => (do
  prove ([[definable s <=> ?p x. (FV p = {x}) /\ !v. holds v p <=> (v x) IN s]])
   (REWRITE_TAC [definable] THEN EQ_TAC THENL [ALL_TAC, MESON_TAC []] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[p:form]]) (X_CHOOSE_TAC ([[x:num]]))) THEN
    EXISTS_TAC ([[(V x === V x) && formsubst (\y. if y = x then V x else Z) p]]) THEN
    EXISTS_TAC ([[x:num]]) THEN
    ASM_REWRITE_TAC [HOLDS_FORMSUBST, FORMSUBST_FV, FV, holds] THEN
    REWRITE_TAC [COND_RAND, EXTENSION, IN_ELIM_THM, IN_SING, FVT, IN_UNION,
                COND_EXPAND, NOT_IN_EMPTY, o_THM, termval] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval DEFINABLE_ONEVAR

#eval phrase 46
unsafe def CLOSED_TRUE_OR_FALSE : thm := keep "CLOSED_TRUE_OR_FALSE" fun _ => (do
  prove ([[!p. closed p ==> arithtrue p \/ arithtrue(Not p)]])
   (REWRITE_TAC [closed, arithtrue, holds] THEN REPEAT STRIP_TAC THEN
    ASM_MESON_TAC [HOLDS_VALUATION, NOT_IN_EMPTY])
  : ExceptT String IO thm).run
#eval CLOSED_TRUE_OR_FALSE

#eval phrase 47
unsafe def SEMCOMPLETE_IMP_COMPLETE : thm := keep "SEMCOMPLETE_IMP_COMPLETE" fun _ => (do
  prove ([[!A. semcomplete A ==> complete A]])
   (REWRITE_TAC [semcomplete, complete] THEN MESON_TAC [CLOSED_TRUE_OR_FALSE])
  : ExceptT String IO thm).run
#eval SEMCOMPLETE_IMP_COMPLETE

#eval phrase 48
unsafe def SOUND_CLOSED : thm := keep "SOUND_CLOSED" fun _ => (do
  prove ([[sound A <=> !p. closed p /\ A |-- p ==> arithtrue p]])
   (REWRITE_TAC [sound] THEN EQ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
    MESON_TAC [TRUE_CLOSURE, PROVABLE_CLOSURE, CLOSED_CLOSURE])
  : ExceptT String IO thm).run
#eval SOUND_CLOSED

#eval phrase 49
unsafe def SOUND_IMP_CONSISTENT : thm := keep "SOUND_IMP_CONSISTENT" fun _ => (do
  prove ([[!A. sound A ==> consistent A]])
   (REWRITE_TAC [sound, consistent, CONSISTENT_ALT] THEN
    SUBGOAL_THEN ([[~(arithtrue False)]]) (fun th => MESON_TAC [th]) THEN
    REWRITE_TAC [arithtrue, holds])
  : ExceptT String IO thm).run
#eval SOUND_IMP_CONSISTENT

#eval phrase 50
unsafe def SEMCOMPLETE_SOUND_EQ_CONSISTENT : thm := keep "SEMCOMPLETE_SOUND_EQ_CONSISTENT" fun _ => (do
  prove ([[!A. semcomplete A ==> (sound A <=> consistent A)]])
   (REWRITE_TAC [semcomplete] THEN REPEAT STRIP_TAC THEN EQ_TAC THEN
    REWRITE_TAC [SOUND_IMP_CONSISTENT] THEN
    REWRITE_TAC [consistent, SOUND_CLOSED] THEN
    ASM_MESON_TAC [CLOSED_TRUE_OR_FALSE])
  : ExceptT String IO thm).run
#eval SEMCOMPLETE_SOUND_EQ_CONSISTENT

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.SigmaComplete" do
  replay (
          HolLogicArith.Derived.ensure)
  replay (
          robinson)
  replay (
          do IO.println suc_inj; IO.println num_cases; IO.println add_0; IO.println add_suc; IO.println mul_0; IO.println mul_suc; IO.println le_def; IO.println lt_def)
  replay (
          «suc_inj'»)
  replay (
          «num_cases'»)
  replay (
          «add_0'»)
  replay (
          «add_suc'»)
  replay (
          «mul_0'»)
  replay (
          «mul_suc'»)
  replay (
          «lt_def'»)
  replay (
          SIGMA1_COMPLETE_ADD)
  replay (
          SIGMA1_COMPLETE_MUL)
  replay (
          SIGMA1_COMPLETE_TERM)
  replay (
          do
      let a ← pure canonize_clauses
      let b ← pure false_imp
      let c ← pure true_imp
      IO.println a; IO.println b; IO.println c)
  replay (
          do IO.println "<fun>")
  replay (
          suc_inj_eq)
  replay (
          suc_le_eq)
  replay (
          le_iff_lt)
  replay (
          suc_lt_eq)
  replay (
          not_suc_eq_0)
  replay (
          not_suc_le_0)
  replay (
          not_lt_0)
  replay (
          add_0_right)
  replay (
          ATOM_EQ_FALSE)
  replay (
          ATOM_LE_FALSE)
  replay (
          ATOM_LT_FALSE)
  replay (
          ATOM_EQ_TRUE)
  replay (
          ATOM_LE_TRUE)
  replay (
          ATOM_LT_TRUE)
  replay (
          FORMSUBST_FORMSUBST_SAME_NONE)
  replay (
          num_cases_rule)
  replay (
          SIGMAPI1_COMPLETE)
  replay (
          G1_ROBINSON)
  replay (
          complete)
  replay (
          sound)
  replay (
          semcomplete)
  replay (
          generalize)
  replay (
          closure)
  replay (
          TRUE_GENERALIZE)
  replay (
          PROVABLE_GENERALIZE)
  replay (
          FV_GENERALIZE)
  replay (
          CLOSED_CLOSURE)
  replay (
          TRUE_CLOSURE)
  replay (
          PROVABLE_CLOSURE)
  replay (
          DEFINABLE_DEFINABLE_BY)
  replay (
          DEFINABLE_ONEVAR)
  replay (
          CLOSED_TRUE_OR_FALSE)
  replay (
          SEMCOMPLETE_IMP_COMPLETE)
  replay (
          SOUND_CLOSED)
  replay (
          SOUND_IMP_CONSISTENT)
  replay (
          SEMCOMPLETE_SOUND_EQ_CONSISTENT)
-- @@ENSURE END

end HolLogicArith.SigmaComplete
