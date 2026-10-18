/- File: IndTypes.lean
Inductive (or free recursive) types.
John Harrison, University of Cambridge Computer Laboratory

Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026 -/

import HolCore.Bool
import HolCore.Equal
import HolCore.Drule
import HolCore.Tactics
import HolCore.Itab
import HolCore.Simp
import HolCore.Parser
import HolCore.Printer
import HolCore.Nets
import HolCore.Theorems
import HolCore.IndDefs
import HolCore.Classic
import HolCore.Trivia
import HolCore.Canon
import HolCore.Meson
import HolCore.ImpConv
import HolMath.Pair
import HolMath.Nums
import HolMath.Recursion
import HolMath.Arith
import HolMath.Wf
import HolMath.CalcNum
import HolMath.Normalizer
import HolMath.Grobner
import HolMath.Base

namespace HolMath.IndTypes

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/-- The definitions and theorems of `ind_types.ml` lines 13-300: the
    number-pairing and injection infrastructure used to carve out an
    inductively defined set inside `num->A->bool`, and the lifted
    constructor/recursion theorems built on top of it.

    Field names match the OCaml identifiers exactly, in OCaml order. -/
structure IndTypesThms where
  /- Abstract left inverses for binary injections (13-25). -/
  INJ_INVERSE2     : thm
  /- An injective pairing function on `:num` (29-52). -/
  NUMPAIR          : thm
  NUMPAIR_INJ_LEMMA : thm
  NUMPAIR_INJ      : thm
  NUMPAIR_DEST     : thm
  /- An injective map `bool->num->num` (55-71). -/
  NUMSUM           : thm
  NUMSUM_INJ       : thm
  NUMSUM_DEST      : thm
  /- Injection `num->Z`, where `Z == num->A->bool` (74-85). -/
  INJN             : thm
  INJN_INJ         : thm
  /- Injection `A->Z`, where `Z == num->A->bool` (87-98). -/
  INJA             : thm
  INJA_INJ         : thm
  /- Injection `(num->Z)->Z`, where `Z == num->A->bool` (100-114). -/
  INJF             : thm
  INJF_INJ         : thm
  /- Injection `Z->Z->Z`, where `Z == num->A->bool` (116-132). -/
  INJP             : thm
  INJP_INJ         : thm
  /- "Constructor" and "bottom" element (134-147). -/
  ZCONSTR          : thm
  ZBOT             : thm
  ZCONSTR_ZBOT     : thm
  /- The inductively defined set `ZRECSPACE` (149-155). -/
  ZRECSPACE_RULES  : thm
  ZRECSPACE_INDUCT : thm
  ZRECSPACE_CASES  : thm
  /- The `recspace` type definition (157-160). -/
  recspace_tydef   : thm × thm
  /- Lifted constructors (162-171). -/
  BOTTOM           : thm
  CONSTR           : thm
  /- Some lemmas (173-190). -/
  MK_REC_INJ       : thm
  DEST_REC_INJ     : thm
  /- The set is freely inductively generated (192-239). -/
  CONSTR_BOT       : thm
  CONSTR_INJ       : thm
  CONSTR_IND       : thm
  /- The recursion theorem (241-280). -/
  CONSTR_REC       : thm
  /- Coding up functions casewise (282-296). -/
  FCONS            : thm
  FCONS_UNDO       : thm
  FNIL             : thm
  deriving Inhabited

/-- ind_types.ml 13-297: the number-pairing and injection infrastructure,
    the inductively defined ZRECSPACE, the recspace type, its
    free-generation lemmas, the recursion theorem, and the casewise coding
    helpers.  The definition principles depend on session state, so Session
    passes them in. -/
@[nospecialize]
def setupIndTypes [HolBase]
    (Nm : HolMath.Nums.NumsThms)
    (Ar1 : HolMath.Arith.ArithThms1) (Ar2 : HolMath.Arith.ArithThms2)
    (Ar5 : HolMath.Arith.ArithThms5) (CnA : HolMath.CalcNum.ArithRewrites)
    (Tv : HolCore.Trivia.TriviaThms) (ETA_AX : thm)
    (new_definition' : term → IO (Except String thm))
    (new_specification' : List String → thm → IO (Except String thm))
    (new_inductive_definition' : term → IO (Except String (thm × thm × thm)))
    (new_recursive_definition' : thm → term → IO (Except String thm))
    (prove_inductive_relations_exist' : term → IO (Except String thm)) :
    ExceptT String IO IndTypesThms := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let new_specification (ns : List String) (th : thm) : ExceptT String IO thm :=
    new_specification' ns th
  let new_inductive_definition (s : String) :
      ExceptT String IO (thm × thm × thm) := do
    new_inductive_definition' (← q s)
  let new_recursive_definition (ax : thm) (s : String) : ExceptT String IO thm := do
    new_recursive_definition' ax (← q s)
  let prove_inductive_relations_exist (t : term) : ExceptT String IO thm :=
    prove_inductive_relations_exist' t
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC Nm.num_INDUCTION
  let { NOT_SUC, SUC_INJ, num_RECURSION, .. } := Nm
  let { EXP, MULT_ASSOC, EQ_MULT_LCANCEL, EXP_EQ_0, .. } := Ar2
  let { EQ_ADD_RCANCEL, .. } := Ar1
  let { EVEN, EVEN_MULT, EVEN_ADD, EVEN_DOUBLE, .. } := Ar5
  let { ARITH, .. } := CnA
  let { o_THM, .. } := Tv
  let { BETA_THM, AND_FORALL_THM, FORALL_AND_THM, EXISTS_UNIQUE_REFL,
        EXISTS_UNIQUE_THM, UNWIND_THM1, RIGHT_EXISTS_AND_THM, CONJ_ASSOC, .. } := HolBase.T
  let { FUN_EQ_THM, SELECT_UNIQUE, SKOLEM_THM, UNIQUE_SKOLEM_ALT, .. } := HolBase.C
  -- `W(C SUBGOAL_THEN ASSUME_TAC o funpow 2 lhand o snd)`.
  let SUBGOAL_LHAND2_TAC : tactic :=
    W (fun g => tactic_of do pure (C SUBGOAL_THEN ASSUME_TAC (← funpowM 2 lhand (snd g))))

  /- Abstract left inverses for binary injections (we could construct them...) -/

  let INJ_INVERSE2 ← prove
   r"!P:A->B->C.
    (!x1 y1 x2 y2. (P x1 y1 = P x2 y2) <=> (x1 = x2) /\ (y1 = y2))
    ==> ?X Y. !x y. (X(P x y) = x) /\ (Y(P x y) = y)"
   (GEN_TAC THEN DISCH_TAC THEN
    EXISTS_TAC (← q r"\z:C. @x:A. ?y:B. P x y = z") THEN
    EXISTS_TAC (← q r"\z:C. @y:B. ?x:A. P x y = z") THEN
    REPEAT GEN_TAC THEN ASM_REWRITE_TAC [BETA_THM] THEN
    CONJ_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN GEN_TAC THEN BETA_TAC THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    W (fun g => tactic_of do pure (EXISTS_TAC (← rand (← dest_exists (snd g)).2))) THEN
    REFL_TAC)

  /- Define an injective pairing function on ":num". -/

  let NUMPAIR ← new_definition
   r"NUMPAIR x y = (2 EXP x) * (2 * y + 1)"

  let NUMPAIR_INJ_LEMMA ← prove
   r"!x1 y1 x2 y2. (NUMPAIR x1 y1 = NUMPAIR x2 y2) ==> (x1 = x2)"
   (REWRITE_TAC [NUMPAIR] THEN REPEAT (INDUCT_TAC THEN GEN_TAC) THEN
    ASM_REWRITE_TAC [EXP, ← GSYM MULT_ASSOC, ARITH, EQ_MULT_LCANCEL,
      NOT_SUC, ← GSYM NOT_SUC, SUC_INJ] THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"EVEN")) THEN
    REWRITE_TAC [EVEN_MULT, EVEN_ADD, ARITH])

  let NUMPAIR_INJ ← prove
   r"!x1 y1 x2 y2. (NUMPAIR x1 y1 = NUMPAIR x2 y2) <=> (x1 = x2) /\ (y1 = y2)"
   (REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (SUBST_ALL_TAC o MATCH_MP NUMPAIR_INJ_LEMMA) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [NUMPAIR] THEN
    REWRITE_TAC [EQ_MULT_LCANCEL, EQ_ADD_RCANCEL, EXP_EQ_0, ARITH])

  let NUMPAIR_DEST ← new_specification
    ["NUMFST", "NUMSND"]
    (← MATCH_MP INJ_INVERSE2 NUMPAIR_INJ)

  /- Also, an injective map bool->num->num (even easier!) -/

  let NUMSUM ← new_definition
   r"NUMSUM b x = if b then SUC(2 * x) else 2 * x"

  let NUMSUM_INJ ← prove
   r"!b1 x1 b2 x2. (NUMSUM b1 x1 = NUMSUM b2 x2) <=> (b1 = b2) /\ (x1 = x2)"
   (REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    POP_ASSUM (MP_TAC o REWRITE_RULE [NUMSUM]) THEN
    DISCH_THEN (fun th => tactic_of do pure (
      MP_TAC th THEN MP_TAC (← AP_TERM (← q r"EVEN") th))) THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC [EVEN, EVEN_DOUBLE] THEN
    REWRITE_TAC [SUC_INJ, EQ_MULT_LCANCEL, ARITH])

  let NUMSUM_DEST ← new_specification
    ["NUMLEFT", "NUMRIGHT"]
    (← MATCH_MP INJ_INVERSE2 NUMSUM_INJ)

  /- Injection num->Z, where Z == num->A->bool. -/

  let INJN ← new_definition
   r"INJN (m:num) = \(n:num) (a:A). n = m"

  let INJN_INJ ← prove
   r"!n1 n2. (INJN n1 :num->A->bool = INJN n2) <=> (n1 = n2)"
   (REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    POP_ASSUM (MP_TAC o C AP_THM (← q r"n1:num") o REWRITE_RULE [INJN]) THEN
    DISCH_THEN (MP_TAC o C AP_THM (← q r"a:A")) THEN REWRITE_TAC [BETA_THM])

  /- Injection A->Z, where Z == num->A->bool. -/

  let INJA ← new_definition
   r"INJA (a:A) = \(n:num) b. b = a"

  let INJA_INJ ← prove
   r"!a1 a2. (INJA a1 = INJA a2) <=> (a1:A = a2)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [INJA, FUN_EQ_THM] THEN EQ_TAC THENL
     [DISCH_THEN (MP_TAC o SPEC (← q r"a1:A")) THEN REWRITE_TAC [],
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC []])

  /- Injection (num->Z)->Z, where Z == num->A->bool. -/

  let INJF ← new_definition
   r"INJF (f:num->(num->A->bool)) = \n. f (NUMFST n) (NUMSND n)"

  let INJF_INJ ← prove
   r"!f1 f2. (INJF f1 :num->A->bool = INJF f2) <=> (f1 = f2)"
   (REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [FUN_EQ_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"m:num", ← q r"a:A"] THEN
    POP_ASSUM (MP_TAC o REWRITE_RULE [INJF]) THEN
    DISCH_THEN (MP_TAC o C AP_THM (← q r"a:A") o C AP_THM (← q r"NUMPAIR n m")) THEN
    REWRITE_TAC [NUMPAIR_DEST])

  /- Injection Z->Z->Z, where Z == num->A->bool. -/

  let INJP ← new_definition
   r"INJP f1 f2:num->A->bool =
        \n a. if NUMLEFT n then f1 (NUMRIGHT n) a else f2 (NUMRIGHT n) a"

  let INJP_INJ ← prove
   r"!(f1:num->A->bool) f1' f2 f2'.
        (INJP f1 f2 = INJP f1' f2') <=> (f1 = f1') /\ (f2 = f2')"
   (REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [FUN_EQ_THM] THEN REWRITE_TAC [AND_FORALL_THM] THEN
    X_GEN_TAC (← q r"n:num") THEN POP_ASSUM (MP_TAC o REWRITE_RULE [INJP]) THEN
    DISCH_THEN (MP_TAC o GEN (← q r"b:bool") o C AP_THM (← q r"NUMSUM b n")) THEN
    DISCH_THEN (fun th => tactic_of do pure (
      MP_TAC (← SPEC (← q r"T") th) THEN MP_TAC (← SPEC (← q r"F") th))) THEN
    ASM_SIMP_TAC [NUMSUM_DEST, ETA_AX])

  /- Now, set up "constructor" and "bottom" element. -/

  let ZCONSTR ← new_definition
   r"ZCONSTR c i r :num->A->bool
     = INJP (INJN (SUC c)) (INJP (INJA i) (INJF r))"

  let ZBOT ← new_definition
   r"ZBOT = INJP (INJN 0) (@z:num->A->bool. T)"

  let ZCONSTR_ZBOT ← prove
   r"!c i r. ~(ZCONSTR c i r :num->A->bool = ZBOT)"
   (REWRITE_TAC [ZCONSTR, ZBOT, INJP_INJ, INJN_INJ, NOT_SUC])

  /- Carve out an inductively defined set. -/

  let (ZRECSPACE_RULES, ZRECSPACE_INDUCT, ZRECSPACE_CASES) ←
    new_inductive_definition
     r"ZRECSPACE (ZBOT:num->A->bool) /\
    (!c i r. (!n. ZRECSPACE (r n)) ==> ZRECSPACE (ZCONSTR c i r))"

  let recspace_tydef ← ExceptT.mk (new_basic_type_definition "recspace" "_mk_rec" "_dest_rec"
    (← CONJUNCT1 ZRECSPACE_RULES))

  /- Define lifted constructors. -/

  let BOTTOM ← new_definition
   r"BOTTOM = _mk_rec (ZBOT:num->A->bool)"

  let CONSTR ← new_definition
   r"CONSTR c i r :(A)recspace
     = _mk_rec (ZCONSTR c i (\n. _dest_rec(r n)))"

  /- Some lemmas. -/

  let MK_REC_INJ ← prove
   r"!x y. (_mk_rec x :(A)recspace = _mk_rec y)
         ==> (ZRECSPACE x /\ ZRECSPACE y ==> (x = y))"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [recspace_tydef.2] THEN
    DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [← GSYM th])) THEN
    ASM_REWRITE_TAC [])

  let DEST_REC_INJ ← prove
   r"!x y. (_dest_rec x = _dest_rec y) <=> (x:(A)recspace = y)"
   (REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    POP_ASSUM (MP_TAC o AP_TERM
      (← q r"_mk_rec:(num->A->bool)->(A)recspace")) THEN
    REWRITE_TAC [recspace_tydef.1])

  /- Show that the set is freely inductively generated. -/

  let CONSTR_BOT ← prove
   r"!c i r. ~(CONSTR c i r :(A)recspace = BOTTOM)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [CONSTR, BOTTOM] THEN
    DISCH_THEN (MP_TAC o MATCH_MP MK_REC_INJ) THEN
    REWRITE_TAC [ZCONSTR_ZBOT, ZRECSPACE_RULES] THEN
    MATCH_MP_TAC (← CONJUNCT2 ZRECSPACE_RULES) THEN
    REWRITE_TAC [recspace_tydef.1, recspace_tydef.2])

  let CONSTR_INJ ← prove
   r"!c1 i1 r1 c2 i2 r2. (CONSTR c1 i1 r1 :(A)recspace = CONSTR c2 i2 r2) <=>
                       (c1 = c2) /\ (i1 = i2) /\ (r1 = r2)"
   (REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    POP_ASSUM (MP_TAC o REWRITE_RULE [CONSTR]) THEN
    DISCH_THEN (MP_TAC o MATCH_MP MK_REC_INJ) THEN
    SUBGOAL_LHAND2_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC (← CONJUNCT2 ZRECSPACE_RULES) THEN
      REWRITE_TAC [recspace_tydef.1, recspace_tydef.2],
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [ZCONSTR] THEN
      REWRITE_TAC [INJP_INJ, INJN_INJ, INJF_INJ, INJA_INJ] THEN
      ONCE_REWRITE_TAC [FUN_EQ_THM] THEN BETA_TAC THEN
      REWRITE_TAC [SUC_INJ, DEST_REC_INJ]])

  let CONSTR_IND ← prove
   r"!P. P(BOTTOM) /\
       (!c i r. (!n. P(r n)) ==> P(CONSTR c i r))
       ==> !x:(A)recspace. P(x)"
   (← do
    let it ← ITAUT (← q r"(a ==> a /\ b) <=> (a ==> b)")
    pure
     (REPEAT STRIP_TAC THEN
      MP_TAC (← SPEC (← q r"\z:num->A->bool. ZRECSPACE(z) /\ P(_mk_rec z)")
             ZRECSPACE_INDUCT) THEN
      BETA_TAC THEN ASM_REWRITE_TAC [ZRECSPACE_RULES, ← GSYM BOTTOM] THEN
      SUBGOAL_LHAND2_TAC THENL
       [REPEAT GEN_TAC THEN REWRITE_TAC [FORALL_AND_THM] THEN
        REPEAT STRIP_TAC THENL
         [MATCH_MP_TAC (← CONJUNCT2 ZRECSPACE_RULES) THEN ASM_REWRITE_TAC [],
          FIRST_ASSUM (ANTE_RES_THEN MP_TAC) THEN
          REWRITE_TAC [CONSTR] THEN
          RULE_ASSUM_TAC (REWRITE_RULE [recspace_tydef.2]) THEN
          ASM_SIMP_TAC [ETA_AX]],
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"_dest_rec (x:(A)recspace)")) THEN
        REWRITE_TAC [recspace_tydef.1] THEN
        REWRITE_TAC [it] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC [recspace_tydef.1, recspace_tydef.2]]))

  /- Now prove the recursion theorem (this subcase is all we need). -/

  let CONSTR_REC ← prove
   r"!Fn:num->A->(num->(A)recspace)->(num->B)->B.
     ?f. (!c i r. f (CONSTR c i r) = Fn c i r (\n. f (r n)))"
   (REPEAT STRIP_TAC THEN MP_TAC (← prove_inductive_relations_exist
      (← q r"(Z:(A)recspace->B->bool) BOTTOM b /\
       (!c i r y. (!n. Z (r n) (y n)) ==> Z (CONSTR c i r) (Fn c i r y))")) THEN
    DISCH_THEN (CHOOSE_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o GSYM)) THEN
    SUBGOAL_THEN (← q r"!x. ?!y. (Z:(A)recspace->B->bool) x y") MP_TAC THENL
     [W (MP_TAC o PART_MATCH rand CONSTR_IND o snd) THEN
      DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
       [FIRST_ASSUM (fun t => tactic_of do pure (GEN_REWRITE_TAC BINDER_CONV [← GSYM t])) THEN
        REWRITE_TAC [← GSYM CONSTR_BOT, EXISTS_UNIQUE_REFL],
        DISCH_THEN (MP_TAC o REWRITE_RULE [EXISTS_UNIQUE_THM, FORALL_AND_THM]) THEN
        DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
        DISCH_THEN (MP_TAC o REWRITE_RULE [SKOLEM_THM]) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"y:num->B") ASSUME_TAC) THEN
        REWRITE_TAC [EXISTS_UNIQUE_THM] THEN
        FIRST_ASSUM (fun th => tactic_of do pure (CHANGED_TAC (ONCE_REWRITE_TAC [← GSYM th]))) THEN
        CONJ_TAC THENL
         [EXISTS_TAC (← q r"(Fn:num->A->(num->(A)recspace)->(num->B)->B) c i r y") THEN
          REWRITE_TAC [CONSTR_BOT, CONSTR_INJ, ← GSYM CONJ_ASSOC] THEN
          REWRITE_TAC [UNWIND_THM1, RIGHT_EXISTS_AND_THM] THEN
          EXISTS_TAC (← q r"y:num->B") THEN ASM_REWRITE_TAC [],
          REWRITE_TAC [CONSTR_BOT, CONSTR_INJ, ← GSYM CONJ_ASSOC] THEN
          REWRITE_TAC [UNWIND_THM1, RIGHT_EXISTS_AND_THM] THEN
          REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
          REPEAT AP_TERM_TAC THEN ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
          X_GEN_TAC (← q r"w:num") THEN FIRST_ASSUM MATCH_MP_TAC THEN
          EXISTS_TAC (← q r"w:num") THEN ASM_REWRITE_TAC []]],
      REWRITE_TAC [UNIQUE_SKOLEM_ALT] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"fn:(A)recspace->B") (ASSUME_TAC o GSYM)) THEN
      EXISTS_TAC (← q r"fn:(A)recspace->B") THEN ASM_REWRITE_TAC [] THEN
      REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN
      FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC I [← GSYM th])) THEN
      REWRITE_TAC [BETA_THM]])

  /- The following is useful for coding up functions casewise. -/

  let FCONS ← new_recursive_definition num_RECURSION
   r"(!a f. FCONS (a:A) f 0 = a) /\
  (!a f n. FCONS (a:A) f (SUC n) = f n)"

  let FCONS_UNDO ← prove
   r"!f:num->A. f = FCONS (f 0) (f o SUC)"
   (GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
    INDUCT_TAC THEN REWRITE_TAC [FCONS, o_THM])

  let FNIL ← new_definition
   r"FNIL (n:num) = @x:A. T"

  return {
    INJ_INVERSE2, NUMPAIR, NUMPAIR_INJ_LEMMA, NUMPAIR_INJ, NUMPAIR_DEST,
    NUMSUM, NUMSUM_INJ, NUMSUM_DEST, INJN, INJN_INJ, INJA, INJA_INJ, INJF,
    INJF_INJ, INJP, INJP_INJ, ZCONSTR, ZBOT, ZCONSTR_ZBOT, ZRECSPACE_RULES,
    ZRECSPACE_INDUCT, ZRECSPACE_CASES, recspace_tydef, BOTTOM, CONSTR,
    MK_REC_INJ, DEST_REC_INJ, CONSTR_BOT, CONSTR_INJ, CONSTR_IND, CONSTR_REC,
    FCONS, FCONS_UNDO, FNIL }

end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax
open HolCore.Bool (list_mk_exists list_mk_disj mk_exists)
open HolCore.Classic (mk_select)
open HolCore.Parser (lexcode)

/- ---------------------------------------------------------------------- -/
/- Small helpers.                                                         -/
/- ---------------------------------------------------------------------- -/

/-- `mk_eq(l,r)`: `=` at the type of `l`; fails if `r` has another type. -/
def mkEq (l r : term) : Except String term := do
  let ty := type_of l
  mk_comb (← mk_comb (.Const "=" (.Tyapp "fun" [ty, .Tyapp "fun" [ty, bool_ty]])) l) r

/-- lib.ml's `map2`, for a function that can fail (head first). -/
def map2M {α β γ : Type} (f : α → β → ExceptT String IO γ) :
    List α → List β → ExceptT String IO (List γ)
  | [], [] => pure []
  | x :: xs, y :: ys => do
      let h ← f x y
      return h :: (← map2M f xs ys)
  | _, _ => throw "map2: length mismatch"

/-- lib.ml's `mapfilter`: the tail is done first, and elements whose `f`
    fails are dropped. -/
def mapfilterM {α β : Type} (f : α → ExceptT String IO β) : List α → ExceptT String IO (List β)
  | [] => pure []
  | h :: t => do
      let rest ← mapfilterM f t
      tryWith (do return (← f h) :: rest) (pure rest)

/-- lib.ml's `tryfind`, for a function that can fail. -/
def tryfindM' {α β : Type} (f : α → ExceptT String IO β) : List α → ExceptT String IO β
  | [] => throw "tryfind"
  | h :: t => tryWith (f h) (tryfindM' f t)

/-- `mk_type(op,args)`. -/
def mkType (op : String) (args : List hol_type) : ExceptT String IO hol_type :=
  ExceptT.mk (mk_type op args)

/-- `mk_fun_ty ty1 ty2`. -/
def mkFunTy (ty1 ty2 : hol_type) : ExceptT String IO hol_type := ExceptT.mk (mk_fun_ty ty1 ty2)

/-- `mk_const(c,theta)`. -/
def mkConst (c : String) (theta : List (hol_type × hol_type)) : ExceptT String IO term :=
  ExceptT.mk (mk_const c theta)

/-- `subst theta tm`. -/
def substM (theta : List (term × term)) (tm : term) : ExceptT String IO term := do
  ExceptT.mk ((← ExceptT.mk (subst theta)) tm)

/- ---------------------------------------------------------------------- -/
/- define_type_raw #1 (ind_types.ml 302-738).                             -/
/- ---------------------------------------------------------------------- -/

/-- What the first `define_type_raw` binds before `fun def -> ...`: its
    quotations (in `sucivate`, `justify_inductive_type_model` and
    `create_recursion_iso_constructor`) and `derive_recursion_theorem`'s
    `CCONV`, together with the theorems and the kernel/inductive-definition
    functions it uses.  `eepth` is `EXISTS_EQUATION`'s proforma. -/
structure DefTypeRaw where
  FST : thm
  SND : thm
  FCONS : thm
  BETA_THM : thm
  CONSTR_REC : thm
  eepth : thm
  mk_pair : term × term → IO (Except String term)
  derive_nonschematic_inductive_relations : term → IO (Except String thm)
  prove_monotonicity_hyps : thm → IO (Except String thm)
  new_definition : term → IO (Except String thm)
  new_basic_type_definition :
    String → String → String → thm → IO (Except String (thm × thm))
  zero_tm : term
  suc_tm : term
  t_tm : term
  n_tm : term
  beps_tm : term
  s_tm : term
  zty : hol_type
  numty : hol_type
  CCONV : ioconv

instance : Inhabited DefTypeRaw :=
  ⟨⟨default, default, default, default, default, default,
    fun _ => pure (.error ""), fun _ => pure (.error ""), fun _ => pure (.error ""),
    fun _ => pure (.error ""), fun _ _ _ _ => pure (.error ""),
    default, default, default, default, default, default, default, default,
    fun _ => pure (.error "")⟩⟩

/-- Build the `DefTypeRaw` (ind_types.ml 308-310, 330, 632-634, 675). -/
@[nospecialize]
def setupDefTypeRaw [HolBase] (FST SND FCONS BETA_THM CONSTR_REC eepth : thm)
    (mk_pair : term × term → IO (Except String term))
    (derive_nonschematic_inductive_relations : term → IO (Except String thm))
    (prove_monotonicity_hyps : thm → IO (Except String thm))
    (new_definition : term → IO (Except String thm))
    (new_basic_type_definition :
      String → String → String → thm → IO (Except String (thm × thm))) :
    ExceptT String IO DefTypeRaw := do
  let zero_tm ← q r"0"
  let suc_tm ← q r"SUC"
  let t_tm ← q r"T"
  let n_tm ← q r"n:num"
  let beps_tm ← q r"@x:bool. T"
  let s_tm ← q r"s:num->Z"
  let zty ← qty r"Z"
  let numty ← qty r"num"
  let CCONV := funpow 3 RATOR_CONV (REPEATC (← GEN_REWRITE_CONV_NET id [FCONS]))
  return { FST, SND, FCONS, BETA_THM, CONSTR_REC, eepth, mk_pair,
           derive_nonschematic_inductive_relations, prove_monotonicity_hyps,
           new_definition, new_basic_type_definition,
           zero_tm, suc_tm, t_tm, n_tm, beps_tm, s_tm, zty, numty, CCONV }

/- ---------------------------------------------------------------------- -/
/- The initial mutual type definition function, with a type-restricted    -/
/- recursion theorem.                                                     -/
/- ---------------------------------------------------------------------- -/

/- ---------------------------------------------------------------------- -/
/- Handy utility to produce "SUC o SUC o SUC ..." form of numeral.        -/
/- ---------------------------------------------------------------------- -/

/-- `sucivate n = funpow n (curry mk_comb suc) zero` (ind_types.ml 308-310). -/
def sucivate (D : DefTypeRaw) (n : Nat) : Except String term :=
  let rec go : Nat → term → Except String term
    | 0, acc => .ok acc
    | k + 1, acc => do go k (← mk_comb D.suc_tm acc)
  go n D.zero_tm

/- ---------------------------------------------------------------------- -/
/- Eliminate local "definitions" in hyps.                                 -/
/- ---------------------------------------------------------------------- -/

/-- `SCRUB_EQUATION eq (th,insts)` (ind_types.ml 317-320). -/
def SCRUB_EQUATION [HolBase] (eq : term) (thi : thm × List (term × term)) :
    ExceptT String IO (thm × List (term × term)) := do
  let (th, insts) := thi
  let eq' ← insts.foldrM (fun t acc => substM [t] acc) eq
  let (l, r) ← liftExcept (dest_eq eq')
  return (← MP (← INST [(r, l)] (← DISCH eq' th)) (REFL r), (r, l) :: insts)

/-- `itlist SCRUB_EQUATION eqs (th,[])`, keeping the theorem. -/
def scrubAll [HolBase] (eqs : List term) (th : thm) : ExceptT String IO thm := do
  return (← eqs.foldrM SCRUB_EQUATION (th, [])).1

/-- The `munion` of `justify_inductive_type_model` (ind_types.ml 331-337). -/
partial def munion [BEq α] (s1 s2 : List α) : List α :=
  match s1 with
  | [] => s2
  | h1 :: s1' =>
    match Lib.remove (fun h2 => h2 == h1) s2 with
    | .ok (_, s2') => h1 :: munion s1' s2'
    | .error _ => h1 :: munion s1' s2

/-- The `mk_injector` of `mk_constructor` (ind_types.ml 349-356). -/
partial def mk_injector : List term → List hol_type → List term → Except String (List term)
  | _, [], _ => .ok []
  | epstms, ty :: alltys, iargs =>
    match Lib.remove (fun t => type_of t == ty) iargs with
    | .ok (a, iargs') => do return a :: (← mk_injector (← tl epstms) alltys iargs')
    | .error _ => do return (← hd epstms) :: (← mk_injector (← tl epstms) alltys iargs)

/- ---------------------------------------------------------------------- -/
/- Proves existence of model (inductively); use pseudo-constructors.      -/
/-                                                                        -/
/- Returns suitable definitions of constructors in terms of CONSTR, and   -/
/- the rule and induction theorems from the inductive relation package.   -/
/- ---------------------------------------------------------------------- -/

/-- `justify_inductive_type_model def` (ind_types.ml 329-395).  Returns
    `(conths, th2a, th2b)`. -/
def justify_inductive_type_model [HolBase] (D : DefTypeRaw)
    (def_ : List (hol_type × List (String × List hol_type))) :
    ExceptT String IO (List thm × thm × thm) := do
  let (newtys, rights) := unzip def_
  let tyargls := itlist (fun r acc => r.map Prod.snd ++ acc) rights []
  let alltys := itlist (fun tys acc => munion (subtract tys newtys) acc) tyargls []
  let mkSel ← ExceptT.mk mk_select
  let epstms ← liftExcept (alltys.mapM (fun ty => mkSel (mk_var "v" ty, D.t_tm)))
  let pty ← tryWith (end_itlist (fun ty1 ty2 => mkType "prod" [ty1, ty2]) alltys) (pure bool_ty)
  let recty ← mkType "recspace" [pty]
  let constr ← mkConst "CONSTR" [(pty, aty)]
  let fcons ← mkConst "FCONS" [(recty, aty)]
  let bot ← mkConst "BOTTOM" [(pty, aty)]
  let bottail ← liftExcept (mk_abs D.n_tm bot)
  let mk_constructor (n : Nat) (cn : String × List hol_type) : ExceptT String IO term := do
    let (cname, cargs) := cn
    let ttys := cargs.map (fun ty => if mem ty newtys then recty else ty)
    let args ← liftExcept (make_args "a" [] ttys)
    let (rargs, iargs) := partition (fun t => type_of t == recty) args
    let iarg ← tryWith (do
        end_itlist (fun a b => ExceptT.mk (D.mk_pair (a, b)))
          (← liftExcept (mk_injector epstms alltys iargs)))
      (pure D.beps_tm)
    let rarg ← liftExcept (rargs.foldrM (fun r acc => do (← mk_binop fcons r) acc) bottail)
    let conty ← (args.map type_of).foldrM mkFunTy recty
    let condef ← liftExcept (do list_mk_comb constr [← sucivate D n, iarg, rarg])
    liftExcept (do mkEq (mk_var cname conty) (← list_mk_abs args condef))
  let rec mk_constructors (n : Nat) : List (String × List hol_type) → ExceptT String IO (List term)
    | [] => pure []
    | r :: rs => do
        let h ← mk_constructor n r
        return h :: (← mk_constructors (n + 1) rs)
  let condefs ← mk_constructors 0 (itlist (· ++ ·) rights [])
  let conths ← condefs.mapM ASSUME
  let predty ← mkFunTy recty bool_ty
  let edefs := itlist (fun (xl : hol_type × List (String × List hol_type)) acc =>
      xl.2.map (fun t => (xl.1, t)) ++ acc) def_ []
  let idefs ← map2M (fun (e : hol_type × (String × List hol_type)) (d : term) =>
      pure ((e.1, e.2.2), d)) edefs condefs
  let mk_rule (rad : (hol_type × List hol_type) × term) : Except String term := do
    let ((r, a), condef) := rad
    let (left, right) ← dest_eq condef
    let (args, _bod) := strip_abs right
    let lapp ← list_mk_comb left args
    let conds ← itlist2M (fun arg argty sofar =>
        if mem argty newtys then do
          return (← mk_comb (mk_var (← dest_vartype argty) predty) arg) :: sofar
        else pure sofar) args a []
    let conc ← mk_comb (mk_var (← dest_vartype r) predty) lapp
    let rule ← if conds == [] then pure conc else do mk_imp (← list_mk_conj conds) conc
    list_mk_forall args rule
  let rules ← liftExcept (do list_mk_conj (← idefs.mapM mk_rule))
  let th0 ← ExceptT.mk (D.derive_nonschematic_inductive_relations rules)
  let th1 ← ExceptT.mk (D.prove_monotonicity_hyps th0)
  let (th2a, th2bc) ← CONJ_PAIR th1
  let th2b ← CONJUNCT1 th2bc
  return (conths, th2a, th2b)

/- ---------------------------------------------------------------------- -/
/- Shows that the predicates defined by the rules are all nonempty.       -/
/- (This could be done much more efficiently/cleverly, but it's OK.)      -/
/- ---------------------------------------------------------------------- -/

/-- `prove_model_inhabitation rth` (ind_types.ml 401-423). -/
partial def prove_model_inhabitation [HolBase] (rth : thm) : ExceptT String IO (List thm) := do
  let srules ← (CONJUNCTS rth).mapM SPEC_ALL
  let (imps, bases) := partition (fun th => is_imp (concl th)) srules
  let concs := bases.map concl ++ (← liftExcept (imps.mapM (fun th => rand (concl th))))
  let preds := setify (concs.map (repeat' rator))
  let rec exhaust_inhabitations (ths sofar : List thm) : ExceptT String IO (List thm) := do
    let dunnit := setify (sofar.map (fun th => (strip_comb (concl th)).1))
    let useful := ths.filter (fun th =>
      match rand (concl th) with
      | .ok r => !(mem (strip_comb r).1 dunnit)
      | .error _ => false)
    if useful == [] then return sofar
    let follow_horn (thm0 : thm) : ExceptT String IO thm := do
      let preds := (conjuncts (← liftExcept (lhand (concl thm0)))).map (fun c => (strip_comb c).1)
      let asms ← liftExcept (preds.mapM (fun p =>
        Lib.find (fun th => (strip_comb (concl th)).1 == p) sofar))
      MATCH_MP thm0 (← end_itlist CONJ asms)
    let newth ← tryfindM' follow_horn useful
    exhaust_inhabitations ths (newth :: sofar)
  let ithms ← exhaust_inhabitations imps bases
  liftExcept (preds.mapM (fun p => Lib.find (fun th => (strip_comb (concl th)).1 == p) ithms))

/- ---------------------------------------------------------------------- -/
/- Makes a type definition for one of the defined subsets.                -/
/- ---------------------------------------------------------------------- -/

/-- `define_inductive_type cdefs exth` (ind_types.ml 428-441). -/
def define_inductive_type [HolBase] (D : DefTypeRaw) (cdefs : List thm) (exth : thm) :
    ExceptT String IO (thm × thm) := do
  let extm := concl exth
  let epred := (strip_comb extm).1
  let (ename, _) ← liftExcept (dest_var epred)
  -- ind_types.ml 432: OCaml `find (fun eq -> lhand eq = epred)` propagates
  -- `lhand`'s Failure, so use a failure-propagating find.
  let predE (eq : term) : Except String Bool := do pure ((← lhand eq) == epred)
  let rec findE : List term → Except String term
    | []     => failwith "find"
    | h :: t => do if (← predE h) then pure h else findE t
  let th1 ← ASSUME (← liftExcept (findE (hyp exth)))
  let th2 ← TRANS th1 (← ExceptT.mk (SUBS_CONV cdefs (← liftExcept (rand (concl th1)))))
  let th3 ← EQ_MP (← AP_THM th2 (← liftExcept (rand extm))) exth
  let th4 ← scrubAll (hyp th3) th3
  let mkname := "_mk_" ++ ename
  let destname := "_dest_" ++ ename
  let (bij1, bij2) ← ExceptT.mk (D.new_basic_type_definition ename mkname destname th4)
  let bij2a ← AP_THM th2 (← liftExcept (do rand (← rand (concl bij2))))
  let bij2b ← TRANS bij2a bij2
  return (bij1, bij2b)

/- ---------------------------------------------------------------------- -/
/- Defines a type constructor corresponding to current                    -/
/- pseudo-constructor.                                                    -/
/- ---------------------------------------------------------------------- -/

/-- `define_inductive_type_constructor defs consindex th` (ind_types.ml
    446-468). -/
def define_inductive_type_constructor [HolBase] (D : DefTypeRaw) (defs : List thm)
    (consindex : List (term × (term × term))) (th : thm) : ExceptT String IO thm := do
  let (_avs, bod) := strip_forall (concl th)
  let (asms, conc) ←
    if is_imp bod then liftExcept (do return (conjuncts (← lhand bod), ← rand bod))
    else pure ([], bod)
  let asmlist ← liftExcept (asms.mapM dest_comb)
  let (cpred, cterm) ← liftExcept (dest_comb conc)
  let (oldcon, oldargs) := strip_comb cterm
  let modify_arg (v : term) : term × term :=
    match (do
      let dest := (← Lib.assoc (← Lib.rev_assoc v asmlist) consindex).2
      let ty' ← hd (← dest_type (type_of dest)).2
      let v' := mk_var (← dest_var v).1 ty'
      return (← mk_comb dest v', v') : Except String (term × term)) with
    | .ok p => p
    | .error _ => (v, v)
  let (newrights, newargs) := unzip (oldargs.map modify_arg)
  let retmk := (← liftExcept (Lib.assoc cpred consindex)).1
  let defbod ← liftExcept (do mk_comb retmk (← list_mk_comb oldcon newrights))
  let defrt ← liftExcept (list_mk_abs newargs defbod)
  let expth ← liftExcept (Lib.find (fun th =>
      match lhand (concl th) with | .ok l => l == oldcon | .error _ => false) defs)
  let rexpth ← ExceptT.mk (SUBS_CONV [expth] defrt)
  let deflf := mk_var (← liftExcept (dest_var oldcon)).1 (type_of defrt)
  let defth ← ExceptT.mk (D.new_definition
    (← liftExcept (do mkEq deflf (← rand (concl rexpth)))))
  TRANS defth (← SYM rexpth)

/- ---------------------------------------------------------------------- -/
/- Instantiate the induction theorem on the representatives to transfer   -/
/- it to the new type(s). Uses "\x. rep-pred(x) /\ P(mk x)" for "P".      -/
/- ---------------------------------------------------------------------- -/

/-- `instantiate_induction_theorem consindex ith` (ind_types.ml 474-489). -/
def instantiate_induction_theorem [HolBase] (consindex : List (term × (term × term)))
    (ith : thm) : ExceptT String IO thm := do
  let (avs, bod) := strip_forall (concl ith)
  let corlist ← liftExcept ((conjuncts (← rand bod)).mapM (fun c => do
      let (a, b) ← dest_imp (← body (← rand c))
      return (repeat' rator a, repeat' rator b)))
  let consindex' ← liftExcept (avs.mapM (fun v => do
      let w ← Lib.rev_assoc v corlist
      return (w, ← Lib.assoc w consindex)))
  let recty ← liftExcept (do hd (← dest_type (type_of (← hd consindex).2.1)).2)
  let newtys ← liftExcept (consindex'.mapM (fun (ci : term × (term × term)) => do
      hd (← dest_type (type_of ci.2.2)).2))
  let ptypes ← newtys.mapM (fun ty => mkFunTy ty bool_ty)
  let preds ← liftExcept (make_args "P" [] ptypes)
  let args ← liftExcept (make_args "x" [] (preds.map (fun _ => recty)))
  let lambs ← map2M (fun (ci : term × (term × term)) (pa : term × term) => do
      let (r, (m, _d)) := ci
      let (p, a) := pa
      liftExcept (do mk_abs a (← mk_conj (← mk_comb r a) (← mk_comb p (← mk_comb m a)))))
    consindex' (← liftExcept (zip preds args))
  SPECL lambs ith

/- ---------------------------------------------------------------------- -/
/- Reduce a single clause of the postulated induction theorem (old_ver)   -/
/- ba                                                                     -/
/- to the kind wanted for the new type (new_ver); |- new_ver ==> old_ver  -/
/- ---------------------------------------------------------------------- -/

/-- `pullback_induction_clause tybijpairs conthms` (ind_types.ml 495-533):
    builds `PRERULE` and `IPRULE` once and returns `fun rthm tm -> ...`. -/
def pullback_induction_clause [HolBase] (tybijpairs : List (thm × thm)) (conthms : List thm) :
    ExceptT String IO (thm → term → ExceptT String IO thm) := do
  let PRERULE := CONV_RULE (← GEN_REWRITE_CONV_NET (funpow 3 RAND_CONV) (← conthms.mapM SYM))
  let ipconv ← GEN_REWRITE_CONV_NET id (tybijpairs.map Prod.snd)
  let IPRULE (th : thm) : ExceptT String IO thm := do SYM (← CONV_RULE ipconv th)
  return fun rthm tm => do
    let (avs, bimp) := strip_forall tm
    if is_imp bimp then
      let (ant, con) ← liftExcept (dest_imp bimp)
      let ths ← (CONJUNCTS (← ASSUME ant)).mapM (CONV_RULE BETA_CONV)
      let (tths, pths) := unzip (← ths.mapM CONJ_PAIR)
      let tth ← MATCH_MP (← SPEC_ALL rthm) (← end_itlist CONJ tths)
      let mths ← (tth :: tths).mapM IPRULE
      let conth1 ← liftExcept (Equal.BETA_CONV con)
      let contm1 ← liftExcept (rand (concl conth1))
      let conth2 ← TRANS conth1 (← AP_TERM (← liftExcept (rator contm1))
        (← ExceptT.mk (SUBS_CONV (mths.drop 1) (← liftExcept (rand contm1)))))
      let conth3 ← PRERULE conth2
      let lctms := pths.map concl
      let asmin ← liftExcept (do mk_imp (← list_mk_conj lctms) (← rand (← rand (concl conth3))))
      let argsin ← liftExcept ((conjuncts (← lhand asmin)).mapM rand)
      let argsgen ← liftExcept (argsin.mapM (fun tm => do
        return mk_var (← dest_var (← rand tm)).1 (type_of tm)))
      let asmgen ← substM (← liftExcept (zip argsgen argsin)) asmin
      let asmquant ← liftExcept (do
        list_mk_forall (strip_comb (← rand (← rand asmgen))).2 asmgen)
      let th1 ← INST (← liftExcept (zip argsin argsgen)) (← SPEC_ALL (← ASSUME asmquant))
      let th2 ← MP th1 (← end_itlist CONJ pths)
      let th3 ← EQ_MP (← SYM conth3) (← CONJ tth th2)
      DISCH asmquant (← GENL avs (← DISCH ant th3))
    else
      let con := bimp
      let conth2 ← liftExcept (Equal.BETA_CONV con)
      let tth ← PART_MATCH (fun t => .ok t) rthm (← liftExcept (do lhand (← rand (concl conth2))))
      let conth3 ← PRERULE conth2
      let asmgen ← liftExcept (do rand (← rand (concl conth3)))
      let asmquant ← liftExcept (do list_mk_forall (strip_comb (← rand asmgen)).2 asmgen)
      let th2 ← SPEC_ALL (← ASSUME asmquant)
      let th3 ← EQ_MP (← SYM conth3) (← CONJ tth th2)
      DISCH asmquant (← GENL avs th3)

/- ---------------------------------------------------------------------- -/
/- Finish off a consequence of the induction theorem.                     -/
/- ---------------------------------------------------------------------- -/

/-- `finish_induction_conclusion consindex tybijpairs` (ind_types.ml
    538-556): builds `PRERULE` and `FINRULE` once and returns `fun th -> ...`. -/
def finish_induction_conclusion [HolBase] (consindex : List (term × (term × term)))
    (tybijpairs : List (thm × thm)) : ExceptT String IO (thm → ExceptT String IO thm) := do
  let (tybij1, tybij2) := unzip tybijpairs
  let pre1 ← GEN_REWRITE_CONV_NET (fun c => LAND_CONV (LAND_CONV (RAND_CONV c))) tybij1
  let pre2 ← GEN_REWRITE_CONV_NET LAND_CONV tybij2
  let PRERULE (th : thm) : ExceptT String IO thm := do CONV_RULE pre1 (← CONV_RULE pre2 th)
  let FINRULE := CONV_RULE (← GEN_REWRITE_CONV_NET RAND_CONV tybij1)
  return fun th => do
    let (_av, bimp) ← liftExcept (dest_forall (concl th))
    let pv ← liftExcept (do lhand (← body (← rator (← rand bimp))))
    let (p, v) ← liftExcept (dest_comb pv)
    let (_mk, dest) ← liftExcept (Lib.assoc p consindex)
    let ty ← liftExcept (do hd (← dest_type (type_of dest)).2)
    let v' := mk_var (← liftExcept (dest_var v)).1 ty
    let dv ← liftExcept (mk_comb dest v')
    let th1 ← PRERULE (← SPEC dv th)
    let th2 ← MP th1 (REFL (← liftExcept (do rand (← lhand (concl th1)))))
    let th3 ← CONV_RULE BETA_CONV th2
    GEN v' (← FINRULE (← CONJUNCT2 th3))

/- ---------------------------------------------------------------------- -/
/- Derive the induction theorem.                                          -/
/- ---------------------------------------------------------------------- -/

/-- `derive_induction_theorem consindex tybijpairs conthms iith rth`
    (ind_types.ml 561-578). -/
def derive_induction_theorem [HolBase] (consindex : List (term × (term × term)))
    (tybijpairs : List (thm × thm)) (conthms : List thm) (iith rth : thm) :
    ExceptT String IO thm := do
  let pull ← pullback_induction_clause tybijpairs conthms
  let bths ← map2M pull (CONJUNCTS rth) (conjuncts (← liftExcept (lhand (concl iith))))
  let asm ← liftExcept (do list_mk_conj (← bths.mapM (fun th => lhand (concl th))))
  let ths ← map2M MP bths (CONJUNCTS (← ASSUME asm))
  let th1 ← MP iith (← end_itlist CONJ ths)
  let finish ← finish_induction_conclusion consindex tybijpairs
  let th2 ← end_itlist CONJ (← (CONJUNCTS th1).mapM finish)
  let th3 ← DISCH asm th2
  let preds ← liftExcept ((conjuncts (← rand (concl th3))).mapM (fun c => do
      rator (← body (← rand c))))
  let th4 ← GENL preds th3
  let cfsts := consindex.map Prod.fst
  let pasms := (hyp th4).filter (fun t =>
    match lhand t with | .ok l => mem l cfsts | .error _ => false)
  let th5 ← pasms.foldrM DISCH th4
  let th6 ← scrubAll (hyp th5) th5
  let th7 ← UNDISCH_ALL th6
  scrubAll (hyp th7) th7

/- ---------------------------------------------------------------------- -/
/- Create the recursive functions and eliminate pseudo-constructors.      -/
/- (These are kept just long enough to derive the key property.)          -/
/- ---------------------------------------------------------------------- -/

/-- `create_recursive_functions tybijpairs consindex conthms rth`
    (ind_types.ml 584-626). -/
def create_recursive_functions [HolBase] (tybijpairs : List (thm × thm))
    (consindex : List (term × (term × term))) (conthms : List thm) (rth : thm) :
    ExceptT String IO thm := do
  let domtys ← liftExcept (consindex.mapM (fun (ci : term × (term × term)) => do
      hd (← dest_type (type_of ci.2.2)).2))
  let recty ← liftExcept (do hd (← dest_type (type_of (← hd consindex).2.1)).2)
  let ranty := mk_vartype "Z"
  let fn := mk_var "fn" (← mkFunTy recty ranty)
  let fns ← liftExcept (make_args "fn" [] (← domtys.mapM (fun ty => mkFunTy ty ranty)))
  let args ← liftExcept (make_args "a" [] domtys)
  let rights ← map2M (fun (ci : term × (term × term)) (a : term) =>
      liftExcept (do mk_abs a (← mk_comb fn (← mk_comb ci.2.2 a)))) consindex args
  let eqs ← map2M (fun f r => liftExcept (mkEq f r)) fns rights
  let fdefs ← eqs.mapM ASSUME
  let fxths1 ← conthms.mapM (fun th1 => tryfindM' (fun th2 => MK_COMB (th2, th1)) fdefs)
  let fxths2 ← fxths1.mapM (fun th => do
    TRANS th (← liftExcept (do Equal.BETA_CONV (← rand (concl th)))))
  let mk_tybijcons (p : thm × thm) : ExceptT String IO thm := do
    let (th1, th2) := p
    let th3 ← INST [(← liftExcept (do rand (← lhand (concl th1))),
                     ← liftExcept (do rand (← lhand (concl th2))))] th2
    let th4 ← AP_TERM (← liftExcept (do rator (← lhand (← rand (concl th2))))) th1
    EQ_MP (← SYM th3) th4
  let SCONV ← GEN_REWRITE_CONV_NET id (← tybijpairs.mapM mk_tybijcons)
  let ERULE := CONV_RULE (← GEN_REWRITE_CONV_NET id (tybijpairs.map Prod.snd))
  let simplify_fxthm (rthm fxth : thm) : ExceptT String IO thm := do
    let pat ← liftExcept (funpowM 4 rand (concl fxth))
    if is_imp (repeat' (fun t => (dest_forall t).map Prod.snd) (concl rthm)) then
      let th1 ← PART_MATCH (fun t => do rand (← rand t)) rthm pat
      let tms1 := conjuncts (← liftExcept (lhand (concl th1)))
      let ths2 ← tms1.mapM (fun t => do EQ_MP (← SYM (← ExceptT.mk (SCONV t))) HolBase.B.TRUTH)
      ERULE (← MP th1 (← end_itlist CONJ ths2))
    else
      ERULE (← PART_MATCH rand rthm pat)
  let fxths3 ← map2M simplify_fxthm (CONJUNCTS rth) fxths2
  let fxths4 ← map2M (fun th1 th2 => do TRANS th1 (← AP_TERM fn th2)) fxths2 fxths3
  let cleanup_fxthm (cth fxth : thm) : ExceptT String IO thm := do
    let tms := (strip_comb (← liftExcept (do rand (← rand (concl fxth))))).2
    let kth ← RIGHT_BETAS tms (← ASSUME (← liftExcept (hd (hyp cth))))
    TRANS fxth (← AP_TERM fn kth)
  let fxth5 ← end_itlist CONJ (← map2M cleanup_fxthm conthms fxths4)
  let cfsts := consindex.map Prod.fst
  let pasms := (hyp fxth5).filter (fun t =>
    match lhand t with | .ok l => mem l cfsts | .error _ => false)
  let fxth6 ← pasms.foldrM DISCH fxth5
  let fxth7 ← scrubAll (itlist (fun c acc => union (hyp c) acc) conthms []) fxth6
  let fxth8 ← UNDISCH_ALL fxth7
  scrubAll (subtract (hyp fxth8) eqs) fxth8

/-- The `extract_arg` of `create_recursion_iso_constructor` (ind_types.ml
    635-643). -/
partial def extract_arg [HolBase] (D : DefTypeRaw) (tup v : term) : ExceptT String IO thm := do
  if v == tup then return REFL tup
  let (t1, t2) ← liftExcept (HolMath.Pair.dest_pair tup)
  let PAIR_th ← ISPECL [t1, t2] (if free_in v t1 then D.FST else D.SND)
  let tup' ← liftExcept (rand (concl PAIR_th))
  if tup' == v then return PAIR_th
  let th ← extract_arg D tup' v
  SUBS [← SYM PAIR_th] th

/- ---------------------------------------------------------------------- -/
/- Create a function for recursion clause.                                -/
/- ---------------------------------------------------------------------- -/

/-- `create_recursion_iso_constructor consindex` (ind_types.ml 644-669):
    the part depending on `consindex` only is built once, and the function
    of `cth` is returned. -/
def create_recursion_iso_constructor [HolBase] (D : DefTypeRaw)
    (consindex : List (term × (term × term))) :
    ExceptT String IO (thm → ExceptT String IO term) := do
  let recty ← liftExcept (do hd (← dest_type (type_of (← hd consindex).1)).2)
  let domty ← liftExcept (do hd (← dest_type recty).2)
  let i := mk_var "i" domty
  let r := mk_var "r" (← mkFunTy D.numty recty)
  let mks := consindex.map (fun ci => ci.2.1)
  let mkindex ← liftExcept (mks.mapM (fun t => do
      return (← hd (← tl (← dest_type (type_of t)).2), t)))
  return fun cth => do
    let artms := (strip_comb (← liftExcept (do rand (← rand (concl cth))))).2
    let artys := mapfilter (fun t => do return type_of (← rand t)) artms
    let (args, bod) := strip_abs (← liftExcept (do rand (← hd (hyp cth))))
    let (ccitm, rtm) ← liftExcept (dest_comb bod)
    let (_cctm, itm) ← liftExcept (dest_comb ccitm)
    let (rargs, iargs) := partition (fun a => free_in a rtm) args
    let xths ← iargs.mapM (extract_arg D itm)
    let cargs' ← xths.mapM (fun th => do substM [(i, itm)] (← liftExcept (lhand (concl th))))
    let indices ← liftExcept ((List.range rargs.length).mapM (sucivate D))
    let rindexed ← liftExcept (indices.mapM (mk_comb r))
    let rargs' ← map2M (fun a rx => liftExcept (do mk_comb (← Lib.assoc a mkindex) rx))
      artys rindexed
    let sargs' ← liftExcept (indices.mapM (mk_comb D.s_tm))
    let allargs := cargs' ++ rargs' ++ sargs'
    let funty ← allargs.foldrM (fun a acc => mkFunTy (type_of a) acc) D.zty
    let funname := (← liftExcept (do dest_const (repeat' rator (← lhand (concl cth))))).1 ++ "'"
    let funarg := mk_var funname funty
    liftExcept (do list_mk_abs [i, r, D.s_tm] (← list_mk_comb funarg allargs))

/- ---------------------------------------------------------------------- -/
/- Derive the recursion theorem.                                          -/
/- ---------------------------------------------------------------------- -/

/-- `derive_recursion_theorem tybijpairs consindex conthms rath`
    (ind_types.ml 674-710). -/
def derive_recursion_theorem [HolBase] (D : DefTypeRaw) (tybijpairs : List (thm × thm))
    (consindex : List (term × (term × term))) (conthms : List thm) (rath : thm) :
    ExceptT String IO thm := do
  let isocons ← conthms.mapM (← create_recursion_iso_constructor D consindex)
  let ty := type_of (← liftExcept (hd isocons))
  let fcons ← mkConst "FCONS" [(ty, aty)]
  let fnil ← mkConst "FNIL" [(ty, aty)]
  let bigfun ← liftExcept (isocons.foldrM (fun c acc => do (← mk_binop fcons c) acc) fnil)
  let eth ← ISPEC bigfun D.CONSTR_REC
  let fn ← liftExcept (do rator (← rand (← hd (conjuncts (concl rath)))))
  let betm ← liftExcept (do
    let (v, bod) ← dest_abs (← rand (concl eth))
    return (← vsubst [(fn, v)]) bod)
  let LCONV := REWR_CONV (← ASSUME betm)
  let fnths ← (hyp rath).mapM (fun t => do
    RIGHT_BETAS [← liftExcept (do bndvar (← rand t))] (← ASSUME t))
  let SIMPER := CONV_RULE (← PURE_REWRITE_CONV_NET
    ((← fnths.mapM SYM) ++ tybijpairs.map Prod.fst ++ [D.FST, D.SND, D.FCONS, D.BETA_THM]))
  let hackdown_rath (th : thm) : ExceptT String IO thm := do
    let (ltm, rtm) ← liftExcept (dest_eq (concl th))
    let wargs := (strip_comb (← liftExcept (rand ltm))).2
    let th1 ← TRANS th (← ExceptT.mk (LCONV rtm))
    let th2 ← TRANS th1 (← ExceptT.mk (D.CCONV (← liftExcept (rand (concl th1)))))
    let th3 ← TRANS th2 (← ExceptT.mk
      (funpow 2 RATOR_CONV BETA_CONV (← liftExcept (rand (concl th2)))))
    let th4 ← TRANS th3 (← ExceptT.mk (RATOR_CONV BETA_CONV (← liftExcept (rand (concl th3)))))
    let th5 ← TRANS th4 (← liftExcept (do Equal.BETA_CONV (← rand (concl th4))))
    GENL wargs (← SIMPER th5)
  let rthm ← end_itlist CONJ (← (CONJUNCTS rath).mapM hackdown_rath)
  let unseqs := (hyp rthm).filter is_eq
  let tys ← liftExcept (consindex.mapM (fun (ci : term × (term × term)) => do
      hd (← dest_type (type_of ci.2.2)).2))
  let seqs ← liftExcept (tys.mapM (fun ty => Lib.find (fun t =>
      match (do hd (← dest_type (type_of (← lhand t))).2) with
      | .ok h => h == ty
      | .error _ => false) unseqs))
  let rethm ← liftExcept (seqs.foldrM (fun eq th => IndDefs.EXISTS_EQUATION HolBase.B D.eepth eq th) rthm)
  let fethm ← CHOOSE (fn, eth) rethm
  let pcons ← liftExcept ((conjuncts (concl rthm)).mapM (fun c => do
      return repeat' rator (← rand (repeat' (fun t => (dest_forall t).map Prod.snd) c))))
  GENL pcons fethm

/- ---------------------------------------------------------------------- -/
/- Basic function: returns induction and recursion separately. No parser. -/
/- ---------------------------------------------------------------------- -/

/-- `define_type_raw def`, the first of ind_types.ml's three (712-738). -/
def define_type_raw1 [HolBase] (D : DefTypeRaw)
    (def_ : List (hol_type × List (String × List hol_type))) : ExceptT String IO (thm × thm) := do
  let (defs, rth, ith) ← justify_inductive_type_model D def_
  let neths ← prove_model_inhabitation rth
  let tybijpairs ← neths.mapM (define_inductive_type D defs)
  let preds := neths.map (fun th => repeat' rator (concl th))
  let mkdests ← liftExcept (tybijpairs.mapM (fun (p : thm × thm) => do
      let tm ← lhand (concl p.1)
      return (← rator tm, ← rator (← rand tm))))
  let consindex ← liftExcept (zip preds mkdests)
  let condefs ← (CONJUNCTS rth).mapM (define_inductive_type_constructor D defs consindex)
  let conthms ← condefs.mapM (fun th => do
    RIGHT_BETAS (strip_abs (← liftExcept (rand (concl th)))).1 th)
  let iith ← instantiate_induction_theorem consindex ith
  let fth ← derive_induction_theorem consindex tybijpairs conthms iith rth
  let rath ← create_recursive_functions tybijpairs consindex conthms rth
  let kth ← derive_recursion_theorem D tybijpairs consindex conthms rath
  return (fth, kth)

/-- Render a parser failure (`HolCore.Parser.PErr`) as a plain message. -/
private def perrString : HolCore.Parser.PErr → String
  | .noparse  => "Noparse"
  | .fail msg => msg

/-- `parse_inductive_type_specification` (ind_types.ml 740-761).

    A parser, built from the `HolCore.Parser` combinators, that reads a Melham
    style specification string such as `"sum = INL A | INR B"` into the
    internal spec shape `List (hol_type × List (String × List hol_type))`
    consumed by `define_type_raw1`.

    The OCaml uses the pure combinators (`many`, `listof`, `a`, `++`, `>>`),
    but the inner `parse_type_loc` calls `type_of_pretype`, which is IO here
    (`mk_type`), so the whole parser lives in the IO layer `ParserM`.  The
    inner OCaml bindings become the four local `let`s below:
    `parse_type_loc`, `parse_type_conapp`, `parse_type_clause`, and
    `parse_type_definition`.  A failing `match ... | _ -> fail()` becomes a
    backtracking `.noparse`. -/
def parse_inductive_type_specification (s : String) :
    IO (Except String (List (hol_type × List (String × List hol_type)))) := do
  -- parse_type_loc: parse a pretype, then convert to a type (IO-fallible).
  let parse_type_loc : HolCore.Parser.ParserM hol_type := fun c inp => do
    match HolCore.Parser.parse_pretype c inp with
    | .error e => return .error e
    | .ok (pty, rst) =>
      match ← (HolCore.Preterm.type_of_pretype pty).run with
      | .error m => return .error (.fail m)
      | .ok ty   => return .ok (ty, rst)
  -- parse_type_conapp: `(Ident cn)::sps -> cn,sps | _ -> fail()`, then
  -- `many parse_type_loc`, yielding `(cn, tys)`.
  let parse_type_conapp : HolCore.Parser.ParserM (String × List hol_type) :=
    fun c inp =>
      match inp with
      | .Ident cn :: sps => do
          match ← HolCore.Parser.pmanyM parse_type_loc c sps with
          | .error e => return .error e
          | .ok (tys, rst) => return .ok ((cn, tys), rst)
      | _ => return .error .noparse
  -- parse_type_clause: `(Ident tn)::sps -> tn,sps | _ -> fail()`, then
  -- `a (Ident "=") ++ listof parse_type_conapp (a (Resword "|")) "..." >> snd`,
  -- yielding `(mk_vartype tn, tys)`.
  let parse_type_clause :
      HolCore.Parser.ParserM (hol_type × List (String × List hol_type)) :=
    fun c inp =>
      match inp with
      | .Ident tn :: sps => do
          let p : HolCore.Parser.ParserM (List (String × List hol_type)) :=
            HolCore.Parser.pmapM
              (HolCore.Parser.pseqM
                (HolCore.Parser.liftP (HolCore.Parser.pa (lexcode.Ident "=")))
                (HolCore.Parser.plistofM parse_type_conapp
                  (HolCore.Parser.liftP (HolCore.Parser.pa (lexcode.Resword "|")))
                  "type definition clauses"))
              Prod.snd
          match ← p c sps with
          | .error e => return .error e
          | .ok (tys, rst) => return .ok ((mk_vartype tn, tys), rst)
      | _ => return .error .noparse
  -- parse_type_definition: `listof parse_type_clause (a (Resword ";")) "..."`.
  let parse_type_definition :
      HolCore.Parser.ParserM (List (hol_type × List (String × List hol_type))) :=
    HolCore.Parser.plistofM parse_type_clause
      (HolCore.Parser.liftP (HolCore.Parser.pa (lexcode.Resword ";")))
      "type definition"
  -- fun s -> let spec,rst = (parse_type_definition o lex o explode) s in
  --          if rst = [] then spec else failwith "...junk after def".
  let c ← HolCore.Parser.mkCtx
  match HolCore.Parser.lex c (explode s) with
  | .error e => return .error (perrString e)
  | .ok toks =>
    match ← parse_type_definition c toks with
    | .error e => return .error (perrString e)
    | .ok (spec, rst) =>
        if rst.isEmpty then return .ok spec
        else return .error "parse_inductive_type_specification: junk after def"

/- ---------------------------------------------------------------------- -/
/- Use this temporary version to define the sum type.                     -/
/- ---------------------------------------------------------------------- -/

/-- `sum_INDUCT,sum_RECURSION = define_type_raw (parse_inductive_type_specification
    "sum = INL A | INR B")` (ind_types.ml 768-769), with the first
    `define_type_raw`. -/
def sum_INDUCT_RECURSION [HolBase] (D : DefTypeRaw) : ExceptT String IO (thm × thm) := do
  define_type_raw1 D (← ExceptT.mk (parse_inductive_type_specification "sum = INL A | INR B"))

/-- `OUTL = new_recursive_definition sum_RECURSION `OUTL (INL x :A+B) = x``
    (ind_types.ml 771-772). -/
def defineOUTL [HolBase] (new_recursive_definition : thm → term → IO (Except String thm))
    (sum_RECURSION : thm) : ExceptT String IO thm := do
  ExceptT.mk (new_recursive_definition sum_RECURSION (← q r"OUTL (INL x :A+B) = x"))

/-- `OUTR = new_recursive_definition sum_RECURSION `OUTR (INR y :A+B) = y``
    (ind_types.ml 773-774). -/
def defineOUTR [HolBase] (new_recursive_definition : thm → term → IO (Except String thm))
    (sum_RECURSION : thm) : ExceptT String IO thm := do
  ExceptT.mk (new_recursive_definition sum_RECURSION (← q r"OUTR (INR y :A+B) = y"))

/- ---------------------------------------------------------------------- -/
/- define_type_raw #2 (ind_types.ml 785-877).                             -/
/- ---------------------------------------------------------------------- -/

/-- The second `define_type_raw`: the first one, plus
    `generalize_recursion_theorem`'s `ELIM_OUTCOMBS` (built once). -/
structure DefTypeRaw2 where
  D : DefTypeRaw
  OUTL : thm
  OUTR : thm
  ELIM_OUTCOMBS : ioconv

instance : Inhabited DefTypeRaw2 := ⟨⟨default, default, default, fun _ => pure (.error "")⟩⟩

/-- `ELIM_OUTCOMBS = GEN_REWRITE_RULE TOP_DEPTH_CONV [OUTL; OUTR]`
    (ind_types.ml 787). -/
@[nospecialize]
def setupDefTypeRaw2 [HolBase] (D : DefTypeRaw) (OUTL OUTR : thm) :
    ExceptT String IO DefTypeRaw2 := do
  return { D, OUTL, OUTR, ELIM_OUTCOMBS := ← GEN_REWRITE_CONV_NET TOP_DEPTH_CONV [OUTL, OUTR] }

/-- The `mk_sum` of `generalize_recursion_theorem` (ind_types.ml 788-792). -/
partial def mk_sum (tys : List hol_type) : ExceptT String IO hol_type := do
  let k := tys.length
  if k == 1 then return ← liftExcept (hd tys)
  let (tys1, tys2) ← liftExcept (chop_list (k / 2) tys)
  mkType "sum" [← mk_sum tys1, ← mk_sum tys2]

/-- The `mk_inls` of `generalize_recursion_theorem` (ind_types.ml 793-803). -/
partial def mk_inls (ty : hol_type) : ExceptT String IO (List term) := do
  let rec go (ty : hol_type) : ExceptT String IO (List term) := do
    if is_vartype ty then return [mk_var "x" ty]
    let [ty1, ty2] := (← liftExcept (dest_type ty)).2 | throw "mk_inls"
    let inls1 ← go ty1
    let inls2 ← go ty2
    let inl ← mkConst "INL" [(ty1, aty), (ty2, bty)]
    let inr ← mkConst "INR" [(ty1, aty), (ty2, bty)]
    return (← liftExcept (inls1.mapM (mk_comb inl))) ++ (← liftExcept (inls2.mapM (mk_comb inr)))
  let bods ← go ty
  liftExcept (bods.mapM (fun t => do mk_abs (← find_term is_var t) t))

/-- The `mk_outls` of `generalize_recursion_theorem` (ind_types.ml 804-812). -/
partial def mk_outls (ty : hol_type) : ExceptT String IO (List term) := do
  let rec go (sof : term) (ty : hol_type) : ExceptT String IO (List term) := do
    if is_vartype ty then return [sof]
    let [ty1, ty2] := (← liftExcept (dest_type ty)).2 | throw "mk_outls"
    let outl ← mkConst "OUTL" [(ty1, aty), (ty2, bty)]
    let outr ← mkConst "OUTR" [(ty1, aty), (ty2, bty)]
    return (← go (← liftExcept (mk_comb outl sof)) ty1) ++
           (← go (← liftExcept (mk_comb outr sof)) ty2)
  let x := mk_var "x" ty
  liftExcept ((← go x ty).mapM (mk_abs x))

/-- The `mk_newfun` of `generalize_recursion_theorem` (ind_types.ml 813-821). -/
def mk_newfun [HolBase] (fn outl : term) : ExceptT String IO thm := do
  let (s, ty) ← liftExcept (dest_var fn)
  let dty ← liftExcept (do hd (← dest_type ty).2)
  let x := mk_var "x" dty
  let (y, bod) ← liftExcept (dest_abs outl)
  let r ← liftExcept (do mk_abs x ((← vsubst [(← mk_comb fn x, y)]) bod))
  let l := mk_var s (type_of r)
  let th1 ← ASSUME (← liftExcept (mkEq l r))
  RIGHT_BETAS [x] th1

/- ---------------------------------------------------------------------- -/
/- Generalize the recursion theorem to multiple domain types.             -/
/- (We needed to use a single type to justify it via a proforma theorem.) -/
/-                                                                        -/
/- NB! Before this is called nontrivially (i.e. more than one new type)   -/
/- the type constructor ":sum", used internally, must have been defined.  -/
/- ---------------------------------------------------------------------- -/

/-- `generalize_recursion_theorem th` (ind_types.ml 822-874). -/
def generalize_recursion_theorem [HolBase] (D2 : DefTypeRaw2) (th : thm) :
    ExceptT String IO thm := do
  let (_avs, ebod) := strip_forall (concl th)
  let (evs, bod) := strip_exists ebod
  let n := evs.length
  if n == 1 then return th
  let tys := (List.range n).map (fun i => mk_vartype ("Z" ++ toString i))
  let sty ← mk_sum tys
  let inls ← mk_inls sty
  let outls ← mk_outls sty
  let zty := type_of (← liftExcept (do rand (strip_forall (← hd (conjuncts bod))).2))
  let ith ← INST_TYPE [(sty, zty)] th
  let (_avs, ebod) := strip_forall (concl ith)
  let (evs, bod) := strip_exists ebod
  let fns' ← map2M mk_newfun evs outls
  let fnalist ← liftExcept (do zip evs (← fns'.mapM (fun th => do rator (← lhs (concl th)))))
  let inlalist ← liftExcept (zip evs inls)
  let outlalist ← liftExcept (zip evs outls)
  let hack_clause (tm : term) : ExceptT String IO (term × term) := do
    let (_avs, bod) := strip_forall tm
    let (l, r) ← liftExcept (dest_eq bod)
    let (fn, args) := strip_comb r
    let pargs ← args.mapM (fun a => do
      let g ← liftM (genvar (type_of a) : IO term)
      if is_var a then return (g, g)
      let outl ← liftExcept (do Lib.assoc (← rator a) outlalist)
      return (← liftExcept (mk_comb outl g), g))
    let (args', args'') := unzip pargs
    let inl ← liftExcept (do Lib.assoc (← rator l) inlalist)
    let rty ← liftExcept (do hd (← dest_type (type_of inl)).2)
    let nty ← args'.foldrM (fun a acc => mkFunTy (type_of a) acc) rty
    let fn' := mk_var (← liftExcept (dest_var fn)).1 nty
    let r' ← liftExcept (do list_mk_abs args'' (← mk_comb inl (← list_mk_comb fn' args')))
    return (r', fn)
  let defs ← (conjuncts bod).mapM hack_clause
  let jth ← BETA_RULE (← SPECL (defs.map Prod.fst) ith)
  let bth ← ASSUME (strip_exists (concl jth)).2
  let finish_clause (th : thm) : ExceptT String IO thm := do
    let (avs, bod) := strip_forall (concl th)
    let outl ← liftExcept (do Lib.assoc (← rator (← lhand bod)) outlalist)
    GENL avs (← BETA_RULE (← AP_TERM outl (← SPECL avs th)))
  let cth ← end_itlist CONJ (← (CONJUNCTS bth).mapM finish_clause)
  let dth ← CONV_RULE D2.ELIM_OUTCOMBS cth
  let eth ← GEN_REWRITE_RULE ONCE_DEPTH_CONV (← fns'.mapM SYM) dth
  let fth ← (fnalist.map Prod.snd).foldrM SIMPLE_EXISTS eth
  let dtms ← liftExcept (fns'.mapM (fun th => hd (hyp th)))
  let gth ← dtms.foldrM (fun e th => do
    let (l, r) ← liftExcept (dest_eq e)
    MP (← INST [(r, l)] (← DISCH e th)) (REFL r)) fth
  let hth ← PROVE_HYP jth (← evs.foldrM SIMPLE_CHOOSE gth)
  let xvs ← liftExcept ((conjuncts (concl eth)).mapM (fun c => do
    return (strip_comb (← rand (strip_forall c).2)).1))
  GENL xvs hth

/-- `define_type_raw def`, the second of ind_types.ml's three (875-877). -/
def define_type_raw2 [HolBase] (D2 : DefTypeRaw2)
    (def_ : List (hol_type × List (String × List hol_type))) : ExceptT String IO (thm × thm) := do
  let (ith, rth) ← define_type_raw1 D2.D def_
  return (ith, ← generalize_recursion_theorem D2 rth)

/- ---------------------------------------------------------------------- -/
/- Set up options and lists.                                              -/
/- ---------------------------------------------------------------------- -/

/-- `option_INDUCT,option_RECURSION` (ind_types.ml 880-882). -/
def option_INDUCT_RECURSION [HolBase] (D2 : DefTypeRaw2) : ExceptT String IO (thm × thm) := do
  define_type_raw2 D2 (← ExceptT.mk (parse_inductive_type_specification "option = NONE | SOME A"))

/-- `list_INDUCT,list_RECURSION` (ind_types.ml 884-886). -/
def list_INDUCT_RECURSION [HolBase] (D2 : DefTypeRaw2) : ExceptT String IO (thm × thm) := do
  define_type_raw2 D2 (← ExceptT.mk (parse_inductive_type_specification "list = NIL | CONS A list"))

/-- `FORALL_OPTION_THM` (ind_types.ml 888-890). -/
def prove_FORALL_OPTION_THM [HolBase] (option_INDUCT : thm) : ExceptT String IO thm := do
  prove r"!P:A option->bool. (!x. P x) <=> P NONE /\ !a. P(SOME a)"
    (GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [option_INDUCT] THEN SIMP_TAC [])

/-- `EXISTS_OPTION_THM` (ind_types.ml 892-895). -/
def prove_EXISTS_OPTION_THM [HolBase] (FORALL_OPTION_THM : thm)
    (MESON : List thm → term → IO (Except String thm))
    (MESON_TAC : List thm → tactic) : ExceptT String IO thm := do
  prove r"!P:A option->bool. (?x. P x) <=> P NONE \/ ?a. P(SOME a)"
    (GEN_TAC THEN
     REWRITE_TAC [← ExceptT.mk (MESON [] (← q r"(?x. P x) <=> ~(!x. ~P x)"))] THEN
     REWRITE_TAC [FORALL_OPTION_THM] THEN MESON_TAC [])

/- ---------------------------------------------------------------------- -/
/- Tools for proving injectivity and distinctness of constructors.        -/
/- ---------------------------------------------------------------------- -/

/-- `prove_constructors_injective` (ind_types.ml 902-926): builds `DEPAIR`
    once and returns `fun ax -> ...`. -/
def prove_constructors_injective [HolBase] (BETA_THM PAIR_EQ : thm)
    (mk_pair : term × term → IO (Except String term)) :
    ExceptT String IO (thm → ExceptT String IO thm) := do
  let DEPAIR := CONV_RULE (← GEN_REWRITE_CONV_NET TOP_SWEEP_CONV [PAIR_EQ])
  let prove_distinctness (ax : thm) (pat : term) : ExceptT String IO thm := do
    let (f, args) := strip_comb pat
    let rt ← end_itlist (fun a b => ExceptT.mk (mk_pair (a, b))) args
    let ty ← mkFunTy (type_of pat) (type_of rt)
    let fn ← liftM (genvar ty : IO term)
    let dtm ← liftExcept (do mkEq (← mk_comb fn pat) rt)
    let eth ← HolMath.Recursion.prove_recursive_functions_exist BETA_THM ax
      (← liftExcept (list_mk_forall args dtm))
    let args' ← liftExcept (variants args args)
    let atm ← liftExcept (do mkEq pat (← list_mk_comb f args'))
    let ath ← ASSUME atm
    let bth ← AP_TERM fn ath
    let cth1 ← SPECL args (← ASSUME (← liftExcept (dest_exists (concl eth))).2)
    let cth2 ← INST (← liftExcept (zip args' args)) cth1
    let pth ← TRANS (← TRANS (← SYM cth1) bth) cth2
    let qth ← DEPAIR pth
    let qtm := concl qth
    let rth ← (CONJUNCTS (← ASSUME qtm)).foldlM (fun acc th => MK_COMB (acc, th)) (REFL f)
    let tth ← IMP_ANTISYM_RULE (← DISCH atm qth) (← DISCH qtm rth)
    let uth ← GENL args (← GENL args' tth)
    PROVE_HYP eth (← SIMPLE_CHOOSE fn uth)
  return fun ax => do
    let cls := conjuncts (strip_exists (strip_forall (concl ax)).2).2
    let pats ← liftExcept (cls.mapM (fun c => do rand (← lhand (strip_forall c).2)))
    end_itlist CONJ (← mapfilterM (prove_distinctness ax) pats)

/-- `prove_constructors_distinct` (ind_types.ml 928-959): parses `num_ty`
    and proves `NEGATE`'s tautology once, and returns `fun ax -> ...`. -/
def prove_constructors_distinct [HolBase] (BETA_THM : thm) (numK : HolMath.Nums.NumeralConsts)
    (NUM_EQ_CONV : ioconv) : ExceptT String IO (thm → ExceptT String IO thm) := do
  let num_ty ← qty r"num"
  let rec allopairs {α β : Type} (f : α → α → β) : List α → List α → List β
    | [], _ => []
    | _, [] => []
    | h :: t, _ :: m => m.map (f h) ++ allopairs f t m
  let negth ← TAUT (← q r"a ==> F <=> ~a")
  let NEGATE (th : thm) : ExceptT String IO thm := do GEN_ALL (← CONV_RULE (REWR_CONV negth) th)
  let prove_distinct (ax : thm) (pat : List term) : ExceptT String IO (List thm) := do
    let nums ← liftExcept ((List.range pat.length).mapM (fun k =>
      HolMath.Nums.mk_small_numeral numK (Int.ofNat k)))
    let fn ← liftM (genvar (← mkType "fun" [type_of (← liftExcept (hd pat)), num_ty]) : IO term)
    let ls ← liftExcept (pat.mapM (mk_comb fn))
    let defs ← map2M (fun l r => liftExcept (do
      list_mk_forall (frees (← rand l)) (← mkEq l r))) ls nums
    let eth ← HolMath.Recursion.prove_recursive_functions_exist BETA_THM ax
      (← liftExcept (list_mk_conj defs))
    let (ev, bod) ← liftExcept (dest_exists (concl eth))
    let REWRITE := CONV_RULE (← GEN_REWRITE_CONV_NET ONCE_DEPTH_CONV (CONJUNCTS (← ASSUME bod)))
    let pat' ← liftExcept (pat.mapM (fun t => do
      let (f, args) := if HolMath.Nums.is_numeral t then (t, []) else strip_comb t
      list_mk_comb f (← variants args args)))
    let pairs ← liftExcept ((allopairs (fun a b => (a, b)) pat pat').mapM (fun p => mkEq p.1 p.2))
    let nths ← pairs.mapM (fun p => do REWRITE (← AP_TERM fn (← ASSUME p)))
    let fths ← map2M (fun t th => do NEGATE (← DISCH t (← CONV_RULE NUM_EQ_CONV th))) pairs nths
    return CONJUNCTS (← PROVE_HYP eth (← SIMPLE_CHOOSE ev (← end_itlist CONJ fths)))
  return fun ax => do
    let cls := conjuncts (strip_exists (strip_forall (concl ax)).2).2
    let lefts ← liftExcept (cls.mapM (fun c => do dest_comb (← lhand (strip_forall c).2)))
    let fns := itlist (fun (p : term × term) acc => insert p.1 acc) lefts []
    let pats := fns.map (fun f => (lefts.filter (fun p => p.1 == f)).map Prod.snd)
    end_itlist CONJ (← end_itlist (fun a b => pure (a ++ b)) (← mapfilterM (prove_distinct ax) pats))

/- ---------------------------------------------------------------------- -/
/- Automatically prove the case analysis theorems.                        -/
/- ---------------------------------------------------------------------- -/

/-- `prove_cases_thm th` (ind_types.ml 964-1006).  `eepth` is
    `EXISTS_EQUATION`'s proforma. -/
partial def prove_cases_thm [HolBase] (eepth : thm) (th : thm) : ExceptT String IO thm := do
  let mk_exclauses (x : term) (rpats : List term) : Except String term := do
    let xts ← rpats.mapM (fun t => do list_mk_exists (frees t) (← mkEq x t))
    mk_abs x (← list_mk_disj xts)
  let prove_triv (tm : term) : ExceptT String IO thm := do
    let (_evs, bod) := strip_exists tm
    let (l, r) ← liftExcept (dest_eq bod)
    if l == r then return REFL l
    let (lf, largs) := strip_comb l
    let (rf, rargs) := strip_comb r
    if lf == rf then
      let ths ← (← liftExcept (zip rargs largs)).mapM (fun p => do ASSUME (← liftExcept (mkEq p.1 p.2)))
      let th1 ← ths.foldlM (fun acc th => MK_COMB (acc, th)) (REFL lf)
      liftExcept ((ths.map concl).foldrM (fun eq th => IndDefs.EXISTS_EQUATION HolBase.B eepth eq th)
        (← SYM th1))
    else throw "prove_triv"
  let rec prove_disj (tm : term) : ExceptT String IO thm := do
    if is_disj tm then
      let (l, r) ← liftExcept (dest_disj tm)
      tryWith (do DISJ1 (← prove_triv l) r) (do DISJ2 l (← prove_disj r))
    else prove_triv tm
  let prove_eclause (tm : term) : ExceptT String IO thm := do
    let (avs, bod) := strip_forall tm
    let ctm ← if is_imp bod then liftExcept (rand bod) else pure bod
    let cth ← prove_disj ctm
    let dth ← if is_imp bod then do DISCH (← liftExcept (lhand bod)) cth else pure cth
    GENL avs dth
  let (_avs, bod) := strip_forall (concl th)
  let cls := (conjuncts (← liftExcept (lhand bod))).map (fun t => (strip_forall t).2)
  let pats ← liftExcept (cls.mapM (fun t => if is_imp t then rand t else .ok t))
  let spats ← liftExcept (pats.mapM dest_comb)
  let preds := itlist (fun (p : term × term) acc => insert p.1 acc) spats []
  let rpatlist := preds.map (fun pr => (spats.filter (fun p => p.1 == pr)).map Prod.snd)
  let xs ← liftExcept (do make_args "x" (freesl pats) (← rpatlist.mapM (fun l => do
    return type_of (← hd l))))
  let xpreds ← map2M (fun x rp => liftExcept (mk_exclauses x rp)) xs rpatlist
  let ith ← BETA_RULE (← INST (← liftExcept (zip xpreds preds)) (← SPEC_ALL th))
  let eclauses := conjuncts (← liftExcept (dest_imp (concl ith))).1
  MP ith (← end_itlist CONJ (← eclauses.mapM prove_eclause))

/- ---------------------------------------------------------------------- -/
/- Now deal with nested recursion. Need a store of previous theorems.     -/
/- ---------------------------------------------------------------------- -/

/- ---------------------------------------------------------------------- -/
/- Also add a cached rewrite of distinctness and injectivity theorems.    -/
/- Since                                                                  -/
/- there can be quadratically many distinctness clauses, it would really  -/
/- be                                                                     -/
/- preferable to have a conversion, but this seems OK up 100              -/
/- constructors.                                                          -/
/- ---------------------------------------------------------------------- -/

/-- The element type of `distinctness_store` and `injectivity_store`
    (ind_types.ml 1023-1024).  The refs live in Session. -/
abbrev RectypeStore := List (String × thm)

/-- `extend_rectype_net (tyname,(_,_,rth))` (ind_types.ml 1026-1033), given
    `prove_constructors_distinct` and `prove_constructors_injective`.  Takes
    the current contents of the three stores and returns the new ones. -/
def extend_rectype_net [HolBase]
    (prove_constructors_distinct prove_constructors_injective : thm → ExceptT String IO thm)
    (entry : String × (Int × thm × thm)) (curNet : HolCore.Nets.net Simp.gconv)
    (curDist curInj : RectypeStore) :
    ExceptT String IO (HolCore.Nets.net Simp.gconv × RectypeStore × RectypeStore) := do
  let (tyname, (_, _, rth)) := entry
  let ths1 ← tryWith (do return [← prove_constructors_distinct rth]) (pure [])
  let ths2 ← tryWith (do return [← prove_constructors_injective rth]) (pure [])
  let canon_thl ← (ths1 ++ ths2).foldrM
    (fun th acc => ExceptT.mk (Simp.mk_rewrites HolBase.B false th acc)) []
  let dist' := ths1.map (fun th => (tyname, th)) ++ curDist
  let inj' := ths2.map (fun th => (tyname, th)) ++ curInj
  let net' ← canon_thl.foldrM
    (fun th acc => ExceptT.mk (Simp.net_of_thm HolBase.B true th acc)) curNet
  return (net', dist', inj')

/- ---------------------------------------------------------------------- -/
/- Return distinctness and injectivity for a type by simple lookup.       -/
/- ---------------------------------------------------------------------- -/

/-- `distinctness ty = assoc ty (!distinctness_store)` (ind_types.ml 1041). -/
def distinctness (store : RectypeStore) (ty : String) : Except String thm :=
  Lib.assoc ty store

/-- `injectivity ty = assoc ty (!injectivity_store)` (ind_types.ml 1043). -/
def injectivity (store : RectypeStore) (ty : String) : Except String thm :=
  Lib.assoc ty store

/-- `cases ty` (ind_types.ml 1045-1047). -/
def cases [HolBase] (eepth num_CASES : thm) (store : List (String × (Int × thm × thm)))
    (ty : String) : ExceptT String IO thm := do
  if ty == "num" then return num_CASES
  let (_, ith, _) ← liftExcept (Lib.assoc ty store)
  prove_cases_thm eepth ith

/-- `option_DISTINCT` (ind_types.ml 1049-1051); `distinctness "option"` is
    passed in. -/
def prove_option_DISTINCT [HolBase] (optionDistinct : thm) : ExceptT String IO thm := do
  prove r"!a:A. ~(SOME a = NONE)" (REWRITE_TAC [optionDistinct])

/-- `option_INJ` (ind_types.ml 1053-1055); `injectivity "option"` is passed
    in. -/
def prove_option_INJ [HolBase] (optionInj : thm) : ExceptT String IO thm := do
  prove r"!a b:A. SOME a = SOME b <=> a = b" (REWRITE_TAC [optionInj])

end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/- Convenient definitions for type isomorphism (ind_types.ml 1061-1080). -/

@[nospecialize]
def setupISO [HolBase]
    (new_definition' : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic) :
    IO (Except String (thm × thm × thm × thm)) := ExceptT.run do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let { FUN_EQ_THM, .. } := HolBase.C

  let ISO ← new_definition
   r"ISO (f:A->B) (g:B->A) <=> (!x. f(g x) = x) /\ (!y. g(f y) = y)"

  let ISO_REFL ← prove
   r"ISO (\x:A. x) (\x. x)"
   (REWRITE_TAC [ISO])

  let ISO_FUN ← prove
   r"ISO (f:A->A') f' /\ ISO (g:B->B') g'
   ==> ISO (\h a'. g(h(f' a'))) (\h a. g'(h(f a)))"
   (REWRITE_TAC [ISO, FUN_EQ_THM] THEN MESON_TAC [])

  let ISO_USAGE ← prove
   r"ISO f g
   ==> (!P. (!x. P x) <=> (!x. P(g x))) /\
       (!P. (?x. P x) <=> (?x. P(g x))) /\
       (!(a:A) (b:B). (a = g b) <=> (f a = b))"
   (REWRITE_TAC [ISO, FUN_EQ_THM] THEN MESON_TAC [])

  return (ISO, ISO_REFL, ISO_FUN, ISO_USAGE)

end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax
open HolCore.Bool (list_mk_exists list_mk_disj mk_exists)
open HolCore.Classic (mk_select)
open HolCore.Parser (lexcode)

/- ---------------------------------------------------------------------- -/
/- define_type_raw #3: nested types (ind_types.ml 1084-1387).             -/
/- ---------------------------------------------------------------------- -/

/- ---------------------------------------------------------------------- -/
/- Hence extend type definition to nested types.                          -/
/- ---------------------------------------------------------------------- -/

/-- What the third `define_type_raw` binds before `fun def -> ...`
    (ind_types.ml 1084-1281): `ISO_EXPAND_CONV`, `DE_EXISTENTIALIZE_RULE`'s
    `pth`, `SIMPLE_BETA_RULE`'s rewrite and `REWRITE_FUN_EQ_RULE`'s net (made
    from `basic_net()` as it is when this is built).  `getStore` reads
    `!inductive_type_store`; `addEntries` does
    `inductive_type_store := newentries @ (!inductive_type_store);
     do_list extend_rectype_net newentries`. -/
structure DefTypeRaw3 where
  D2 : DefTypeRaw2
  ISO : thm
  ISO_REFL : thm
  ISO_FUN : thm
  ISO_USAGE : thm
  ISO_EXPAND_CONV : ioconv
  dePth : thm
  simpleBetaConv : ioconv
  funEqNet : HolCore.Nets.net Simp.gconv
  getStore : IO (List (String × (Int × thm × thm)))
  addEntries : List (String × (Int × thm × thm)) → IO (Except String Unit)

instance : Inhabited DefTypeRaw3 :=
  ⟨⟨default, default, default, default, default, fun _ => pure (.error ""), default,
    fun _ => pure (.error ""), HolCore.Nets.empty_net, pure [], fun _ => pure (.error "")⟩⟩

/-- Build the `DefTypeRaw3` (ind_types.ml 1112, 1131-1136, 1274, 1278-1280). -/
@[nospecialize]
def setupDefTypeRaw3 [HolBase] (D2 : DefTypeRaw2) (ISO ISO_REFL ISO_FUN ISO_USAGE : thm)
    (ETA_AX SELECT_AX FUN_EQ_THM : thm)
    (getStore : IO (List (String × (Int × thm × thm))))
    (addEntries : List (String × (Int × thm × thm)) → IO (Except String Unit)) :
    ExceptT String IO DefTypeRaw3 := do
  let ISO_EXPAND_CONV ← PURE_ONCE_REWRITE_CONV_NET [ISO]
  let dePth ← prove r"(?) P ==> (c = (@)P) ==> P c"
    (GEN_REWRITE_TAC (fun c => LAND_CONV (RAND_CONV c)) [← GSYM ETA_AX] THEN
     DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN
     MATCH_MP_TAC SELECT_AX THEN POP_ASSUM ACCEPT_TAC)
  let simpleBetaConv ← PURE_REWRITE_CONV_NET [D2.D.BETA_THM, FUN_EQ_THM]
  let ths ← ExceptT.mk (Simp.mk_rewrites HolBase.B false FUN_EQ_THM [])
  let funEqNet ← ths.foldrM (fun th acc => ExceptT.mk (Simp.net_of_thm HolBase.B false th acc))
    (← liftM (Simp.basic_net : IO (HolCore.Nets.net Simp.gconv)))
  return { D2, ISO, ISO_REFL, ISO_FUN, ISO_USAGE, ISO_EXPAND_CONV, dePth, simpleBetaConv,
           funEqNet, getStore, addEntries }

/- ---------------------------------------------------------------------- -/
/- Dispose of trivial antecedent.                                         -/
/- ---------------------------------------------------------------------- -/

/-- `TRIV_ANTE_RULE` (ind_types.ml 1090-1106). -/
def TRIV_ANTE_RULE [HolBase] (th : thm) : ExceptT String IO thm := do
  let TRIV_IMP_CONV (tm : term) : ExceptT String IO thm := do
    let (avs, bod) := strip_forall tm
    let bth ←
      if is_eq bod then pure (REFL (← liftExcept (rand bod)))
      else do
        let (ant, con) ← liftExcept (dest_imp bod)
        let ith ← ExceptT.mk (SUBS_CONV (CONJUNCTS (← ASSUME ant)) (← liftExcept (lhs con)))
        DISCH ant ith
    GENL avs bth
  let tm := concl th
  if is_imp tm then
    let (ant, _con) ← liftExcept (dest_imp (concl th))
    MP th (← end_itlist CONJ (← (conjuncts ant).mapM TRIV_IMP_CONV))
  else pure th

/- ---------------------------------------------------------------------- -/
/- Lift type bijections to "arbitrary" (well, free rec or function) type. -/
/- ---------------------------------------------------------------------- -/

/-- `lift_type_bijections iths cty` (ind_types.ml 1114-1125). -/
partial def lift_type_bijections [HolBase] (R : DefTypeRaw3) (iths : List thm) (cty : hol_type) :
    ExceptT String IO thm := do
  let itys ← liftExcept (iths.mapM (fun th => do
    hd (← dest_type (type_of (← lhand (concl th)))).2))
  tryWith (liftExcept (do Lib.assoc cty (← zip itys iths))) (do
    if !(exists' (fun ity => occurs_in ity cty) itys) then INST_TYPE [(cty, aty)] R.ISO_REFL
    else
      let (tycon, isotys) ← liftExcept (dest_type cty)
      if tycon == "fun" then
        MATCH_MP R.ISO_FUN (← end_itlist CONJ (← isotys.mapM (lift_type_bijections R iths)))
      else throw ("lift_type_bijections: Unexpected type operator \"" ++ tycon ++ "\""))

/-- `DE_EXISTENTIALIZE_RULE th` (ind_types.ml 1137-1145), with `USE_PTH =
    MATCH_MP pth`. -/
partial def DE_EXISTENTIALIZE_RULE [HolBase] (pth th : thm) : ExceptT String IO (List term × thm) := do
  if !(is_exists (concl th)) then return ([], th)
  let th1 ← MATCH_MP pth th
  let v1 ← liftExcept (do rand (← rand (concl th1)))
  let gv ← liftM (genvar (type_of v1) : IO term)
  let th2 ← CONV_RULE BETA_CONV (← UNDISCH (← INST [(gv, v1)] th1))
  let (vs, th3) ← DE_EXISTENTIALIZE_RULE pth th2
  return (gv :: vs, th3)

/-- `grab_type = type_of o rand o lhand o snd o strip_forall` (ind_types.ml
    1147). -/
def grab_type (tm : term) : Except String hol_type := do
  return type_of (← rand (← lhand (strip_forall tm).2))

/-- `clause_corresponds cl0 cl1` (ind_types.ml 1149-1157). -/
def clause_corresponds (cl0 cl1 : term) : Except String Bool := do
  let (f0, ctm0) ← dest_comb (← lhs cl0)
  let (c0, _) ← dest_const (strip_comb ctm0).1
  let (dty0, rty0) ← dest_fun_ty (type_of f0)
  let (f1, ctm1) ← dest_comb (← lhs cl1)
  let (c1, _) ← dest_const (strip_comb ctm1).1
  let (dty1, rty1) ← dest_fun_ty (type_of f1)
  return (c0 == c1 && dty0 == rty1 && rty0 == dty1)

/- ---------------------------------------------------------------------- -/
/- Prove isomorphism of nested types where former is the smaller.         -/
/- ---------------------------------------------------------------------- -/

/-- `prove_inductive_types_isomorphic n k (ith0,rth0) (ith1,rth1)`
    (ind_types.ml 1159-1256). -/
def prove_inductive_types_isomorphic [HolBase] (R : DefTypeRaw3) (n k : Nat)
    (ir0 ir1 : thm × thm) : ExceptT String IO (thm × thm) := do
  let (ith0, rth0) := ir0
  let (ith1, rth1) := ir1
  let sth0 ← SPEC_ALL rth0
  let sth1 ← SPEC_ALL rth1
  let t_tm := concl HolBase.B.TRUTH
  let (pevs0, pbod0) := strip_exists (concl sth0)
  let (pevs1, pbod1) := strip_exists (concl sth1)
  let (pcjs0, _qcjs0) ← liftExcept (chop_list k (conjuncts pbod0))
  let (pcjs1, _qcjs1) ← liftExcept (do chop_list k (← chop_list n (conjuncts pbod1)).2)
  -- OCaml's `compare` on pairs is lexicographic.
  let tyal0 := @setify (hol_type × hol_type) _ lexOrd
    (← liftExcept (do zip (← pcjs1.mapM grab_type) (← pcjs0.mapM grab_type)))
  let tyal1 := tyal0.map (fun (a, b) => (b, a))
  let tyins0 ← pevs0.mapM (fun f => do
    let (domty, ranty) ← liftExcept (dest_fun_ty (type_of f))
    return (← tysubst tyal0 domty, ranty))
  let tyins1 ← pevs1.mapM (fun f => do
    let (domty, ranty) ← liftExcept (dest_fun_ty (type_of f))
    return (← tysubst tyal1 domty, ranty))
  let tth0 ← INST_TYPE tyins0 sth0
  let tth1 ← INST_TYPE tyins1 sth1
  let (_evs0, bod0) := strip_exists (concl tth0)
  let (_evs1, bod1) := strip_exists (concl tth1)
  let (lcjs0, rcjs0) ← liftExcept (chop_list k ((conjuncts bod0).map (fun t => (strip_forall t).2)))
  let (lcjs1, rcjsx) ← liftExcept (do
    chop_list k ((← chop_list n (conjuncts bod1)).2.map (fun t => (strip_forall t).2)))
  -- ind_types.ml 1182: OCaml `find (clause_corresponds t) rcjsx` propagates the
  -- predicate's Failure, so use a failure-propagating find per element.
  let rec findCorr (t : term) : List term → Except String term
    | []       => failwith "find"
    | t1 :: ts => do if (← clause_corresponds t t1) then pure t1 else findCorr t ts
  let rcjs1 ← liftExcept (rcjs0.mapM (fun t => findCorr t rcjsx))
  let findArg (ws : List term) (a : term) : Except String term :=
    Lib.find (fun t => is_comb t && (match rand t with | .ok r => r == a | .error _ => false)) ws
  let proc_clause (tm0 tm1 : term) : ExceptT String IO ((term × term) × (term × term)) := do
    let (l0, r0) ← liftExcept (dest_eq tm0)
    let (l1, r1) ← liftExcept (dest_eq tm1)
    let (vc0, wargs0) := strip_comb r0
    let (_con0, vargs0) := strip_comb (← liftExcept (rand l0))
    let gargs0 ← wargs0.mapM (fun a => liftM (genvar (type_of a) : IO term))
    let nestf0 := vargs0.map (fun a => can (findArg wargs0) a)
    let targs0 ← map2M (fun a f => if f then liftExcept (findArg wargs0 a) else pure a) vargs0 nestf0
    let gvlist0 ← liftExcept (zip wargs0 gargs0)
    let xargs0 ← liftExcept (targs0.mapM (fun v => Lib.assoc v gvlist0))
    let inst0 := (← liftExcept (do
      list_mk_abs gargs0 (← list_mk_comb (strip_comb (← rand l1)).1 xargs0)), vc0)
    let (vc1, wargs1) := strip_comb r1
    let (_con1, vargs1) := strip_comb (← liftExcept (rand l1))
    let gargs1 ← wargs1.mapM (fun a => liftM (genvar (type_of a) : IO term))
    let targs1 ← map2M (fun a f => if f then liftExcept (findArg wargs1 a) else pure a) vargs1 nestf0
    let gvlist1 ← liftExcept (zip wargs1 gargs1)
    let xargs1 ← liftExcept (targs1.mapM (fun v => Lib.assoc v gvlist1))
    let inst1 := (← liftExcept (do
      list_mk_abs gargs1 (← list_mk_comb (strip_comb (← rand l0)).1 xargs1)), vc1)
    return (inst0, inst1)
  let (insts0, insts1) := unzip (← map2M proc_clause (lcjs0 ++ rcjs0) (lcjs1 ++ rcjs1))
  let uth0 ← BETA_RULE (← INST insts0 tth0)
  let uth1 ← BETA_RULE (← INST insts1 tth1)
  let (efvs0, sth0) ← DE_EXISTENTIALIZE_RULE R.dePth uth0
  let (efvs1, sth1) ← DE_EXISTENTIALIZE_RULE R.dePth uth1
  let efvs2 ← liftExcept (efvs0.mapM (fun t1 => do
    let key ← hd (← tl (← dest_type (type_of t1)).2)
    Lib.find (fun t2 => match (do hd (← dest_type (type_of t2)).2) with
      | .ok h => h == key
      | .error _ => false) efvs1))
  let isotms ← map2M (fun ff gg => ExceptT.mk (list_mk_icomb "ISO" [ff, gg])) efvs0 efvs2
  let ctm ← liftExcept (list_mk_conj isotms)
  let cth1 ← ExceptT.mk (R.ISO_EXPAND_CONV ctm)
  let ctm1 ← liftExcept (rand (concl cth1))
  let cjs := conjuncts ctm1
  let eee := (List.range cjs.length).map (fun n => n % 2 == 0)
  let (cjs1, cjs2) := partition Prod.fst (← liftExcept (zip eee cjs))
  let ctm2 ← liftExcept (do
    mk_conj (← list_mk_conj (cjs1.map Prod.snd)) (← list_mk_conj (cjs2.map Prod.snd)))
  let detrivConv ← REWRITE_CONV_NET [sth0, sth1]
  let DETRIV_RULE (th : thm) : ExceptT String IO thm := do TRIV_ANTE_RULE (← CONV_RULE detrivConv th)
  let jth (ith : thm) (tms : List term) : ExceptT String IO thm := do
    let itha ← SPEC_ALL ith
    let icjs := conjuncts (← liftExcept (rand (concl itha)))
    let cinsts ← tms.mapM (fun tm => tryfindM' (fun vtm => term_match [] vtm tm) icjs)
    let tvs := subtract (strip_forall (concl ith)).1
      (itlist (fun (ci : Drule.instantiation) acc => union (ci.2.1.map Prod.snd) acc) cinsts [])
    let ctvs ← liftExcept (tvs.mapM (fun p => do
      let x := mk_var "x" (← hd (← dest_type (type_of p)).2)
      return (← mk_abs x t_tm, p)))
    DETRIV_RULE (← INST ctvs (← cinsts.foldrM INSTANTIATE itha))
  let jth0 ← jth ith0 (conjuncts (← liftExcept (rand ctm2)))
  let jth1 ← jth ith1 (conjuncts (← liftExcept (lhand ctm2)))
  let cths4 ← map2M CONJ (CONJUNCTS jth0) (CONJUNCTS jth1)
  let isoConv ← PURE_ONCE_REWRITE_CONV_NET [← GSYM R.ISO]
  let cths5 ← cths4.mapM (CONV_RULE isoConv)
  let cth6 ← end_itlist CONJ cths5
  return (cth6, ← CONJ sth0 sth1)

/- ---------------------------------------------------------------------- -/
/- Define nested type by doing a 1-level unwinding.                       -/
/- ---------------------------------------------------------------------- -/

/-- `SCRUB_ASSUMPTION th` (ind_types.ml 1261-1267). -/
def SCRUB_ASSUMPTION [HolBase] (th : thm) : ExceptT String IO thm := do
  let hyps := hyp th
  let eqn ← liftExcept (Lib.find (fun t =>
    match lhs t with
    | .ok x => forall' (fun u => match rand u with
        | .ok r => !(free_in x r)
        | .error _ => true) hyps
    | .error _ => false) hyps)
  let (l, r) ← liftExcept (dest_eq eqn)
  MP (← INST [(r, l)] (← DISCH eqn th)) (REFL r)

/-- lib.ml's `repeat`, for a rule. -/
partial def repeatRule (f : thm → ExceptT String IO thm) (x : thm) : ExceptT String IO thm :=
  tryWith (do repeatRule f (← f x)) (pure x)

/-- `define_type_basecase def` (ind_types.ml 1269-1272), with the second
    `define_type_raw`. -/
def define_type_basecase [HolBase] (R : DefTypeRaw3)
    (def_ : List (hol_type × List (String × List hol_type))) : ExceptT String IO (thm × thm) := do
  let add_id (_s : String) : ExceptT String IO String := do
    return (← liftExcept (dest_var (← liftM (genvar bool_ty : IO term)))).1
  let def' ← def_.mapM (fun (ty, lis) => do
    return (ty, ← lis.mapM (fun (s, l) => do return (← add_id s, l))))
  define_type_raw2 R.D2 def'

/-- `is_nested vs ty` (ind_types.ml 1283). -/
def is_nested (vs : List hol_type) (ty : hol_type) : Bool :=
  !(is_vartype ty) && !((intersect (tyvars ty) vs).isEmpty)

/-- `modify_type alist ty` (ind_types.ml 1285-1289). -/
partial def modify_type (alist : List (hol_type × hol_type)) (ty : hol_type) : IO hol_type := do
  match Lib.rev_assoc ty alist with
  | .ok t => pure t
  | .error _ =>
    match dest_type ty with
    | .error _ => pure ty
    | .ok (tycon, tyargs) => do
      let args ← tyargs.mapM (modify_type alist)
      match ← mk_type tycon args with
      | .ok r => pure r
      | .error _ => pure ty

/-- `modify_item alist (s,l)` (ind_types.ml 1290-1291). -/
def modify_item (alist : List (hol_type × hol_type)) (sl : String × List hol_type) :
    IO (String × List hol_type) := do
  return (sl.1, ← sl.2.mapM (modify_type alist))

/-- `modify_clause alist (l,lis)` (ind_types.ml 1292-1293). -/
def modify_clause (alist : List (hol_type × hol_type))
    (cl : hol_type × List (String × List hol_type)) : IO (hol_type × List (String × List hol_type)) := do
  return (cl.1, ← cl.2.mapM (modify_item alist))

/-- `recover_clause id tm` (ind_types.ml 1294-1296). -/
def recover_clause (id : String) (tm : term) : Except String (String × List hol_type) := do
  let (con, args) := strip_comb tm
  return ((← dest_const con).1 ++ id, args.map type_of)

/-- `create_auxiliary_clauses nty` (ind_types.ml 1297-1312). -/
def create_auxiliary_clauses (R : DefTypeRaw3) (nty : hol_type) :
    ExceptT String IO (Int × List (hol_type × hol_type)
      × List (hol_type × List (String × List hol_type)) × thm × thm) := do
  let id := (← liftExcept (dest_var (← liftM (genvar bool_ty : IO term)))).1
  let (tycon, _tyargs) ← liftExcept (dest_type nty)
  let (k, ith, rth) ← match Lib.assoc tycon (← liftM R.getStore) with
    | .ok kir => pure kir
    | .error _ => throw ("Can't find definition for nested type: " ++ tycon)
  let (evs, bod) := strip_exists (strip_forall (concl rth)).2
  let cjs ← liftExcept ((conjuncts bod).mapM (fun c => lhand (strip_forall c).2))
  let rtys ← liftExcept (evs.mapM (fun e => do hd (← dest_type (type_of e)).2))
  let tyins ← liftExcept (tryfind (fun vty => type_match vty nty []) rtys)
  let cjs' ← liftExcept (do (← chop_list k.toNat cjs).1.mapM (fun c => do return inst tyins (← rand c)))
  let mtys := itlist (fun c acc => insert (type_of c) acc) cjs' []
  let pcons := mtys.map (fun ty => cjs'.filter (fun t => type_of t == ty))
  let cls' ← liftExcept (do zip mtys (← pcons.mapM (fun l => l.mapM (recover_clause id))))
  let tyal ← liftExcept (mtys.mapM (fun ty => do
    return (mk_vartype ((← dest_type ty).1 ++ id), ty)))
  let cls'' ← liftM (cls'.mapM (fun (ty, l) => do
    let l' ← l.mapM (modify_item tyal)
    return (← modify_type tyal ty, l')) : IO _)
  return (k, tyal, cls'', ← INST_TYPE tyins ith, ← INST_TYPE tyins rth)

/-- `define_type_nested def` (ind_types.ml 1313-1381). -/
partial def define_type_nested [HolBase] (R : DefTypeRaw3)
    (def_ : List (hol_type × List (String × List hol_type))) : ExceptT String IO (Int × thm × thm) := do
  let n : Int := (itlist (· ++ ·) (def_.map (fun cl => cl.2.map Prod.fst)) []).length
  let newtys := def_.map Prod.fst
  let utys := unions (itlist (fun (cl : hol_type × List (String × List hol_type)) acc =>
    union (cl.2.map Prod.snd) acc) def_ [])
  let rectys := utys.filter (is_nested newtys)
  if rectys == [] then
    let (th1, th2) ← define_type_basecase R def_
    return (n, th1, th2)
  let nty ← liftExcept (hd (sort (fun t1 t2 => occurs_in t2 t1) rectys))
  let (k, tyal, ncls, ith, rth) ← create_auxiliary_clauses R nty
  let cls := (← liftM (def_.mapM (modify_clause tyal) : IO _)) ++ ncls
  let (_, ith1, rth1) ← define_type_nested R cls
  let xnewtys ← liftExcept ((strip_exists (strip_forall (concl rth1)).2).1.mapM (fun e => do
    hd (← dest_type (type_of e)).2))
  let xtyal ← liftExcept ((cls.map Prod.fst).mapM (fun ty => do
    let s ← dest_vartype ty
    return (← Lib.find (fun t => match dest_type t with
      | .ok (tn, _) => tn == s
      | .error _ => false) xnewtys, ty)))
  let ith0 ← INST_TYPE xtyal ith
  let rth0 ← INST_TYPE xtyal rth
  let (isoth, rclauses) ← prove_inductive_types_isomorphic R n.toNat k.toNat (ith0, rth0) (ith1, rth1)
  let irth3 ← CONJ ith1 rth1
  let vtylist := itlist (fun v acc => insert (type_of v) acc) (← liftExcept (variables (concl irth3))) []
  let isoths := CONJUNCTS isoth
  let isotys ← liftExcept (isoths.mapM (fun th => do
    hd (← dest_type (type_of (← lhand (concl th)))).2))
  let ctylist := vtylist.filter (fun ty => exists' (fun t => occurs_in t ty) isotys)
  let atylist := itlist (fun ty acc => union (striplist dest_fun_ty ty) acc) ctylist []
  let isoths' ← (atylist.filter (fun ty => exists' (fun t => occurs_in t ty) isotys)).mapM
    (lift_type_bijections R isoths)
  let cisoths ← ctylist.mapM (fun ty => do BETA_RULE (← lift_type_bijections R isoths' ty))
  let uisoths ← cisoths.mapM (MATCH_MP R.ISO_USAGE)
  let visoths ← uisoths.mapM (fun th => ASSUME (concl th))
  let funEqConv ← ExceptT.mk (Simp.GENERAL_REWRITE_CONV HolBase.B true Simp.topDepthConvIO
    R.funEqNet visoths)
  let irth4 ← uisoths.foldrM PROVE_HYP (← CONV_RULE funEqConv irth3)
  let irth5 ← REWRITE_RULE (rclauses :: (← isoths'.mapM (CONV_RULE (REWR_CONV R.ISO)))) irth4
  let irth6 ← repeatRule SCRUB_ASSUMPTION irth5
  let ncjs ← liftExcept ((conjuncts (strip_exists (strip_forall (← rand (concl irth6))).2).2).filterM
    (fun t => do
      return exists' (fun v => !(is_var v)) (strip_comb (← rand (← lhs (strip_forall t).2))).2))
  let mk_newcon (tm : term) : ExceptT String IO thm := do
    let (vs, bod) := strip_forall tm
    let rdeb ← liftExcept (do rand (← lhs bod))
    let rdef ← liftExcept (list_mk_abs vs rdeb)
    let newname := (← liftExcept (dest_var (← liftM (genvar bool_ty : IO term)))).1
    let deftm ← liftExcept (mkEq (mk_var newname (type_of rdef)) rdef)
    let dth ← ExceptT.mk (R.D2.D.new_definition deftm)
    GSYM (← CONV_RULE R.simpleBetaConv dth)
  let dths ← ncjs.mapM mk_newcon
  let (ith6, rth6) ← CONJ_PAIR (← PURE_REWRITE_RULE dths irth6)
  return (n, ith6, rth6)

/-- `define_type_raw def`, the third and final of ind_types.ml's three
    (1382-1387).  Adds the new types to the store and extends the rectype
    net, through `R.addEntries`. -/
def define_type_raw3 [HolBase] (R : DefTypeRaw3)
    (def_ : List (hol_type × List (String × List hol_type))) : ExceptT String IO (thm × thm) := do
  let newtys := def_.map Prod.fst
  let truecons := itlist (· ++ ·) (def_.map (fun cl => cl.2.map Prod.fst)) []
  let (p, ith0, rth0) ← define_type_nested R def_
  let (avs, etm) := strip_forall (concl rth0)
  let allcls := conjuncts (strip_exists etm).2
  let relcls := (← liftExcept (chop_list truecons.length allcls)).1
  let gencons ← liftExcept (relcls.mapM (fun c => do
    return repeat' rator (← rand (← lhand (strip_forall c).2))))
  let cdefs ← map2M (fun s r => do
    SYM (← ExceptT.mk (R.D2.D.new_definition (← liftExcept (mkEq (mk_var s (type_of r)) r)))))
    truecons gencons
  let tavs ← liftExcept (make_args "f" [] (avs.map type_of))
  let ith1 ← SUBS cdefs ith0
  let rth1 ← GENL tavs (← SUBS cdefs (← SPECL tavs rth0))
  let retval := (p, ith1, rth1)
  let newentries ← liftExcept (newtys.mapM (fun s => do return (← dest_vartype s, retval)))
  ExceptT.mk (R.addEntries newentries)
  return (ith1, rth1)

/- ---------------------------------------------------------------------- -/
/- The overall function, with rather crude string-based benignity.        -/
/- ---------------------------------------------------------------------- -/

/-- `define_type s` (ind_types.ml 1396-1414).  `store` is the contents of
    `the_inductive_types`; returns the result and the new contents. -/
def define_type [HolBase] (R : DefTypeRaw3) (store : List (String × (thm × thm))) (s : String) :
    ExceptT String IO ((thm × thm) × List (String × (thm × thm))) := do
  match Lib.assoc s store with
  | .ok retval =>
    HolCore.Lib.warn true "Benign redefinition of inductive type"
    return (retval, store)
  | .error _ =>
    let defspec ← ExceptT.mk (parse_inductive_type_specification s)
    let newtypes := defspec.map Prod.fst
    let constructors := itlist (fun (cl : List (String × List hol_type)) acc =>
      cl.map Prod.fst ++ acc) (defspec.map Prod.snd) []
    if (setify newtypes).length != newtypes.length then
      throw "define_type: multiple definitions of a type"
    if (setify constructors).length != constructors.length then
      throw "define_type: multiple instances of a constructor"
    let canArity (ty : hol_type) : IO Bool := do
      match dest_vartype ty with
      | .error _ => pure false
      | .ok nm => return (← get_type_arity nm).toBool
    if let some ty ← liftM (newtypes.findM? canArity : IO _) then
      throw ("define_type: type :" ++ (← liftExcept (dest_vartype ty)) ++ " already defined")
    let canConst (t : String) : IO Bool := do return (← get_const_type t).toBool
    if let some t ← liftM (constructors.findM? canConst : IO _) then
      throw ("define_type: constant " ++ t ++ " already defined")
    let retval ← define_type_raw3 R defspec
    return (retval, (s, retval) :: store)

/- ---------------------------------------------------------------------- -/
/- Unwinding, and application of patterns (ind_types.ml 1421-1572).      -/
/- ---------------------------------------------------------------------- -/

/-- `INSIDE_EXISTS_CONV conv tm` (ind_types.ml 1455-1457). -/
partial def INSIDE_EXISTS_CONV [HolBase] (conv : ioconv) : ioconv := fun tm =>
  if is_exists tm then BINDER_CONV (INSIDE_EXISTS_CONV conv) tm else conv tm

/-- The `conv bc tm` of `PUSH_EXISTS_CONV` and `PUSH_FORALL_CONV`
    (ind_types.ml 1458-1463, 1541-1545). -/
partial def pushQuantConv [HolBase] (econv : ioconv) (bc : ioconv) : ioconv := fun tm => do
  match ← (econv THENC BINDER_CONV (pushQuantConv econv bc)) tm with
  | .ok th => return .ok th
  | .error _ => bc tm

/-- The `UNWIND_CONV tm` of ind_types.ml 1468-1487, given `PUSH_EXISTS_CONV`
    and `baseconv`. -/
partial def unwindConv [HolBase] (PUSH_EXISTS_CONV : ioconv → ioconv) (baseconv : ioconv) :
    ioconv := fun tm => ExceptT.run do
  let (evs, bod) := strip_exists tm
  let eqs := conjuncts bod
  tryWith (do
      let eq ← liftExcept (Lib.find (fun tm => is_eq tm &&
        (match dest_eq tm with
         | .ok (l, r) => (mem l evs && !(free_in l r)) || (mem r evs && !(free_in r l))
         | .error _ => false)) eqs)
      let (l, r) ← liftExcept (dest_eq eq)
      let v := if mem l evs && !(free_in l r) then l else r
      let cjs' := eq :: subtract eqs [eq]
      let n := evs.length - (1 + (← liftExcept (Lib.index v evs.reverse)))
      let th1 ← CONJ_ACI_RULE (← liftExcept (do mkEq bod (← list_mk_conj cjs')))
      let th2 ← evs.foldrM MK_EXISTS th1
      let th3 ← ExceptT.mk (funpow n BINDER_CONV (PUSH_EXISTS_CONV baseconv)
        (← liftExcept (rand (concl th2))))
      CONV_RULE (RAND_CONV (unwindConv PUSH_EXISTS_CONV baseconv)) (← TRANS th2 th3))
    (pure (REFL tm))

/-- `UNWIND_CONV,MATCH_CONV` (ind_types.ml 1421-1539).  Every rewrite
    conversion is built once.  `!basic_rectype_net` is read through
    `rectypeNetIO` at each application of `BREAK_CONS_CONV`.  Performs the
    `do_list extend_basic_convs [...]` and returns the pair. -/
@[nospecialize]
def setupUnwindMatch [HolBase]
    (MATCH SEQPATTERN FUNCTION UNGUARDED_PATTERN GUARDED_PATTERN GEQ_DEF COND_ID
     COND_CLAUSES CONJ_ASSOC : thm)
    (MESON_TAC : List thm → tactic)
    (rectypeNetIO : IO (HolCore.Nets.net Simp.gconv))
    (extend_basic_convs : String → term × ioconv → IO (Except String Unit)) :
    ExceptT String IO (ioconv × ioconv) := do
  let { SWAP_EXISTS_THM, AND_CLAUSES, OR_CLAUSES, UNWIND_THM1, UNWIND_THM2, EXISTS_REFL,
        EQ_REFL, EXISTS_SIMP, .. } := HolBase.T
  let pth_0 ← prove
   r"(if ?!x. x = a /\ p then @x. x = a /\ p else @x. F) =
     (if p then a else @x. F)"
   (BOOL_CASES_TAC (← q r"p:bool") THEN ASM_REWRITE_TAC [COND_ID] THEN
    MESON_TAC [])
  let pth_1 ← prove
   r"_MATCH x (_SEQPATTERN r s) =
     (if ?y. r x y then _MATCH x r else _MATCH x s) /\
    _FUNCTION (_SEQPATTERN r s) x =
     (if ?y. r x y then _FUNCTION r x else _FUNCTION s x)"
   (REWRITE_TAC [MATCH, SEQPATTERN, FUNCTION] THEN
    MESON_TAC [])
  let pth_2 ← prove
   r"((?y. _UNGUARDED_PATTERN (GEQ s t) (GEQ u y)) <=> s = t) /\
     ((?y. _GUARDED_PATTERN (GEQ s t) p (GEQ u y)) <=> s = t /\ p)"
   (REWRITE_TAC [UNGUARDED_PATTERN, GUARDED_PATTERN, GEQ_DEF] THEN
    MESON_TAC [])
  let pth_3 ← prove
   r"(_MATCH x (\y z. P y z) = if ?!z. P x z then @z. P x z else @x. F) /\
     (_FUNCTION (\y z. P y z) x = if ?!z. P x z then @z. P x z else @x. F)"
   (REWRITE_TAC [MATCH, FUNCTION])
  let pth_4 ← prove
   r"(_UNGUARDED_PATTERN (GEQ s t) (GEQ u y) <=> y = u /\ s = t) /\
     (_GUARDED_PATTERN (GEQ s t) p (GEQ u y) <=> y = u /\ s = t /\ p)"
   (REWRITE_TAC [UNGUARDED_PATTERN, GUARDED_PATTERN, GEQ_DEF] THEN
    MESON_TAC [])
  let pth_5 ← prove
   r"(if ?!z. z = k then @z. z = k else @x. F) = k"
   (MESON_TAC [])
  let PUSH_EXISTS_CONV := pushQuantConv (REWR_CONV SWAP_EXISTS_THM)
  let conv2 := (← GEN_REWRITE_CONV_NET DEPTH_CONV [AND_CLAUSES, OR_CLAUSES]) THENC
               (← ASSOC_CONV CONJ_ASSOC)
  let BREAK_CONS_CONV : ioconv := fun tm => do
    let conv0 := TOP_SWEEP_CONV (REWRITES_CONV (← rectypeNetIO))
    let conv1 := if is_conj tm then LAND_CONV conv0 else conv0
    (conv1 THENC conv2) tm
  let baseconv ← GEN_REWRITE_CONV_NET id
    [UNWIND_THM1, UNWIND_THM2,
     ← EQT_INTRO (← SPEC_ALL EXISTS_REFL),
     ← EQT_INTRO (← GSYM (← SPEC_ALL EXISTS_REFL))]
  let UNWIND_CONV := unwindConv PUSH_EXISTS_CONV baseconv
  let eqAndConv ← GEN_REWRITE_CONV_NET DEPTH_CONV [← EQT_INTRO (← SPEC_ALL EQ_REFL), AND_CLAUSES]
  let existsSimpConv ← GEN_REWRITE_CONV_NET DEPTH_CONV [EXISTS_SIMP]
  let MATCH_SEQPATTERN_CONV :=
    (← GEN_REWRITE_CONV_NET id [pth_1]) THENC
    RATOR_CONV (LAND_CONV
     (BINDER_CONV (RATOR_CONV BETA_CONV THENC BETA_CONV) THENC
      PUSH_EXISTS_CONV ((← GEN_REWRITE_CONV_NET id [pth_2]) THENC BREAK_CONS_CONV) THENC
      UNWIND_CONV THENC
      eqAndConv THENC
      existsSimpConv))
  let pth3Conv ← GEN_REWRITE_CONV_NET id [pth_3]
  let pth4Conv ← GEN_REWRITE_CONV_NET id [pth_4]
  let MATCH_ONEPATTERN_CONV : ioconv := fun tm => ExceptT.run do
    let th1 ← ExceptT.mk (pth3Conv tm)
    let tm' ← liftExcept (do body (← rand (← lhand (← rand (concl th1)))))
    let th2 ← ExceptT.mk ((INSIDE_EXISTS_CONV (pth4Conv THENC RAND_CONV BREAK_CONS_CONV) THENC
                UNWIND_CONV THENC
                eqAndConv THENC
                existsSimpConv) tm')
    let l2 ← liftExcept (lhand (concl th2))
    let conv : ioconv := fun tm => pure (if tm == l2 then .ok th2 else .error "MATCH_ONEPATTERN_CONV")
    CONV_RULE
      (RAND_CONV (RATOR_CONV
        (COMB2_CONV (RAND_CONV (BINDER_CONV conv)) (BINDER_CONV conv))))
      th1
  let MATCH_SEQPATTERN_CONV_TRIV := MATCH_SEQPATTERN_CONV THENC
    (← GEN_REWRITE_CONV_NET id [COND_CLAUSES])
  let MATCH_SEQPATTERN_CONV_GEN := MATCH_SEQPATTERN_CONV THENC
    (← GEN_REWRITE_CONV_NET TRY_CONV [COND_CLAUSES])
  let MATCH_ONEPATTERN_CONV_TRIV := MATCH_ONEPATTERN_CONV THENC
    (← GEN_REWRITE_CONV_NET id [pth_5])
  let MATCH_ONEPATTERN_CONV_GEN := MATCH_ONEPATTERN_CONV THENC
    (← GEN_REWRITE_CONV_NET TRY_CONV [pth_0, pth_5])
  -- The list's quotations are parsed last first, as OCaml builds a list.
  let p4 ← q r"_FUNCTION (\y z. P y z) x"
  let p3 ← q r"_MATCH x (\y z. P y z)"
  let p2 ← q r"_FUNCTION (_SEQPATTERN r s) x"
  let p1 ← q r"_MATCH x (_SEQPATTERN r s)"
  ExceptT.mk (extend_basic_convs "MATCH_SEQPATTERN_CONV" (p1, MATCH_SEQPATTERN_CONV_TRIV))
  ExceptT.mk (extend_basic_convs "FUN_SEQPATTERN_CONV" (p2, MATCH_SEQPATTERN_CONV_TRIV))
  ExceptT.mk (extend_basic_convs "MATCH_ONEPATTERN_CONV" (p3, MATCH_ONEPATTERN_CONV_TRIV))
  ExceptT.mk (extend_basic_convs "FUN_ONEPATTERN_CONV" (p4, MATCH_ONEPATTERN_CONV_TRIV))
  return (CHANGED_CONV UNWIND_CONV, MATCH_SEQPATTERN_CONV_GEN ORELSEC MATCH_ONEPATTERN_CONV_GEN)

/-- The `FORALL_UNWIND_CONV tm` of ind_types.ml 1550-1570, given
    `PUSH_FORALL_CONV` and `baseconv`. -/
partial def forallUnwindConv [HolBase] (PUSH_FORALL_CONV : ioconv → ioconv) (baseconv : ioconv) :
    ioconv := fun tm => ExceptT.run do
  tryWith (do
      let (avs, bod) := strip_forall tm
      let (ant, con) ← liftExcept (dest_imp bod)
      let eqs := conjuncts ant
      let eq ← liftExcept (Lib.find (fun tm => is_eq tm &&
        (match dest_eq tm with
         | .ok (l, r) => (mem l avs && !(free_in l r)) || (mem r avs && !(free_in r l))
         | .error _ => false)) eqs)
      let (l, r) ← liftExcept (dest_eq eq)
      let v := if mem l avs && !(free_in l r) then l else r
      let cjs' := eq :: subtract eqs [eq]
      let n := avs.length - (1 + (← liftExcept (Lib.index v avs.reverse)))
      let th1 ← CONJ_ACI_RULE (← liftExcept (do mkEq ant (← list_mk_conj cjs')))
      let th2 ← AP_THM (← AP_TERM (← liftExcept (do rator (← rator bod))) th1) con
      let th3 ← avs.foldrM MK_FORALL th2
      let th4 ← ExceptT.mk (funpow n BINDER_CONV (PUSH_FORALL_CONV baseconv)
        (← liftExcept (rand (concl th3))))
      CONV_RULE (RAND_CONV (forallUnwindConv PUSH_FORALL_CONV baseconv)) (← TRANS th3 th4))
    (pure (REFL tm))

/-- `FORALL_UNWIND_CONV` (ind_types.ml 1540-1572).  OCaml evaluates the
    list of `MESON[]` lemmas last element first. -/
@[nospecialize]
def setupForallUnwind [HolBase] (MESON : List thm → term → IO (Except String thm)) :
    ExceptT String IO ioconv := do
  let PUSH_FORALL_CONV := pushQuantConv (REWR_CONV HolBase.T.SWAP_FORALL_THM)
  let m4 ← ExceptT.mk (MESON [] (← q r"(!x. a = x ==> q x) <=> q a"))
  let m3 ← ExceptT.mk (MESON [] (← q r"(!x. x = a ==> q x) <=> q a"))
  let m2 ← ExceptT.mk (MESON [] (← q r"(!x. a = x /\ p x ==> q x) <=> (p a ==> q a)"))
  let m1 ← ExceptT.mk (MESON [] (← q r"(!x. x = a /\ p x ==> q x) <=> (p a ==> q a)"))
  let baseconv ← GEN_REWRITE_CONV_NET id [m1, m2, m3, m4]
  return forallUnwindConv PUSH_FORALL_CONV baseconv

end

end HolMath.IndTypes
