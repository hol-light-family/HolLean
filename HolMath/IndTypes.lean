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
        REWRITE_TAC [(← ITAUT (← q r"(a ==> a /\ b) <=> (a ==> b)"))] THEN
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
  numty : hol_type
  /-- `mk_small_numeral`'s constants (nums.ml). -/
  numK : HolMath.Nums.NumeralConsts
  NUM_LT_CONV : ioconv
  /-- `GEN_REWRITE_CONV I [COND_CLAUSES]` (ind_types.ml 735). -/
  COND_CONV : ioconv
  /-- `(<):num->num->bool` (ind_types.ml 734). -/
  lt_tm : term

instance : Inhabited DefTypeRaw :=
  ⟨⟨default, default, default, default, default, default,
    fun _ => pure (.error ""), fun _ => pure (.error ""), fun _ => pure (.error ""),
    fun _ => pure (.error ""), fun _ _ _ _ => pure (.error ""),
    default, default, default, default, default, default, default,
    fun _ => pure (.error ""), fun _ => pure (.error ""), default⟩⟩

/-- Build the `DefTypeRaw` (ind_types.ml 308-310, 330, 687, 734-735). -/
@[nospecialize]
def setupDefTypeRaw [HolBase] (FST SND FCONS BETA_THM CONSTR_REC eepth COND_CLAUSES : thm)
    (numK : HolMath.Nums.NumeralConsts) (NUM_LT_CONV : ioconv)
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
  let numty ← qty r"num"
  let lt_tm ← q r"(<):num->num->bool"
  let COND_CONV ← GEN_REWRITE_CONV_NET id [COND_CLAUSES]
  return { FST, SND, FCONS, BETA_THM, CONSTR_REC, eepth, mk_pair,
           derive_nonschematic_inductive_relations, prove_monotonicity_hyps,
           new_definition, new_basic_type_definition,
           zero_tm, suc_tm, t_tm, n_tm, beps_tm, numty, numK, NUM_LT_CONV, COND_CONV, lt_tm }

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
/- Eliminate local "definitions" v1 = t1, ..., vn = tn in hyps, with no vi -/
/- free in any tj, by a single instantiation, and check that the hyps left -/
/- are "hs". This applies to the definitions of the representing          -/
/- predicates and then to the definitions of the pseudo-constructors.     -/
/- ---------------------------------------------------------------------- -/

/-- `SCRUB_EQUATIONS eqs hs th` (ind_types.ml 319-323). -/
def SCRUB_EQUATIONS [HolBase] (eqs hs : List term) (th : thm) : ExceptT String IO thm := do
  let theta ← liftExcept (eqs.mapM (fun eq => do let (l, r) ← dest_eq eq; pure (r, l)))
  let th1 ← INST theta (← eqs.foldrM DISCH th)
  let th2 ← theta.foldlM (fun th (r, _) => MP th (REFL r)) th1
  if set_eq (hyp th2) hs then return th2 else throw "SCRUB_EQUATIONS"

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
    let condef ← liftExcept (do
      list_mk_comb constr [← HolMath.Nums.mk_small_numeral D.numK (Int.ofNat n), iarg, rarg])
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
/- The rules have the predicate definitions as hypotheses, which mention  -/
/- all the pseudo-constructors, so we avoid finding their free variables  -/
/- for every rule (as SPEC_ALL and MATCH_MP would do).                    -/
/- ---------------------------------------------------------------------- -/

/-- `SPEC_ALL_RULE` of `prove_model_inhabitation` (ind_types.ml 407-410). -/
partial def specAllRule [HolBase] (hvs : List term) (th : thm) : ExceptT String IO thm := do
  if !(is_forall (concl th)) then return th
  let v ← liftExcept (do bndvar (← rand (concl th)))
  specAllRule hvs (← SPEC (← liftExcept (variant (hvs ++ frees (concl th)) v)) th)

/-- `prove_model_inhabitation rth` (ind_types.ml 407-437). -/
partial def prove_model_inhabitation [HolBase] (rth : thm) : ExceptT String IO (List thm) := do
  let hvs := freesl (hyp rth)
  let srules ← (CONJUNCTS rth).mapM (specAllRule hvs)
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
      let ath ← end_itlist CONJ asms
      MP (← INSTANTIATE (← term_match [] (← liftExcept (lhand (concl thm0))) (concl ath)) thm0) ath
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
  let ceqs := cdefs.map concl
  let th4 ← (do
    let peqs := subtract (hyp th3) ceqs
    SCRUB_EQUATIONS ceqs [] (← SCRUB_EQUATIONS peqs ceqs th3))
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

/-- `RULE_INSTANCE rthm pat` (ind_types.ml 512-517): instantiate a rule
    `!x1 .. xn. [A ==>] P (c x1 .. xn)` to the pattern `c t1 .. tn`.  This is
    done once per clause on theorems with all the predicate definitions as
    hypotheses, so it uses SPECL rather than matching. -/
def RULE_INSTANCE [HolBase] (rthm : thm) (pat : term) : ExceptT String IO thm := do
  let (avs, bod) := strip_forall (concl rthm)
  let cpat ← liftExcept (rand (← if is_imp bod then rand bod else pure bod))
  if (strip_comb cpat).2 == avs && repeat' rator cpat == repeat' rator pat then
    SPECL (strip_comb pat).2 rthm
  else throw "RULE_INSTANCE"

/-- `quantified_tybijs tybijpairs` (ind_types.ml 526-531): the quantified
    forms `!r. P r <=> dest(mk r) = r` and `!a. P(dest a)` of the type
    bijections, keyed by the type predicate (a variable), so that instances
    are obtained by SPEC instead of rewriting. -/
def quantified_tybijs [HolBase] (tybijpairs : List (thm × thm)) :
    ExceptT String IO (List (term × (thm × thm))) :=
  tybijpairs.mapM (fun (th1, th2) => do
    let l ← liftExcept (lhand (concl th2))
    let rl ← liftExcept (rand l)
    let th3 ← INST [((← liftExcept (do rand (← lhand (concl th1)))), rl)] th2
    let th4 ← AP_TERM (← liftExcept (do rator (← lhand (← rand (concl th2))))) th1
    let q2 ← GEN (← liftExcept (rand (concl th1))) (← EQ_MP (← SYM th3) th4)
    let q1 ← GEN rl th2
    return (← liftExcept (rator l), (q1, q2)))

/-- `TYBIJ_RULE qbijs th` (ind_types.ml 533-535). -/
def TYBIJ_RULE [HolBase] (qbijs : List (term × (thm × thm))) (th : thm) :
    ExceptT String IO thm := do
  let (p, x) ← liftExcept (dest_comb (concl th))
  EQ_MP (← SPEC x (← liftExcept (Lib.assoc p qbijs)).1) th

/-- `pullback_induction_clause tybijpairs conthms` (ind_types.ml 543-586):
    builds `PRERULE` and `IPRULE` once and returns `fun rthm tm -> ...`. -/
def pullback_induction_clause [HolBase] (tybijpairs : List (thm × thm)) (conthms : List thm) :
    ExceptT String IO (thm → term → ExceptT String IO thm) := do
  let PRERULE := CONV_RULE (← GEN_REWRITE_CONV_NET (funpow 3 RAND_CONV) (← conthms.mapM SYM))
  let qbijs ← quantified_tybijs tybijpairs
  let IPRULE (th : thm) : ExceptT String IO thm := do SYM (← TYBIJ_RULE qbijs th)
  return fun rthm tm => do
    let (avs, bimp) := strip_forall tm
    if is_imp bimp then
      let (ant, con) ← liftExcept (dest_imp bimp)
      let ths ← (CONJUNCTS (← ASSUME ant)).mapM (CONV_RULE BETA_CONV)
      let (tths, pths) := unzip (← ths.mapM CONJ_PAIR)
      let tth ← MP (← SPECL avs rthm) (← end_itlist CONJ tths)
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
      let tth ← (do
        let th ← SPECL avs rthm
        if concl th == (← liftExcept (do lhand (← rand (concl conth2)))) then pure th
        else throw "pullback_induction_clause")
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
  let ceqs := subtract (hyp th4) pasms
  SCRUB_EQUATIONS ceqs [] (← SCRUB_EQUATIONS pasms ceqs th4)

/-- `range_tyvar consindex` (ind_types.ml 632-636): `Z`, with primes added if
    this is the name of a type variable of the new types. -/
partial def range_tyvar (consindex : List (term × (term × term))) : hol_type :=
  let tvs := itlist (fun (ci : term × (term × term)) acc =>
    union (tyvars (type_of ci.2.1)) acc) consindex []
  let rec fresh (s : String) : hol_type :=
    if mem (mk_vartype s) tvs then fresh (s ++ "'") else mk_vartype s
  fresh "Z"

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
  let ranty := range_tyvar consindex
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
  let qbijs ← quantified_tybijs tybijpairs
  let ERULE := TYBIJ_RULE qbijs
  let SRULE (t : term) : ExceptT String IO thm := do
    let (p, x) ← liftExcept (dest_comb t)
    SPEC (← liftExcept (rand x)) (← liftExcept (Lib.assoc p qbijs)).2
  let simplify_fxthm (rthm fxth : thm) : ExceptT String IO thm := do
    let pat ← liftExcept (funpowM 4 rand (concl fxth))
    if is_imp (repeat' (fun t => (dest_forall t).map Prod.snd) (concl rthm)) then
      let th1 ← RULE_INSTANCE rthm pat
      let tms1 := conjuncts (← liftExcept (lhand (concl th1)))
      let ths2 ← tms1.mapM SRULE
      ERULE (← MP th1 (← end_itlist CONJ ths2))
    else
      ERULE (← RULE_INSTANCE rthm pat)
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
  let rest := subtract (hyp fxth5) pasms
  SCRUB_EQUATIONS (subtract rest eqs) eqs (← SCRUB_EQUATIONS pasms rest fxth5)

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
  let zty := range_tyvar consindex
  let s := mk_var "s" (← mkFunTy D.numty zty)
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
    let sargs' ← liftExcept (indices.mapM (mk_comb s))
    let allargs := cargs' ++ rargs' ++ sargs'
    let funty ← allargs.foldrM (fun a acc => mkFunTy (type_of a) acc) zty
    let funname := (← liftExcept (do dest_const (repeat' rator (← lhand (concl cth))))).1 ++ "'"
    let funarg := mk_var funname funty
    liftExcept (do list_mk_abs [i, r, s] (← list_mk_comb funarg allargs))

/- ---------------------------------------------------------------------- -/
/- Derive the recursion theorem. The function used in CONSTR_REC, mapping -/
/- the k'th constructor number to the k'th function, is a balanced tree   -/
/- of conditionals "if c < m then .. else ..", so evaluating it at numeral -/
/- k takes logarithmically many steps. It is only substituted for a       -/
/- variable at the end, so that the clauses never contain the whole tree. -/
/- ---------------------------------------------------------------------- -/

/-- `TREE_CONV` of `derive_recursion_theorem` (ind_types.ml 736-742). -/
partial def TREE_CONV [HolBase] (D : DefTypeRaw) (tm : term) : ExceptT String IO thm := do
  let th1 ← liftExcept (Equal.BETA_CONV tm)
  let r ← liftExcept (rand (concl th1))
  if !(HolCore.Classic.is_cond r) then return th1
  let th2 ← TRANS th1 (← ExceptT.mk (RATOR_CONV (RATOR_CONV (RAND_CONV D.NUM_LT_CONV)) r))
  let th3 ← TRANS th2 (← ExceptT.mk (D.COND_CONV (← liftExcept (rand (concl th2)))))
  TRANS th3 (← TREE_CONV D (← liftExcept (rand (concl th3))))

/-- The `tree k fs` of `mk_tree` (ind_types.ml 745-751). -/
partial def mkTreeAux (D : DefTypeRaw) (c : term) (k : Nat) (fs : List term) :
    ExceptT String IO term := do
  let n := fs.length
  if n == 1 then return ← liftExcept (do mk_abs c (← hd fs))
  let (fs1, fs2) ← liftExcept (chop_list (n / 2) fs)
  let m := k + n / 2
  -- OCaml evaluates mk_cond's arguments right to left
  let e2 ← mkTreeAux D c m fs2
  let e1 ← mkTreeAux D c k fs1
  let cond ← ExceptT.mk (HolCore.Classic.mk_cond
    (← liftExcept (list_mk_comb D.lt_tm [c, ← HolMath.Nums.mk_small_numeral D.numK (Int.ofNat m)]))
    (← liftExcept (mk_comb e1 c)) (← liftExcept (mk_comb e2 c)))
  liftExcept (mk_abs c cond)

/-- `mk_tree fs` (ind_types.ml 743-752). -/
def mk_tree (D : DefTypeRaw) (fs : List term) : ExceptT String IO term := do
  let c ← (genvar D.numty : IO term)
  mkTreeAux D c 0 fs

/-- `derive_recursion_theorem tybijpairs consindex conthms rath`
    (ind_types.ml 733-792). -/
def derive_recursion_theorem [HolBase] (D : DefTypeRaw) (tybijpairs : List (thm × thm))
    (consindex : List (term × (term × term))) (conthms : List thm) (rath : thm) :
    ExceptT String IO thm := do
  let isocons ← conthms.mapM (← create_recursion_iso_constructor D consindex)
  let nums ← liftExcept ((List.range isocons.length).mapM (fun k =>
    HolMath.Nums.mk_small_numeral D.numK (Int.ofNat k)))
  let gv ← (genvar (← mkFunTy D.numty (type_of (← liftExcept (hd isocons)))) : IO term)
  let gths ← map2M (fun k f => do ASSUME (← liftExcept (do mkEq (← mk_comb gv k) f))) nums isocons
  let eth ← ISPEC gv D.CONSTR_REC
  let fn ← liftExcept (do rator (← rand (← hd (conjuncts (concl rath)))))
  let betm ← liftExcept (do
    let (v, bod) ← dest_abs (← rand (concl eth))
    return (← vsubst [(fn, v)]) bod)
  let bth ← ASSUME betm
  let fnths ← (hyp rath).mapM (fun t => do
    RIGHT_BETAS [← liftExcept (do bndvar (← rand t))] (← ASSUME t))
  let SIMPER := CONV_RULE (← PURE_REWRITE_CONV_NET
    ((← fnths.mapM SYM) ++ tybijpairs.map Prod.fst ++ [D.FST, D.SND, D.FCONS, D.BETA_THM]))
  let hackdown_rath (th gth : thm) : ExceptT String IO thm := do
    let (ltm, rtm) ← liftExcept (dest_eq (concl th))
    let wargs := (strip_comb (← liftExcept (rand ltm))).2
    let th1 ← TRANS th (← SPECL (strip_comb (← liftExcept (rand rtm))).2 bth)
    let gl ← liftExcept (lhs (concl gth))
    let GCONV : ioconv := fun tm =>
      pure (if aconv tm gl then .ok gth else failwith "derive_recursion_theorem")
    let th2 ← TRANS th1 (← ExceptT.mk (funpow 3 RATOR_CONV GCONV (← liftExcept (rand (concl th1)))))
    let th3 ← TRANS th2 (← ExceptT.mk
      (funpow 2 RATOR_CONV BETA_CONV (← liftExcept (rand (concl th2)))))
    let th4 ← TRANS th3 (← ExceptT.mk (RATOR_CONV BETA_CONV (← liftExcept (rand (concl th3)))))
    let th5 ← TRANS th4 (← liftExcept (do Equal.BETA_CONV (← rand (concl th4))))
    GENL wargs (← SIMPER th5)
  let rthm ← end_itlist CONJ (← map2M hackdown_rath (CONJUNCTS rath) gths)
  let unseqs := (hyp rthm).filter (fun t => is_eq t && !(free_in gv t))
  let tys ← liftExcept (consindex.mapM (fun (ci : term × (term × term)) => do
      hd (← dest_type (type_of ci.2.2)).2))
  let seqs ← liftExcept (tys.mapM (fun ty => Lib.find (fun t =>
      match (do hd (← dest_type (type_of (← lhand t))).2) with
      | .ok h => h == ty
      | .error _ => false) unseqs))
  let rethm ← liftExcept (seqs.foldrM (fun eq th => IndDefs.EXISTS_EQUATION HolBase.B D.eepth eq th) rthm)
  let fethm ← CHOOSE (fn, eth) rethm
  let bigfun ← mk_tree D isocons
  let fethm' ← nums.foldrM (fun k th => do
      PROVE_HYP (← TREE_CONV D (← liftExcept (mk_comb bigfun k))) th)
    (← INST [(bigfun, gv)] fethm)
  let pcons ← liftExcept ((conjuncts (concl rthm)).mapM (fun c => do
      return repeat' rator (← rand (repeat' (fun t => (dest_forall t).map Prod.snd) c))))
  GENL pcons fethm'

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

/-- A type variable named `s`, with primes added while it is among `tvs`. -/
partial def freshTyvar (tvs : List hol_type) (s : String) : hol_type :=
  if mem (mk_vartype s) tvs then freshTyvar tvs (s ++ "'") else mk_vartype s

/-- `generalize_recursion_theorem th` (ind_types.ml 822-874). -/
def generalize_recursion_theorem [HolBase] (D2 : DefTypeRaw2) (th : thm) :
    ExceptT String IO thm := do
  let (_avs, ebod) := strip_forall (concl th)
  let (evs, bod) := strip_exists ebod
  let n := evs.length
  if n == 1 then return th
  -- ind_types.ml 910-913: the names Z0, Z1, ... are chosen apart from the
  -- type variables of the recursion theorem's functions
  let tvs := itlist (fun e acc => union (tyvars (type_of e)) acc) evs []
  let tys := (List.range n).map (fun i => freshTyvar tvs ("Z" ++ toString i))
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
/- (ind_types.ml 982-1290.)  The fast methods instantiate the recursion   -/
/- theorem once, with the tuple of arguments injected into a sum type     -/
/- for injectivity, and with a numeral per constructor for distinctness.  -/
/- ---------------------------------------------------------------------- -/

/-- The `BETAS_CONV n` of `instantiate_recursion` (ind_types.ml 1010-1012):
    `n` beta-reductions of an `n`-fold application. -/
def betasConvN : Nat → Equal.conv
  | 0 => fun tm => .ok (REFL tm)
  | n + 1 => Equal.THENC (Equal.RATOR_CONV (betasConvN n)) Equal.BETA_CONV

/-- The `dest_clause` of `instantiate_recursion` (ind_types.ml 1013-1017). -/
def instDestClause (cl : term) : Except String (List term × term × term × List term) := do
  let (xs, eq) := strip_forall cl
  let (l, r) ← dest_eq eq
  let (f, ts) := strip_comb r
  return (xs, ← rator l, f, ts)

/-- The `CLAUSES_CONV k` of `instantiate_recursion` (ind_types.ml 1051-1057),
    with the `nargs`/`nvars` arrays as they are after `mk_inst`. -/
partial def instClausesConv (n : Nat) (nargs : Array Int) (nvars : Array Nat) (k : Nat) :
    Equal.conv := fun tm =>
  let conv : Equal.conv := fun tm =>
    if nargs[k]! < 0 then .ok (REFL tm)
    else funpow nvars[k]! Equal.BINDER_CONV (Equal.RAND_CONV (betasConvN nargs[k]!.toNat)) tm
  if k + 1 < n then Equal.COMB2_CONV (Equal.RAND_CONV conv) (instClausesConv n nargs nvars (k + 1)) tm
  else conv tm

/-- `instantiate_recursion ax vals` (ind_types.ml 1009-1058): instantiates
    the function variables of clause `k` of the recursion theorem `ax` to
    `\ys. v` for each `(k,v)` of `vals`, and the range types to match. -/
def instantiate_recursion [HolBase] (ax : thm) (vals : List (Nat × term)) : ExceptT String IO thm := do
  let (evs, bod) := strip_exists (strip_forall (concl ax)).2
  let cls := (← liftExcept ((conjuncts bod).mapM instDestClause)).toArray
  let n := cls.size
  let tyins ← liftExcept (vals.foldrM (fun (kv : Nat × term) acc => do
    let (k, v) := kv
    let (_, fn, _, _) := cls[k]!
    let rty := (← dest_fun_ty (type_of fn)).2
    let ty := type_of v
    match rev_assoc rty acc with
    | .ok ty' => if ty' == ty then return acc else throw "instantiate_recursion"
    | .error _ =>
      if ty == rty then return acc
      else if is_vartype rty then return (ty, rty) :: acc
      else throw "instantiate_recursion") [])
  let rtys := tyins.map Prod.snd
  let bad (c : List term × term × term × List term) : Except String Bool := do
    let (xs, fn, _, _) := c
    rtys.anyM (fun ty => do
      if xs.any (fun x => occurs_in ty (type_of x)) then return true
      return occurs_in ty (← dest_fun_ty (type_of fn)).1)
  if ← liftExcept (cls.toList.anyM bad) then throw "instantiate_recursion"
  let ax' ← INST_TYPE tyins ax
  let th1 ← SPECL (← liftExcept (variants (thm_frees ax') (strip_forall (concl ax')).1)) ax'
  let cls' := (← liftExcept ((conjuncts (strip_exists (concl th1)).2).mapM instDestClause)).toArray
  let mut nargs : Array Int := Array.replicate n (-1)
  let mut nvars : Array Nat := Array.replicate n 0
  let mut insts : Array (term × term) := #[]
  for (k, v) in vals do
    let (xs, _, f, ts) := cls'[k]!
    if nargs[k]! >= 0 then throw "instantiate_recursion"
    let ys ← ts.mapM (fun t => liftM (genvar (type_of t) : IO term))
    let tys ← liftExcept (zip ts ys)
    let theta ← liftExcept ((intersect (frees v) xs).mapM (fun x => do return (← assoc x tys, x)))
    nargs := nargs.set! k (Int.ofNat ts.length)
    nvars := nvars.set! k xs.length
    insts := insts.push ((← liftExcept (do list_mk_abs ys ((← vsubst theta) v))), f)
  let th2 ← INST insts.toList th1
  let cconv := funpow evs.length Equal.BINDER_CONV (instClausesConv n nargs nvars 0)
  CONV_RULE (fun tm => pure (cconv tm)) th2

/-- `constructor_head` (ind_types.ml 1061-1062): a numeral constructor is
    its own head. -/
def constructor_head (pat : term) : term :=
  if HolMath.Nums.is_numeral pat then pat else repeat' rator pat

/-- `constructor_args` (ind_types.ml 1063-1064). -/
def constructor_args (pat : term) : List term :=
  if HolMath.Nums.is_numeral pat then [] else (strip_comb pat).2

/-- `first_occurrences pats` (ind_types.ml 1065-1072): whether each pattern's
    constructor is a constant not seen in an earlier pattern. -/
def first_occurrences (pats : List term) : List Bool :=
  let rec firsts (seen : List String) : List term → List Bool
    | [] => []
    | p :: t =>
      let c := match dest_const (repeat' rator p) with
        | .ok (s, _) => s
        | .error _ => ""
      (c != "" && !(mem c seen)) :: firsts (c :: seen) t
  firsts [] pats

/-- `finish_injectivity atm qth` (ind_types.ml 1074-1078). -/
def finish_injectivity [HolBase] (atm : term) (qth : thm) : ExceptT String IO thm := do
  let qtm := concl qth
  let f := repeat' rator (← liftExcept (lhand atm))
  let rth ← (CONJUNCTS (← ASSUME qtm)).foldlM (fun acc th => MK_COMB (acc, th)) (REFL f)
  IMP_ANTISYM_RULE (← DISCH atm qth) (← DISCH qtm rth)

/-- `prove_injectivity_slow ax pat` (ind_types.ml 1079-1095). -/
def prove_injectivity_slow [HolBase] (BETA_THM : thm) (DEPAIR : thm → ExceptT String IO thm)
    (mk_pair : term × term → IO (Except String term)) (ax : thm) (pat : term) :
    ExceptT String IO thm := do
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
  let tth ← finish_injectivity atm (← DEPAIR pth)
  let uth ← GENL args (← GENL args' tth)
  PROVE_HYP eth (← SIMPLE_CHOOSE fn uth)

/-- `mk_injections tys` (ind_types.ml 1101-1109): the injections of the
    types `tys` into their balanced sum `mk_sum tys`. -/
partial def mk_injections (tys : List hol_type) :
    ExceptT String IO (List (term → Except String term)) := do
  let k := tys.length
  if k == 1 then return [fun t => .ok t]
  let (tys1, tys2) ← liftExcept (chop_list (k / 2) tys)
  let ty1 ← mk_sum tys1
  let ty2 ← mk_sum tys2
  let inl ← mkConst "INL" [(ty1, aty), (ty2, bty)]
  let inr ← mkConst "INR" [(ty1, aty), (ty2, bty)]
  let injs1 ← mk_injections tys1
  let injs2 ← mk_injections tys2
  return injs1.map (fun f t => do mk_comb inl (← f t)) ++
         injs2.map (fun f t => do mk_comb inr (← f t))

/-- `UNSUM_RULE th` (ind_types.ml 1111-1121): strips `INL`/`INR` from both
    sides of `|- INL s = INL t` etc. with `OUTL`/`OUTR`. -/
partial def unsumRule [HolBase] (OUT_CONV : ioconv) (th : thm) : ExceptT String IO thm :=
  tryWith (do
    let c ← liftExcept (do rator (← lhs (concl th)))
    let (cn, cty) ← liftExcept (dest_const c)
    let dn ← if cn == "INL" then pure "OUTL" else if cn == "INR" then pure "OUTR"
             else throw "UNSUM_RULE"
    let [ty1, ty2] := (← liftExcept (do dest_type (← dest_fun_ty cty).2)).2
      | throw "UNSUM_RULE"
    let d ← mkConst dn [(ty1, aty), (ty2, bty)]
    let th1 ← AP_TERM d th
    let (l, r) ← liftExcept (dest_eq (concl th1))
    let rth ← ExceptT.mk (OUT_CONV r)
    let lth ← ExceptT.mk (OUT_CONV l)
    unsumRule OUT_CONV (← TRANS (← TRANS (← SYM lth) th1) rth))
    (pure th)

/-- The clauses' left-hand sides `fn pat` of a recursion theorem, as pairs. -/
def recursionLefts (ax : thm) : Except String (List (term × term)) := do
  let cls := conjuncts (strip_exists (strip_forall (concl ax)).2).2
  cls.mapM (fun c => do dest_comb (← lhand (strip_forall c).2))

/-- `prove_injectivity_fast ax` (ind_types.ml 1122-1156). -/
def prove_injectivity_fast [HolBase] (DEPAIR : thm → ExceptT String IO thm) (OUT_CONV : ioconv)
    (mk_pair : term × term → IO (Except String term)) (ax : thm) : ExceptT String IO thm := do
  let lefts ← liftExcept (recursionLefts ax)
  let klefts := (((first_occurrences (lefts.map Prod.snd)).zip
      ((List.range lefts.length).zip lefts)).filter (fun (x : Bool × Nat × term × term) =>
        let args := constructor_args x.2.2.2
        x.1 && !args.isEmpty && args.all is_var)).map Prod.snd
  let tup (p : term) : ExceptT String IO term :=
    end_itlist (fun a b => ExceptT.mk (mk_pair (a, b))) (constructor_args p)
  let mk_vals (fn : term) : ExceptT String IO (List (Nat × term)) := do
    let kps := (klefts.filter (fun (x : Nat × term × term) => x.2.1 == fn)).map
      (fun x => (x.1, x.2.2))
    let tys := setify (← kps.mapM (fun kp => do return type_of (← tup kp.2)))
    let injs ← liftExcept (zip tys (← mk_injections tys))
    kps.mapM (fun (k, p) => do
      let tp ← tup p
      let inj ← liftExcept (assoc (type_of tp) injs)
      return (k, ← liftExcept (inj tp)))
  let vals0 ← (setify (klefts.map (fun x => x.2.1))).foldrM
    (fun fn acc => do return (← mk_vals fn) ++ acc) []
  let vals := sort (fun (a b : Nat × term) => a.1 < b.1) vals0
  let eth ← instantiate_recursion ax vals
  let (evs, bod) := strip_exists (concl eth)
  let cths := (CONJUNCTS (← ASSUME bod)).toArray
  let prove_injective (x : Nat × term × term) : ExceptT String IO (thm × List term × List term) := do
    let (k, _, pat) := x
    let args := constructor_args pat
    let args' ← liftExcept (variants args args)
    let atm ← liftExcept (do mkEq pat (← list_mk_comb (repeat' rator pat) args'))
    let cth1 ← SPECL args cths[k]!
    let cth2 ← SPECL args' cths[k]!
    let fn' ← liftExcept (do rator (← lhs (concl cth1)))
    let pth ← TRANS (← TRANS (← SYM cth1) (← AP_TERM fn' (← ASSUME atm))) cth2
    return (← finish_injectivity atm (← DEPAIR (← unsumRule OUT_CONV pth)), args, args')
  let tths ← klefts.mapM prove_injective
  let th ← PROVE_HYP eth (← evs.foldrM SIMPLE_CHOOSE (← end_itlist CONJ (tths.map (·.1))))
  end_itlist CONJ (← map2M (fun th (x : thm × List term × List term) => do
    GENL x.2.1 (← GENL x.2.2 th)) (CONJUNCTS th) tths)

/-- `prove_constructors_numbering ax` (ind_types.ml 1164-1183): the groups
    of (first-occurring, variable-argument) constructors of each type with at
    least two, with the recursion theorem instantiated to number them. -/
def prove_constructors_numbering [HolBase] (numK : HolMath.Nums.NumeralConsts) (ax : thm) :
    ExceptT String IO (thm × List term × List (List (term × thm))) := do
  let lefts ← liftExcept (recursionLefts ax)
  let fns := itlist (fun (p : term × term) acc => insert p.1 acc) lefts []
  let klefts := (first_occurrences (lefts.map Prod.snd)).zip
    ((List.range lefts.length).zip lefts)
  let ok (x : Bool × Nat × term × term) : Bool :=
    let p := x.2.2.2
    x.1 && (HolMath.Nums.is_numeral p || (strip_comb p).2.all is_var)
  let groups := fns.filterMap (fun f =>
    let g := klefts.filter (fun x => x.2.2.1 == f)
    if g.length < 2 || !(g.all ok) then none
    else some (g.map (fun x => (x.2.1, x.2.2.2))))
  if groups.isEmpty then throw "prove_constructors_numbering"
  let vals0 ← liftExcept (groups.foldrM (fun g acc => do
    let ns ← (g.zip (List.range g.length)).mapM (fun (x : (Nat × term) × Nat) => do
      return (x.1.1, ← HolMath.Nums.mk_small_numeral numK (Int.ofNat x.2)))
    return ns ++ acc) [])
  let vals := sort (fun (a b : Nat × term) => a.1 < b.1) vals0
  let eth ← instantiate_recursion ax vals
  let (evs, bod) := strip_exists (concl eth)
  let cths := (CONJUNCTS (← ASSUME bod)).toArray
  return (eth, evs, groups.map (fun g => g.map (fun (k, p) => (p, cths[k]!))))

/-- `DISTINCT_RULE thi thj tm` (ind_types.ml 1184-1187): from
    `|- f (C ..) = i` and `|- f (D ..) = j`, `|- ~(C .. = D ..)`. -/
def DISTINCT_RULE [HolBase] (NUM_EQ_CONV : ioconv) (thi thj : thm) (tm : term) :
    ExceptT String IO thm := do
  let fn ← liftExcept (do rator (← lhs (concl thi)))
  let th1 ← TRANS (← TRANS (← SYM thi) (← AP_TERM fn (← ASSUME tm))) thj
  NOT_INTRO (← DISCH tm (← EQ_MP (← ExceptT.mk (NUM_EQ_CONV (concl th1))) th1))

/-- `prove_distinctness_slow ax pat` (ind_types.ml 1188-1210), given
    `num_ty` and `NEGATE`'s tautology. -/
def prove_distinctness_slow [HolBase] (BETA_THM : thm) (numK : HolMath.Nums.NumeralConsts)
    (NUM_EQ_CONV : ioconv) (num_ty : hol_type) (negth : thm) (ax : thm) (pat : List term) :
    ExceptT String IO (List thm) := do
  let rec allopairs {α β : Type} (f : α → α → β) : List α → List α → List β
    | [], _ => []
    | _, [] => []
    | h :: t, _ :: m => m.map (f h) ++ allopairs f t m
  let NEGATE (th : thm) : ExceptT String IO thm := do GEN_ALL (← CONV_RULE (REWR_CONV negth) th)
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

/-- `prove_distinctness_fast ax` (ind_types.ml 1211-1228). -/
def prove_distinctness_fast [HolBase] (numK : HolMath.Nums.NumeralConsts) (NUM_EQ_CONV : ioconv)
    (ax : thm) : ExceptT String IO thm := do
  let (eth, evs, groups) ← prove_constructors_numbering numK ax
  let prove_group (g : List (term × thm)) : ExceptT String IO (List thm) := do
    let g' ← g.mapM (fun (p, th) => do
      let args := constructor_args p
      let args' ← liftExcept (variants args args)
      return (← SPECL args th, ← SPECL args' th, p,
              ← liftExcept (list_mk_comb (constructor_head p) args')))
    -- `map ... t @ pairs t`: OCaml evaluates `pairs t` first.
    let rec pairs : List (thm × thm × term × term) → ExceptT String IO (List thm)
      | [] => pure []
      | (thi, _, p, _) :: t => do
        let rest ← pairs t
        let here ← t.mapM (fun (_, thj, _, q) => do
          DISTINCT_RULE NUM_EQ_CONV thi thj (← liftExcept (mkEq p q)))
        return here ++ rest
    pairs g'
  let ths ← groups.foldrM (fun g acc => do return (← prove_group g) ++ acc) []
  let th ← PROVE_HYP eth (← evs.foldrM SIMPLE_CHOOSE (← end_itlist CONJ ths))
  end_itlist CONJ (← (CONJUNCTS th).mapM GEN_ALL)

/-- A constructor's argument variables `vs` renamed apart from `avoid`
    (the `fresh` of `constructors_distinct_convs`, ind_types.ml 1261-1267):
    names are compared regardless of type. -/
partial def freshArgVars (avoid : List term) : List term → Except String (List term)
  | [] => .ok []
  | v :: t => do
    let ty := type_of v
    let v' ← variant (← avoid.mapM (fun u => do return mk_var (← dest_var u).1 ty)) v
    return v' :: (← freshArgVars (v' :: avoid) t)

/-- `constructors_distinct_convs ax` (ind_types.ml 1239-1287): for each
    numbered constructor `C` a pattern `C x1 .. xn = y` and a conversion
    proving `(C .. = D ..) <=> F` for the other constructors `D` of its type.
    The theorems for a row `C` are proved together on first use. -/
def constructors_distinct_convs [HolBase] (numK : HolMath.Nums.NumeralConsts)
    (NUM_EQ_CONV : ioconv) (ax : thm) : ExceptT String IO (List (term × ioconv)) := do
  let (eth, evs, groups) ← prove_constructors_numbering numK ax
  let mk_convs (g : List (term × thm)) : ExceptT String IO (List (term × ioconv)) := do
    let n := g.length
    let pats := (g.map Prod.fst).toArray
    let cths := (g.map Prod.snd).toArray
    let ty := type_of pats[0]!
    let heads := pats.toList.map constructor_head
    let (nums, cons) := (heads.zip (List.range n)).partition (fun p => HolMath.Nums.is_numeral p.1)
    let ctab ← liftExcept (cons.mapM (fun (c, i) => do return ((← dest_const c).1, i)))
    let index (tm : term) : Except String Nat :=
      if HolMath.Nums.is_numeral tm then assoc tm nums
      else do assoc (← dest_const (repeat' rator tm)).1 ctab
    let rows ← (IO.mkRef (Array.replicate n (none : Option (Array thm))) : IO _)
    let row (i : Nat) : ExceptT String IO (Array thm) := do
      if let some r := (← (rows.get : IO _))[i]! then return r
      let p := pats[i]!
      let args := constructor_args p
      let thi ← SPECL args cths[i]!
      let js := (List.range n).filter (· != i)
      let ths ← js.mapM (fun j => do
        let q := pats[j]!
        let args' ← liftExcept (freshArgVars args (constructor_args q))
        DISTINCT_RULE NUM_EQ_CONV thi (← SPECL args' cths[j]!)
          (← liftExcept (do mkEq p (← list_mk_comb (constructor_head q) args'))))
      let th ← PROVE_HYP eth (← evs.foldrM SIMPLE_CHOOSE (← end_itlist CONJ ths))
      let mut r : Array thm := Array.replicate n HolBase.B.TRUTH
      for (j, th) in ← liftExcept (zip js (CONJUNCTS th)) do
        r := r.set! j (← EQF_INTRO th)
      (rows.modify (·.set! i (some r)) : IO _)
      return r
    let conv : ioconv := fun tm => ExceptT.run do
      let (i, j) ← match (do
          let (l, r) ← dest_eq tm
          let i ← index l
          let j ← index r
          if i == j || (type_match ty (type_of l) []).toBool == false then throw ""
          return (i, j) : Except String (Nat × Nat)) with
        | .ok ij => pure ij
        | .error _ => throw "constructors_distinct_convs"
      ExceptT.mk (REWR_CONV ((← row i)[j]!) tm)
    pats.toList.mapM (fun p => do
      -- `mk_eq(..., genvar ty)`: OCaml evaluates the right component first.
      let gv ← liftM (genvar ty : IO term)
      let gargs ← (constructor_args p).mapM (fun a => liftM (genvar (type_of a) : IO term))
      return (← liftExcept (do mkEq (← list_mk_comb (constructor_head p) gargs) gv), conv))
  groups.foldrM (fun g acc => do return (← mk_convs g) ++ acc) []

/-- What `let prove_constructors_injective,prove_constructors_distinct,
    constructors_distinct_convs = ...` (ind_types.ml 1007-1290) binds. -/
structure ConstructorProvers where
  injective : thm → ExceptT String IO thm
  distinct : thm → ExceptT String IO thm
  distinctConvs : thm → ExceptT String IO (List (term × ioconv))

instance : Inhabited ConstructorProvers :=
  ⟨⟨fun _ => throw "", fun _ => throw "", fun _ => throw ""⟩⟩

/-- Build the three provers (ind_types.ml 1007-1290): `DEPAIR`'s and
    `OUT_CONV`'s nets, `num_ty` and `NEGATE`'s tautology are made once, in
    that order. -/
def setupConstructorProvers [HolBase] (BETA_THM PAIR_EQ OUTL OUTR : thm)
    (mk_pair : term × term → IO (Except String term)) (numK : HolMath.Nums.NumeralConsts)
    (NUM_EQ_CONV : ioconv) : ExceptT String IO ConstructorProvers := do
  let DEPAIR := CONV_RULE (← GEN_REWRITE_CONV_NET TOP_SWEEP_CONV [PAIR_EQ])
  let OUT_CONV ← GEN_REWRITE_CONV_NET (fun c => c) [OUTL, OUTR]
  let num_ty ← qty r"num"
  let negth ← TAUT (← q r"a ==> F <=> ~a")
  let injective (ax : thm) : ExceptT String IO thm := do
    let cls := conjuncts (strip_exists (strip_forall (concl ax)).2).2
    let pats ← liftExcept (cls.mapM (fun c => do rand (← lhand (strip_forall c).2)))
    if pats.all (fun p => (constructor_args p).isEmpty) then
      throw "prove_constructors_injective"
    tryWith (prove_injectivity_fast DEPAIR OUT_CONV mk_pair ax)
      (do end_itlist CONJ
            (← mapfilterM (prove_injectivity_slow BETA_THM DEPAIR mk_pair ax) pats))
  let distinct (ax : thm) : ExceptT String IO thm := do
    let lefts ← liftExcept (recursionLefts ax)
    let fns := itlist (fun (p : term × term) acc => insert p.1 acc) lefts []
    let pats := fns.map (fun f => (lefts.filter (fun p => p.1 == f)).map Prod.snd)
    if pats.all (fun l => l.length < 2) then throw "prove_constructors_distinct"
    tryWith (prove_distinctness_fast numK NUM_EQ_CONV ax)
      (do end_itlist CONJ (← end_itlist (fun a b => pure (a ++ b))
            (← mapfilterM (prove_distinctness_slow BETA_THM numK NUM_EQ_CONV num_ty negth ax)
                pats)))
  return { injective, distinct,
           distinctConvs := constructors_distinct_convs numK NUM_EQ_CONV }

/- ---------------------------------------------------------------------- -/
/- Automatically prove the case analysis theorems.                        -/
/- ---------------------------------------------------------------------- -/

/-- `prove_cases_thm th` (ind_types.ml 964-1006).  `eepth` is
    `EXISTS_EQUATION`'s proforma. -/
partial def prove_cases_thm [HolBase] (eepth : thm) (th : thm) : ExceptT String IO thm := do
  let mk_exclauses (x : term) (rpats : List term) : Except String term := do
    let xts ← rpats.mapM (fun t => do list_mk_exists (frees t) (← mkEq x t))
    mk_abs x (← list_mk_disj xts)
  let mk_exclauses_apart (avoid : List term) (x : term) (rpats : List term) :
      Except String term := do
    let mk_xt (t : term) : Except String term := do
      let fvs := frees t
      let fvs' ← variants avoid fvs
      list_mk_exists fvs' (← mkEq x ((← vsubst (← zip fvs' fvs)) t))
    mk_abs x (← list_mk_disj (← rpats.mapM mk_xt))
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
  let sth ← SPEC_ALL th
  -- The beta-reductions in the antecedent would substitute C a0 .. an under
  -- the binders a0 .. an of the instance, which is exponential in n, so they
  -- are done with the existential variables named apart and the result
  -- converted back to the original consequent (ind_types.ml 1342-1353).
  let avoid := xs ++ (← liftExcept (Basics.variables (concl sth)))
  let xpreds' ← map2M (fun x rp => liftExcept (mk_exclauses_apart avoid x rp)) xs rpatlist
  let ith ← BETA_RULE (← INST (← liftExcept (zip xpreds' preds)) sth)
  let eclauses := conjuncts (← liftExcept (dest_imp (concl ith))).1
  let th1 ← MP ith (← end_itlist CONJ (← eclauses.mapM prove_eclause))
  let ctm ← liftExcept (do return (← vsubst (← zip xpreds preds)) (← rand (concl sth)))
  let tm ← liftExcept (rand (concl (← ExceptT.mk (REDEPTH_CONV BETA_CONV ctm))))
  EQ_MP (← liftExcept (Equal.ALPHA (concl th1) tm)) th1

/- ---------------------------------------------------------------------- -/
/- Now deal with nested recursion. Need a store of previous theorems.     -/
/- ---------------------------------------------------------------------- -/

/- ---------------------------------------------------------------------- -/
/- Also add cached rewrites for injectivity and conversions for           -/
/- distinctness of constructors to a net (ind_types.ml 1363-1404). Since  -/
/- there can be quadratically many distinctness clauses, there is instead -/
/- one entry "C x1 .. xn = y" for each constructor C, with a conversion   -/
/- that proves (C .. = D ..) <=> F for the other constructors D of its    -/
/- type (see constructors_distinct_convs). They are also put in their own -/
/- net, for CONSTRUCTORS_DISTINCT_CONV. The full distinctness theorem is  -/
/- only proved when it is first asked for.                                -/
/- ---------------------------------------------------------------------- -/

/-- The element type of `injectivity_store` (ind_types.ml 1382).  The refs
    live in Session. -/
abbrev RectypeStore := List (String × thm)

/-- The element type of `distinctness_store` (ind_types.ml 1380-1381): a
    function that proves the theorem on its first call and then returns the
    saved result. -/
abbrev DistinctnessStore := List (String × IO (Except String thm))

/-- The contents of `basic_rectype_net`, `constructors_distinct_net`,
    `distinctness_store` and `injectivity_store`. -/
structure RectypeStores where
  basicNet : HolCore.Nets.net Simp.gconv
  distinctNet : HolCore.Nets.net Simp.gconv
  dist : DistinctnessStore
  inj : RectypeStore

/-- `extend_rectype_net (tyname,(_,_,rth))` (ind_types.ml 1384-1402).  Takes
    the current contents of the four stores and returns the new ones. -/
def extend_rectype_net [HolBase] (P : ConstructorProvers)
    (entry : String × (Int × thm × thm)) (cur : RectypeStores) :
    ExceptT String IO RectypeStores := do
  let (tyname, (_, _, rth)) := entry
  let ths ← tryWith (do return [← P.injective rth]) (pure [])
  let cnvs ← tryWith (P.distinctConvs rth) (pure [])
  let dths ← if !cnvs.isEmpty then pure [] else
             tryWith (do return [← P.distinct rth]) (pure [])
  let saved ← (IO.mkRef (dths.head?) : IO _)
  let dth : IO (Except String thm) := do
    match ← saved.get with
    | some th => return .ok th
    | none =>
      match ← (P.distinct rth).run with
      | .ok th => do saved.set (some th); return .ok th
      | .error e => return .error e
  let canon_thl ← (dths ++ ths).foldrM
    (fun th acc => ExceptT.mk (Simp.mk_rewrites HolBase.B false th acc)) []
  let add_convs (net : HolCore.Nets.net Simp.gconv) : ExceptT String IO (HolCore.Nets.net Simp.gconv) :=
    cnvs.foldrM (fun (c : term × ioconv) acc => ExceptT.mk (Simp.net_of_conv c.1 c.2 acc)) net
  let dist' := if !cnvs.isEmpty || !dths.isEmpty then (tyname, dth) :: cur.dist else cur.dist
  let inj' := ths.map (fun th => (tyname, th)) ++ cur.inj
  let dnet' ← add_convs cur.distinctNet
  let net' ← canon_thl.foldrM
    (fun th acc => ExceptT.mk (Simp.net_of_thm HolBase.B true th acc)) (← add_convs cur.basicNet)
  return { basicNet := net', distinctNet := dnet', dist := dist', inj := inj' }

/- ---------------------------------------------------------------------- -/
/- Return distinctness and injectivity for a type by simple lookup.       -/
/- ---------------------------------------------------------------------- -/

/-- `distinctness ty = assoc ty (!distinctness_store) ()` (ind_types.ml 1410). -/
def distinctness (store : DistinctnessStore) (ty : String) : IO (Except String thm) :=
  match Lib.assoc ty store with
  | .ok f => f
  | .error e => return .error e

/-- `injectivity ty = assoc ty (!injectivity_store)` (ind_types.ml 1412). -/
def injectivity (store : RectypeStore) (ty : String) : Except String thm :=
  Lib.assoc ty store

/-- `CONSTRUCTORS_DISTINCT_CONV` (ind_types.ml 1418-1420), given
    `!constructors_distinct_net`. -/
def CONSTRUCTORS_DISTINCT_CONV (net : HolCore.Nets.net Simp.gconv) : ioconv := fun tm => do
  match ← Simp.REWRITES_CONV net tm with
  | .ok th => return .ok th
  | .error _ => return .error "CONSTRUCTORS_DISTINCT_CONV"

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
     extend_rectype_net (hd newentries); share distinctness_store;
     share injectivity_store`. -/
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
  -- For the big recursion theorem rth1, which is closed and has distinct
  -- bound variables, SPECL of them is what SPEC_ALL would do.
  let fvs1 := (strip_forall (concl rth1)).1
  let sth1 ← SPECL fvs1 rth1
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
  -- The function variables of rth1 for other clauses are instantiated to
  -- arbitrary closed terms, so that the definitions of the isomorphisms
  -- below (hypotheses until scrubbed) do not have them free.
  let insts1 ← do
    let fvs := fvs1.map (inst tyins1)
    let mkSel ← ExceptT.mk mk_select
    let extra ← (subtract fvs (insts1.map Prod.snd)).mapM (fun v => do
      let gv ← liftM (genvar (type_of v) : IO term)
      return (← liftExcept (mkSel (gv, t_tm)), v))
    pure (insts1 ++ extra)
  let uth0 ← BETA_RULE (← INST insts0 tth0)
  let uth1 ← BETA_RULE (← INST insts1 tth1)
  let (efvs0, sth0) ← DE_EXISTENTIALIZE_RULE R.dePth uth0
  let (efvs1, sth1) ← DE_EXISTENTIALIZE_RULE R.dePth uth1
  let efvs2 ← liftExcept (efvs0.mapM (fun t1 => do
    let key ← hd (← tl (← dest_type (type_of t1)).2)
    Lib.find (fun t2 => match (do hd (← dest_type (type_of t2)).2) with
      | .ok h => h == key
      | .error _ => false) efvs1))
  -- Only the clauses for the isomorphisms are used for rewriting.
  let sth1 ← do
    let isofn (th : thm) : Except String term := do
      return repeat' rator (← lhand (strip_forall (concl th)).2)
    end_itlist CONJ (← liftExcept ((CONJUNCTS sth1).filterM (fun th => do
      return mem (← isofn th) efvs2)))
  let isotms ← map2M (fun ff gg => ExceptT.mk (list_mk_icomb "ISO" [ff, gg])) efvs0 efvs2
  let ctm ← liftExcept (list_mk_conj isotms)
  let cth1 ← ExceptT.mk (R.ISO_EXPAND_CONV ctm)
  let ctm1 ← liftExcept (rand (concl cth1))
  let cjs := conjuncts ctm1
  let eee := (List.range cjs.length).map (fun n => n % 2 == 0)
  let (cjs1, cjs2) := partition Prod.fst (← liftExcept (zip eee cjs))
  let ctm2 ← liftExcept (do
    mk_conj (← list_mk_conj (cjs1.map Prod.snd)) (← list_mk_conj (cjs2.map Prod.snd)))
  -- Rewrite with assumed clauses, to keep the hypotheses small.
  let detrivConv ← REWRITE_CONV_NET [← ASSUME (concl sth0), ← ASSUME (concl sth1)]
  let DETRIV_RULE (th : thm) : ExceptT String IO thm := do
    TRIV_ANTE_RULE (← PROVE_HYP sth0 (← PROVE_HYP sth1 (← CONV_RULE detrivConv th)))
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

/-- `create_auxiliary_clauses avoid nty` (ind_types.ml 1692-1717). -/
def create_auxiliary_clauses (R : DefTypeRaw3) (avoid : List hol_type) (nty : hol_type) :
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
  let tyins0 ← liftExcept (tryfind (fun vty => type_match vty nty []) rtys)
  -- Rename the other type variables of the recursion theorem, i.e. its
  -- range types, if they are among those of the definition (avoid).
  let rtvs := itlist (fun e acc => union (tyvars (type_of e)) acc) evs []
  let clash (v : hol_type) : Bool := mem v avoid && !(tyins0.any (fun p => p.2 == v))
  let tyins ← liftExcept ((rtvs.filter clash).foldrM (fun v acc => do
    return (freshTyvar (acc.map Prod.fst ++ union avoid rtvs) (← dest_vartype v), v) :: acc)
    tyins0)
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
  let (k, tyal, ncls, ith, rth) ←
    create_auxiliary_clauses R (itlist (fun ty acc => union (tyvars ty) acc) utys newtys) nty
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
  let REWRITE_ISOS (th : thm) : ExceptT String IO thm := do
    let th1 ← uisoths.foldrM PROVE_HYP (← CONV_RULE funEqConv th)
    PROVE_HYP rclauses (← REWRITE_RULE
      ((← ASSUME (concl rclauses)) :: (← isoths'.mapM (CONV_RULE (REWR_CONV R.ISO)))) th1)
  -- The outer quantifiers !f. P f of the recursion theorem, one for each
  -- constructor, would just become !f'. P(g f') for those whose type is
  -- that of an isomorphism; doing that by instantiation spares rewriting
  -- through the long quantifier prefix, which is quadratic or worse.
  let irth5 ← do
    let gmap ← liftExcept (cisoths.mapM (fun th => do
      let f ← lhand (concl th)
      return ((← dest_fun_ty (type_of f)).1, ← rand (concl th))))
    let avs := (strip_forall (concl rth1)).1
    let reps := avs.map (fun v =>
      match (do
        let g ← Lib.assoc (type_of v) gmap
        let v' := mk_var (← dest_var v).1 (← dest_fun_ty (type_of g)).1
        return (← mk_comb g v', v') : Except String (term × term)) with
      | .ok p => p
      | .error _ => (v, v))
    -- `CONJ a b`: OCaml evaluates b first.
    let b ← GENL (reps.map Prod.snd) (← REWRITE_ISOS (← SPECL (reps.map Prod.fst) rth1))
    let a ← REWRITE_ISOS ith1
    CONJ a b
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

/-- The `conv` of `SUBS_CONSTANTS` (ind_types.ml 1795-1804): rewrites the
    constants `c` of the table's `|- c = d` in one traversal; fails if
    there are none. -/
partial def subsConstantsConv (tbl : List (String × thm)) : Equal.conv := fun tm =>
  match tm with
  | .Const s _ => do
    let th ← Lib.assoc s tbl
    if (← lhs (concl th)) == tm then return th else failwith "SUBS_CONSTANTS"
  | .Comb l r =>
    let attempt : Except String thm := do
      let lth ← subsConstantsConv tbl l
      match (do HolCore.Kernel.MK_COMB lth (← subsConstantsConv tbl r)) with
      | .ok th => .ok th
      | .error _ => Equal.AP_THM lth r
    match attempt with
    | .ok th => .ok th
    | .error _ => do Equal.AP_TERM l (← subsConstantsConv tbl r)
  | .Abs v b => do HolCore.Kernel.ABS v (← subsConstantsConv tbl b)
  | _ => failwith "SUBS_CONSTANTS"

/-- `SUBS_CONSTANTS ths` (ind_types.ml 1790-1805): SUBS for theorems
    `|- c = d` with constants `c`, in a single traversal of the theorem
    (SUBS_CONV does one beta-reduction of all of it for each). -/
def SUBS_CONSTANTS [HolBase] (ths : List thm) : thm → ExceptT String IO thm :=
  let tbl : Except String (List (String × thm)) :=
    ths.mapM (fun th => do return ((← dest_const (← lhs (concl th))).1, th))
  fun th => do
    let tbl ← liftExcept tbl
    CONV_RULE (fun tm => pure (match subsConstantsConv tbl tm with
      | .ok r => .ok r
      | .error _ => .ok (REFL tm))) th

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
  let SUBS_CDEFS := SUBS_CONSTANTS cdefs
  let ith1 ← SUBS_CDEFS ith0
  let rth1 ← GENL tavs (← SUBS_CDEFS (← INST (← liftExcept (zip tavs avs)) (← SPECL avs rth0)))
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
