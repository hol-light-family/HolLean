/- File: HolTest/CoverageTest.lean
Tests for the exported tactics, rules and conversions that no other test or
Help example exercised.  Each expected result was obtained by running the same
OCaml expression in HOL Light.
Part of the Lean4 translation of HOL Light by Chris Walton 2026. -/

import HolTest.CommonTest

open HolCore.Kernel Session HolTest.CommonTest

-- `num` and the arithmetic theorems must exist before the quotations below
-- are parsed.
#eval do let _ ← IO.mkRef (concl ADD_0); pure ()

/- ---------------------------------------------------------------------- -/
/- Tactics.                                                               -/
/- ---------------------------------------------------------------------- -/

#eval ruleOK "ANTE_RES_THEN"
  (prove ([[ (p ==> q) ==> p ==> q ]])
    (THEN DISCH_TAC (DISCH_THEN (ANTE_RES_THEN ACCEPT_TAC))))
  "(p ==> q) ==> p ==> q"
#eval ruleOK "ANTS_TAC"
  (prove ([[ p ==> (p ==> q) ==> q ]])
    (THEN DISCH_TAC (THENL ANTS_TAC [ASM_REWRITE_TAC [], REWRITE_TAC []])))
  "p ==> (p ==> q) ==> q"
#eval failsOK "ANTS_TAC on a goal without an antecedent"
  (prove ([[ p ==> q ]]) ANTS_TAC) "MATCH_MP_TAC: No match"
#eval ruleOK "AP_THM_TAC"
  (prove ([[ (f:A->B) = g ==> f x = g x ]])
    (THEN DISCH_TAC (THEN AP_THM_TAC (ASM_REWRITE_TAC []))))
  "(f:A->B) = g ==> f x = g x"
#eval ruleOK "CHOOSE_TAC"
  (prove ([[ (?x:num. x = 1) ==> ?y:num. y = 1 ]])
    (THEN (DISCH_THEN CHOOSE_TAC)
      (THEN (EXISTS_TAC ([[ x:num ]])) (ASM_REWRITE_TAC []))))
  "(?x:num. x = 1) ==> (?y:num. y = 1)"
#eval ruleOK "EVERY_ASSUM"
  (prove ([[ p ==> q ==> p /\ q ]])
    (THEN (REPEAT DISCH_TAC)
      (THEN CONJ_TAC (EVERY_ASSUM (fun th => TRY (ACCEPT_TAC th))))))
  "p ==> q ==> p /\\ q"
#eval ruleOK "FREEZE_THEN"
  (prove ([[ p ==> p ]]) (DISCH_THEN (fun th => FREEZE_THEN ACCEPT_TAC th)))
  "p ==> p"
#eval ruleOK "MK_COMB_TAC"
  (prove ([[ (f:A->B) = g /\ x = y ==> f x = g y ]])
    (THEN STRIP_TAC (THEN MK_COMB_TAC (ASM_REWRITE_TAC []))))
  "(f:A->B) = g /\\ x = y ==> f x = g y"
#eval ruleOK "REFUTE_THEN"
  (prove ([[ ~ ~p ==> p ]])
    (THEN DISCH_TAC (REFUTE_THEN (fun th =>
      THEN (UNDISCH_TAC ([[ ~ ~p ]])) (REWRITE_TAC [th])))))
  "~ ~p ==> p"
#eval ruleOK "STRIP_THM_THEN"
  (prove ([[ p /\ q ==> q ]])
    (THEN (DISCH_THEN (STRIP_THM_THEN ASSUME_TAC)) (ASM_REWRITE_TAC [])))
  "p /\\ q ==> q"
#eval ruleOK "SUBST_VAR_TAC"
  (prove ([[ x = 1 ==> x + x = 1 + 1 ]])
    (THEN DISCH_TAC (THEN (FIRST_X_ASSUM SUBST_VAR_TAC) REFL_TAC)))
  "x = 1 ==> x + x = 1 + 1"
#eval ruleOK "UNDISCH_THEN"
  (prove ([[ p ==> p ]]) (THEN DISCH_TAC (UNDISCH_THEN ([[ p:bool ]]) ACCEPT_TAC)))
  "p ==> p"

/- ---------------------------------------------------------------------- -/
/- Rewriting and simplification.                                          -/
/- ---------------------------------------------------------------------- -/

#eval ruleOK "ASM_REWRITE_RULE"
  (do match ← ASM_REWRITE_RULE [] (ADD_ASSUM ([[ x = 1 ]]) (SPEC ([[ x:num ]]) ADD_0)) with
      | .ok th => pure (.ok (DISCH_ALL th)) | .error e => pure (.error e))
  "x = 1 ==> 1 + 0 = 1"
#eval ruleOK "PURE_ASM_REWRITE_RULE"
  (do match ← PURE_ASM_REWRITE_RULE [] (ADD_ASSUM ([[ x = 1 ]]) (SPEC ([[ x:num ]]) ADD_0)) with
      | .ok th => pure (.ok (DISCH_ALL th)) | .error e => pure (.error e))
  "x = 1 ==> 1 + 0 = 1"
#eval ruleOK "GEN_REWRITE_RULE"
  (GEN_REWRITE_RULE HolCore.Simp.onceDepthConvIO [ADD_SYM] (REFL ([[ a + b:num ]])))
  "b + a = b + a"
#eval ruleOK "GEN_REWRITE_TAC"
  (prove ([[ a + b = b + a:num ]])
    (THEN (GEN_REWRITE_TAC HolCore.Simp.landConvIO [ADD_SYM]) REFL_TAC))
  "a + b = b + a:num"
#eval ruleOK "ONCE_REWRITE_RULE"
  (ONCE_REWRITE_RULE [ADD_SYM] (REFL ([[ a + b:num ]]))) "T"
#eval ruleOK "PURE_ONCE_REWRITE_RULE"
  (PURE_ONCE_REWRITE_RULE [ADD_SYM] (REFL ([[ a + b:num ]]))) "b + a = b + a"
#eval ruleOK "PURE_ONCE_REWRITE_CONV"
  (PURE_ONCE_REWRITE_CONV [ADD_SYM] ([[ a + b = c:num ]]))
  "a + b = c <=> b + a = c:num"
#eval ruleOK "PURE_ONCE_REWRITE_TAC"
  (prove ([[ a + b = c ==> b + a = c:num ]])
    (THEN DISCH_TAC (THEN (PURE_ONCE_REWRITE_TAC [ADD_SYM]) (ASM_REWRITE_TAC []))))
  "a + b = c ==> b + a = c:num"
#eval ruleOK "PURE_ASM_REWRITE_TAC"
  (prove ([[ x = 1 ==> x + 0 = 1 + 0 ]])
    (THEN DISCH_TAC (THEN (PURE_ASM_REWRITE_TAC []) REFL_TAC)))
  "x = 1 ==> x + 0 = 1 + 0"
#eval ruleOK "ONCE_SIMP_CONV"
  (ONCE_SIMP_CONV [ADD_CLAUSES] ([[ 0 + x + 0 ]])) "0 + x + 0 = x + 0"
#eval ruleOK "ONCE_SIMP_TAC"
  (prove ([[ 0 + x = x ]]) (THEN (ONCE_SIMP_TAC [ADD_CLAUSES]) REFL_TAC))
  "0 + x = x"
#eval ruleOK "ONCE_ASM_SIMP_TAC"
  (prove ([[ x = 1 ==> x + 0 = 1 ]])
    (THEN DISCH_TAC (THEN (ONCE_ASM_SIMP_TAC [ADD_CLAUSES]) (ASM_REWRITE_TAC []))))
  "x = 1 ==> x + 0 = 1"
#eval failsOK "ONCE_ASM_SIMP_TAC leaves a goal"
  (prove ([[ x = 1 ==> x + 0 = 1 ]])
    (THEN DISCH_TAC (ONCE_ASM_SIMP_TAC [ADD_CLAUSES])))
  "TAC_PROOF: Unsolved goals"
#eval ruleOK "PURE_SIMP_CONV"
  (PURE_SIMP_CONV [ADD_CLAUSES] ([[ 0 + SUC x ]])) "0 + SUC x = SUC x"
#eval ruleOK "PURE_SIMP_RULE"
  (PURE_SIMP_RULE [ADD_CLAUSES] (REFL ([[ 0 + x ]]))) "x = x"
#eval ruleOK "PURE_SIMP_TAC"
  (prove ([[ 0 + x = x ]]) (THEN (PURE_SIMP_TAC [ADD_CLAUSES]) REFL_TAC))
  "0 + x = x"
#eval ruleOK "PURE_ASM_SIMP_TAC"
  (prove ([[ x = 1 ==> x + 0 = 1 ]])
    (THEN DISCH_TAC (THEN (PURE_ASM_SIMP_TAC [ADD_CLAUSES]) REFL_TAC)))
  "x = 1 ==> x + 0 = 1"

/- ---------------------------------------------------------------------- -/
/- Classical rules and conversions.                                       -/
/- ---------------------------------------------------------------------- -/

#eval ruleOK "CCONTR"
  (pure (do
    let th ← MP (ASSUME ([[ ~p ==> F ]])) (ASSUME ([[ ~p ]]))
    return DISCH_ALL (← CCONTR ([[ p:bool ]]) th)))
  "(~p ==> F) ==> p"
#eval failsOK "CCONTR on a non-F theorem"
  (pure (CCONTR ([[ p:bool ]]) (ASSUME ([[ q:bool ]])))) "CCONTR"
#eval ruleOK "CONTRAPOS_CONV" (pure (CONTRAPOS_CONV ([[ p ==> q ]])))
  "(p ==> q) <=> (~q ==> ~p)"
#eval failsOK "CONTRAPOS_CONV on a non-implication"
  (pure (CONTRAPOS_CONV ([[ p /\ q ]]))) "CONTRAPOS_CONV"
-- The real term is parsed after the real layer is loaded.
#eval (do
  let _ ← IO.mkRef (concl realThms1.REAL_OF_NUM_LT)
  match ← HolCore.Parser.parse_term "&1 / &2 + &1 / &3" with
  | .error e => IO.println s!"REAL_RAT_RED_CONV -> MISMATCH parse {e}"
  | .ok tm => ruleOK "REAL_RAT_RED_CONV" (REAL_RAT_RED_CONV tm) "&1 / &2 + &1 / &3 = &5 / &6" : IO Unit)
