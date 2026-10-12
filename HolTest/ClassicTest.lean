/- File: HolTest/ClassicTest.lean
Runtime test suite: class.ml - the axioms and classical constants
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Tests: class.ml - the axioms and classical constants.                  -/
/- ---------------------------------------------------------------------- -/


-- class.ml: axioms/constants declared
#eval ETA_AX      -- |- !t. (\x. t x) = t
#eval SELECT_AX   -- |- !P x. P x ==> P ((@) P)
#eval COND_DEF    -- |- COND = \t t1 t2. @x. ...
#eval EQ_EXT      -- |- !f g. (!x. f x = g x) ==> f = g
#eval FUN_EQ_THM  -- |- !f g. f = g <=> (!x. f x = g x)
#eval EXISTS_THM    -- |- (?) = (\P. P ((@) P))
#eval SELECT_REFL   -- |- !x. (@y. y = x) = x
#eval SELECT_UNIQUE -- |- !P x. (!y. P y <=> y = x) ==> (@) P = x
-- SELECT_CONV on a term containing a real epsilon-term (@x. x = a):
#eval SELECT_CONV ([[ (@x:A. x = a) = a ]])   -- |- ((@x. x = a) = a) <=> (?x. x = a)
#eval EXCLUDED_MIDDLE   -- |- !t. t \/ ~t
#eval BOOL_CASES_AX     -- |- !t. (t <=> T) \/ (t <=> F)
#eval TAUT ([[ (p:bool) ==> p ]])                       -- |- p ==> p
#eval TAUT ([[ ~(p /\ (q:bool)) <=> ~p \/ ~q ]])        -- |- de Morgan
#eval DE_MORGAN_THM   -- |- !t1 t2. (~(t1/\t2)<=>~t1\/~t2)/\(~(t1\/t2)<=>~t1/\~t2)
#eval NOT_CLAUSES     -- |- (!t. ~~t<=>t)/\(~T<=>F)/\(~F<=>T)
#eval NOT_IMP         -- |- !t1 t2. ~(t1==>t2)<=>t1/\~t2
#eval NOT_EXISTS_THM  -- |- !P. ~(?x. P x) <=> (!x. ~P x)
#eval NOT_FORALL_THM  -- |- !P. ~(!x. P x) <=> (?x. ~P x)
#eval FORALL_BOOL_THM -- |- (!b. P b) <=> P T /\ P F
#eval EXISTS_BOOL_THM -- |- (?b. P b) <=> P T \/ P F
#eval LEFT_FORALL_OR_THM   -- |- !P Q. (!x. P x \/ Q) <=> (!x. P x) \/ Q
#eval LEFT_IMP_FORALL_THM  -- |- !P Q. ((!x. P x) ==> Q) <=> (?x. P x ==> Q)
#eval RIGHT_IMP_EXISTS_THM -- |- !P Q. (P ==> ?x. Q x) <=> (?x. P ==> Q x)
#eval COND_CLAUSES  -- |- !t1 t2. ((if T then t1 else t2)=t1)/\((if F then t1 else t2)=t2)
#eval COND_ID       -- |- !b t. (if b then t else t) = t
#eval COND_RAND     -- |- !b f x y. f (if b then x else y) = if b then f x else f y
#eval MONO_COND     -- |- (A==>B')/\(C==>D)==>(if b then A else C)==>(if b then B' else D)
#eval COND_ELIM_THM -- |- P (if c then x else y) <=> (c==>P x)/\(~c==>P y)
#eval SKOLEM_THM      -- |- !P. (!x. ?y. P x y) <=> (?y. !x. P x (y x))
#eval SKOLEM_THM_GEN  -- |- !P R. (!x. P x ==> ?y. R x y) <=> (?f. !x. P x ==> R x (f x))
#eval UNIQUE_SKOLEM_ALT -- |- !P. (!x. ?!y. P x y) <=> (?f. !x y. P x y <=> f x = y)
#eval UNIQUE_SKOLEM_THM -- |- !P. (!x. ?!y. P x y) <=> (?!f. !x. P x (f x))
#eval bool_INDUCT     -- |- !P. P F /\ P T ==> !x. P x
#eval bool_RECURSION  -- |- !a b. ?f. f F = a /\ f T = b
-- COND_CASES_TAC: split on the arbitrary conditional's guard.
#eval prove ([[ (if (b:bool) then (t:A) else t) = t ]])
        (THEN COND_CASES_TAC (REWRITE_TAC []))            -- |- (if b then t else t) = t
