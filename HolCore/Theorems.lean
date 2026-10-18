/- File: Theorems.lean
Additional theorems, mainly about quantifiers, and additional tactics.
Original       John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Original (c) Copyright, Marco Maggesi 2012
Lean4 translation by Chris Walton 2026
-/

import HolCore.Bool
import HolCore.Equal
import HolCore.Drule
import HolCore.Tactics
import HolCore.Itab
import HolCore.Simp
import HolCore.Parser

open HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Bool HolCore.Equal
     HolCore.Drule HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Parser

namespace HolCore.Theorems

/-- The standard logical theorems proved in `theorems.ml`. Built once by
    `setupTheorems` (which also extends the basic rewrites/congruences). -/
structure TheoremThms where
  EQ_REFL : thm
  REFL_CLAUSE : thm
  EQ_SYM : thm
  EQ_SYM_EQ : thm
  EQ_TRANS : thm
  BETA_THM : thm
  ABS_SIMP : thm
  CONJ_ASSOC : thm
  CONJ_SYM : thm
  CONJ_ACI : thm
  DISJ_ASSOC : thm
  DISJ_SYM : thm
  DISJ_ACI : thm
  IMP_CONJ : thm
  IMP_IMP : thm
  IMP_CONJ_ALT : thm
  LEFT_OR_DISTRIB : thm
  RIGHT_OR_DISTRIB : thm
  FORALL_SIMP : thm
  EXISTS_SIMP : thm
  EQ_IMP : thm
  EQ_CLAUSES : thm
  NOT_CLAUSES_WEAK : thm
  AND_CLAUSES : thm
  OR_CLAUSES : thm
  IMP_CLAUSES : thm
  EXISTS_UNIQUE_THM : thm
  EXISTS_REFL : thm
  EXISTS_UNIQUE_REFL : thm
  UNWIND_THM1 : thm
  UNWIND_THM2 : thm
  FORALL_UNWIND_THM2 : thm
  FORALL_UNWIND_THM1 : thm
  SWAP_FORALL_THM : thm
  SWAP_EXISTS_THM : thm
  FORALL_AND_THM : thm
  AND_FORALL_THM : thm
  LEFT_AND_FORALL_THM : thm
  RIGHT_AND_FORALL_THM : thm
  EXISTS_OR_THM : thm
  OR_EXISTS_THM : thm
  LEFT_OR_EXISTS_THM : thm
  RIGHT_OR_EXISTS_THM : thm
  LEFT_EXISTS_AND_THM : thm
  RIGHT_EXISTS_AND_THM : thm
  TRIV_EXISTS_AND_THM : thm
  LEFT_AND_EXISTS_THM : thm
  RIGHT_AND_EXISTS_THM : thm
  TRIV_AND_EXISTS_THM : thm
  TRIV_FORALL_OR_THM : thm
  TRIV_OR_FORALL_THM : thm
  RIGHT_IMP_FORALL_THM : thm
  RIGHT_FORALL_IMP_THM : thm
  LEFT_IMP_EXISTS_THM : thm
  LEFT_FORALL_IMP_THM : thm
  TRIV_FORALL_IMP_THM : thm
  TRIV_EXISTS_IMP_THM : thm
  MONO_AND : thm
  MONO_OR : thm
  MONO_IMP : thm
  MONO_NOT : thm
  MONO_FORALL : thm
  MONO_EXISTS : thm
  WLOG_RELATION : thm
  EXISTS_UNIQUE_ALT : thm
  EXISTS_UNIQUE : thm
  deriving Inhabited

/-- Establish the `theorems.ml` layer: prove the standard logical theorems and
    extend the basic rewrite/congruence sets. Run once, after `setupBool`.
    A pure `ExceptT String IO` computation (no `unsafe`, no cache/state of its
    own; it only reads its `BoolThms` argument and calls the safe Simp API). -/
def setupTheorems (B : BoolThms) : ExceptT String IO TheoremThms := do
  let prove := Tactics.prove B
  let THEN := Tactics.THEN B
  let GEN_TAC := Tactics.GEN_TAC B
  let REPEAT := Tactics.REPEAT B
  let REFL_TAC := Tactics.REFL_TAC B
  let EQ_TAC := Tactics.EQ_TAC B
  let STRIP_TAC := Tactics.STRIP_TAC B
  let MATCH_ACCEPT_TAC := Tactics.MATCH_ACCEPT_TAC B
  let DISCH_THEN := Tactics.DISCH_THEN B
  let DISCH_TAC := Tactics.DISCH_TAC B
  let ACCEPT_TAC := Tactics.ACCEPT_TAC B
  let BETA_TAC := Tactics.BETA_TAC B
  let REWRITE_TAC := Simp.REWRITE_TAC B
  let PURE_ASM_REWRITE_TAC := Simp.PURE_ASM_REWRITE_TAC B
  let ITAUT_TAC := Itab.ITAUT_TAC_MAIN B
  let THENL := Tactics.THENL B
  let EXISTS_TAC := Tactics.EXISTS_TAC B
  let MATCH_MP_TAC := Tactics.MATCH_MP_TAC B
  let CONJ_TAC := Tactics.CONJ_TAC B
  let TRY := Tactics.TRY B
  let ORELSE := Tactics.ORELSE
  let FIRST_ASSUM := Tactics.FIRST_ASSUM
  let CHOOSE_THEN := Tactics.CHOOSE_THEN B
  let X_CHOOSE_TAC := Tactics.X_CHOOSE_TAC B
  let CONJUNCTS_THEN2 := Tactics.CONJUNCTS_THEN2 B
  let SUBST1_TAC := Tactics.SUBST1_TAC B
  let CONV_TAC := Tactics.CONV_TAC B
  let MP_TAC := Tactics.MP_TAC B
  let ASM_REWRITE_TAC := Simp.ASM_REWRITE_TAC B
  let ASM_SIMP_TAC := Simp.ASM_SIMP_TAC B
  let pt (s : String) : ExceptT String IO term := do (parse_term s : IO (Except String term))
  let ITAUT (s : String) : ExceptT String IO thm := do (Itab.ITAUT B (← pt s) : IO (Except String thm))

  -- More stuff about equality.
  let EQ_REFL ← (prove (← pt "!x:A. x = x") (THEN GEN_TAC REFL_TAC) : IO (Except String thm))
  let REFL_CLAUSE ← (prove (← pt "!x:A. (x = x) <=> T")
      (THEN GEN_TAC (MATCH_ACCEPT_TAC (← B.EQT_INTRO (← B.SPEC_ALL EQ_REFL)))) : IO (Except String thm))
  let EQ_SYM ← (prove (← pt "!(x:A) y. (x = y) ==> (y = x)")
      (THEN (REPEAT GEN_TAC)
            (DISCH_THEN (fun th => fun g => do
               match SYM th with
               | .ok s => (ACCEPT_TAC s g : IO (Except String goalstate))
               | .error e => return .error e))) : IO (Except String thm))
  let EQ_SYM_EQ ← (prove (← pt "!(x:A) y. (x = y) <=> (y = x)")
      (THEN (REPEAT GEN_TAC) (THEN EQ_TAC (MATCH_ACCEPT_TAC EQ_SYM))) : IO (Except String thm))
  let EQ_TRANS ← (prove (← pt "!(x:A) y z. (x = y) /\\ (y = z) ==> (x = z)")
      (THEN (REPEAT STRIP_TAC) (THEN (PURE_ASM_REWRITE_TAC []) REFL_TAC)) : IO (Except String thm))

  -- A couple of theorems about beta reduction.
  let BETA_THM ← (prove (← pt "!(f:A->B) y. (\\x. (f:A->B) x) y = f y")
      (THEN (REPEAT GEN_TAC) (THEN BETA_TAC REFL_TAC)) : IO (Except String thm))
  let ABS_SIMP ← (prove (← pt "!(t1:A) (t2:B). (\\x. t1) t2 = t1")
      (THEN (REPEAT GEN_TAC) (REWRITE_TAC [BETA_THM, REFL_CLAUSE])) : IO (Except String thm))

  -- A few "big name" intuitionistic tautologies.
  let CONJ_ASSOC ← (prove (← pt "!t1 t2 t3. t1 /\\ t2 /\\ t3 <=> (t1 /\\ t2) /\\ t3") ITAUT_TAC : IO (Except String thm))
  let CONJ_SYM ← (prove (← pt "!t1 t2. t1 /\\ t2 <=> t2 /\\ t1") ITAUT_TAC : IO (Except String thm))
  let CONJ_ACI ← (prove (← pt "(p /\\ q <=> q /\\ p) /\\ ((p /\\ q) /\\ r <=> p /\\ (q /\\ r)) /\\ (p /\\ (q /\\ r) <=> q /\\ (p /\\ r)) /\\ (p /\\ p <=> p) /\\ (p /\\ (p /\\ q) <=> p /\\ q)") ITAUT_TAC : IO (Except String thm))
  let DISJ_ASSOC ← (prove (← pt "!t1 t2 t3. t1 \\/ t2 \\/ t3 <=> (t1 \\/ t2) \\/ t3") ITAUT_TAC : IO (Except String thm))
  let DISJ_SYM ← (prove (← pt "!t1 t2. t1 \\/ t2 <=> t2 \\/ t1") ITAUT_TAC : IO (Except String thm))
  let DISJ_ACI ← (prove (← pt "(p \\/ q <=> q \\/ p) /\\ ((p \\/ q) \\/ r <=> p \\/ (q \\/ r)) /\\ (p \\/ (q \\/ r) <=> q \\/ (p \\/ r)) /\\ (p \\/ p <=> p) /\\ (p \\/ (p \\/ q) <=> p \\/ q)") ITAUT_TAC : IO (Except String thm))
  let IMP_CONJ ← (prove (← pt "p /\\ q ==> r <=> p ==> q ==> r") ITAUT_TAC : IO (Except String thm))
  let IMP_IMP ← liftExcept (GSYM IMP_CONJ)
  let IMP_CONJ_ALT ← (prove (← pt "p /\\ q ==> r <=> q ==> p ==> r") ITAUT_TAC : IO (Except String thm))
  -- A couple of "distribution" tautologies are useful.
  let LEFT_OR_DISTRIB ← (prove (← pt "!p q r. p /\\ (q \\/ r) <=> p /\\ q \\/ p /\\ r") ITAUT_TAC : IO (Except String thm))
  let RIGHT_OR_DISTRIB ← (prove (← pt "!p q r. (p \\/ q) /\\ r <=> p /\\ r \\/ q /\\ r") ITAUT_TAC : IO (Except String thm))
  -- Degenerate cases of quantifiers.
  let FORALL_SIMP ← (prove (← pt "!t. (!x:A. t) = t") ITAUT_TAC : IO (Except String thm))
  let EXISTS_SIMP ← (prove (← pt "!t. (?x:A. t) = t") ITAUT_TAC : IO (Except String thm))
  -- I also use this a lot (as a prelude to congruence reasoning).
  let EQ_IMP ← ITAUT "(a <=> b) ==> a ==> b"

  -- Start building up the basic rewrites; we add a few more later.
  let EQ_CLAUSES ← (prove (← pt "!t. ((T <=> t) <=> t) /\\ ((t <=> T) <=> t) /\\ ((F <=> t) <=> ~t) /\\ ((t <=> F) <=> ~t)") ITAUT_TAC : IO (Except String thm))
  let NOT_CLAUSES_WEAK ← (prove (← pt "(~T <=> F) /\\ (~F <=> T)") ITAUT_TAC : IO (Except String thm))
  let AND_CLAUSES ← (prove (← pt "!t. (T /\\ t <=> t) /\\ (t /\\ T <=> t) /\\ (F /\\ t <=> F) /\\ (t /\\ F <=> F) /\\ (t /\\ t <=> t)") ITAUT_TAC : IO (Except String thm))
  let OR_CLAUSES ← (prove (← pt "!t. (T \\/ t <=> T) /\\ (t \\/ T <=> T) /\\ (F \\/ t <=> t) /\\ (t \\/ F <=> t) /\\ (t \\/ t <=> t)") ITAUT_TAC : IO (Except String thm))
  let IMP_CLAUSES ← (prove (← pt "!t. (T ==> t <=> t) /\\ (t ==> T <=> T) /\\ (F ==> t <=> T) /\\ (t ==> t <=> T) /\\ (t ==> F <=> ~t)") ITAUT_TAC : IO (Except String thm))
  let IMP_EQ_CLAUSE ← (prove (← pt "((x = x) ==> p) <=> p")
      (REWRITE_TAC [(← B.EQT_INTRO (← B.SPEC_ALL EQ_REFL)), IMP_CLAUSES]) : IO (Except String thm))
  let _ ← (Simp.extend_basic_rewrites B
      [REFL_CLAUSE, EQ_CLAUSES, NOT_CLAUSES_WEAK, AND_CLAUSES, OR_CLAUSES,
       IMP_CLAUSES, FORALL_SIMP, EXISTS_SIMP, BETA_THM, IMP_EQ_CLAUSE] : IO (Except String Unit))
  let congThm ← ITAUT "(p <=> p') ==> (p' ==> (q <=> q')) ==> (p ==> q <=> p' ==> q')"
  Simp.extend_basic_congs [congThm]

  -- Rewrite rule for unique existence.
  let EXISTS_UNIQUE_THM ← (prove (← pt "!P. (?!x:A. P x) <=> (?x. P x) /\\ (!x x'. P x /\\ P x' ==> (x = x'))")
      (THEN GEN_TAC (REWRITE_TAC [B.EXISTS_UNIQUE_DEF])) : IO (Except String thm))

  -- Trivial instances of existence.
  let EXISTS_REFL ← (prove (← pt "!a:A. ?x. x = a")
      (THEN GEN_TAC (THEN (EXISTS_TAC (← pt "a:A")) REFL_TAC)) : IO (Except String thm))
  let EXISTS_UNIQUE_REFL ← (prove (← pt "!a:A. ?!x. x = a")
      (THEN GEN_TAC (THEN (REWRITE_TAC [EXISTS_UNIQUE_THM])
        (THEN (THENL (REPEAT (ORELSE EQ_TAC STRIP_TAC))
                     [EXISTS_TAC (← pt "a:A"), ASM_REWRITE_TAC []])
              REFL_TAC)))
      : IO (Except String thm))
  -- Unwinding.
  let UNWIND_THM1 ← (prove (← pt "!P (a:A). (?x. a = x /\\ P x) <=> P a")
      (THEN (REPEAT GEN_TAC) (THENL EQ_TAC
        [DISCH_THEN (CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC ACCEPT_TAC)),
         THEN DISCH_TAC (THEN (EXISTS_TAC (← pt "a:A"))
           (THEN CONJ_TAC (THEN (TRY (FIRST_ASSUM MATCH_ACCEPT_TAC)) REFL_TAC)))]))
      : IO (Except String thm))
  let UNWIND_THM2 ← (prove (← pt "!P (a:A). (?x. x = a /\\ P x) <=> P a")
      (THEN (REPEAT GEN_TAC)
        (THEN (CONV_TAC (fun t => return (LAND_CONV (ONCE_DEPTH_CONV SYM_CONV) t)))
              (MATCH_ACCEPT_TAC UNWIND_THM1))) : IO (Except String thm))
  let FORALL_UNWIND_THM2 ← (prove (← pt "!P (a:A). (!x. x = a ==> P x) <=> P a")
      (THEN (REPEAT GEN_TAC) (THENL EQ_TAC
        [THEN (DISCH_THEN (fun th => fun g => do
                 match B.SPEC (← liftM (parse_term "a:A")).toOption.get! th with
                 | .ok s => (MP_TAC s g : IO (Except String goalstate))
                 | .error e => return .error e)) (REWRITE_TAC []),
         THEN DISCH_TAC (THEN GEN_TAC (THEN (DISCH_THEN SUBST1_TAC) (ASM_REWRITE_TAC [])))]))
      : IO (Except String thm))
  let FORALL_UNWIND_THM1 ← (prove (← pt "!P (a:A). (!x. a = x ==> P x) <=> P a")
      (THEN (REPEAT GEN_TAC)
        (THEN (CONV_TAC (fun t => return (LAND_CONV (ONCE_DEPTH_CONV SYM_CONV) t)))
              (MATCH_ACCEPT_TAC FORALL_UNWIND_THM2))) : IO (Except String thm))

  -- Permuting quantifiers
  let SWAP_FORALL_THM ← (prove (← pt "!P:A->B->bool. (!x y. P x y) <=> (!y x. P x y)") ITAUT_TAC : IO (Except String thm))
  let SWAP_EXISTS_THM ← (prove (← pt "!P:A->B->bool. (?x y. P x y) <=> (?y x. P x y)") ITAUT_TAC : IO (Except String thm))

  -- Universal quantifier and conjunction.
  let FORALL_AND_THM ← (prove (← pt "!P Q. (!x:A. P x /\\ Q x) <=> (!x. P x) /\\ (!x. Q x)") ITAUT_TAC : IO (Except String thm))
  let AND_FORALL_THM ← (prove (← pt "!P Q. (!x. P x) /\\ (!x. Q x) <=> (!x:A. P x /\\ Q x)") ITAUT_TAC : IO (Except String thm))
  let LEFT_AND_FORALL_THM ← (prove (← pt "!P Q. (!x:A. P x) /\\ Q <=> (!x:A. P x /\\ Q)") ITAUT_TAC : IO (Except String thm))
  let RIGHT_AND_FORALL_THM ← (prove (← pt "!P Q. P /\\ (!x:A. Q x) <=> (!x. P /\\ Q x)") ITAUT_TAC : IO (Except String thm))
  -- Existential quantifier and disjunction.
  let EXISTS_OR_THM ← (prove (← pt "!P Q. (?x:A. P x \\/ Q x) <=> (?x. P x) \\/ (?x. Q x)") ITAUT_TAC : IO (Except String thm))
  let OR_EXISTS_THM ← (prove (← pt "!P Q. (?x. P x) \\/ (?x. Q x) <=> (?x:A. P x \\/ Q x)") ITAUT_TAC : IO (Except String thm))
  let LEFT_OR_EXISTS_THM ← (prove (← pt "!P Q. (?x. P x) \\/ Q <=> (?x:A. P x \\/ Q)") ITAUT_TAC : IO (Except String thm))
  let RIGHT_OR_EXISTS_THM ← (prove (← pt "!P Q. P \\/ (?x. Q x) <=> (?x:A. P \\/ Q x)") ITAUT_TAC : IO (Except String thm))
  -- Existential quantifier and conjunction.
  let LEFT_EXISTS_AND_THM ← (prove (← pt "!P Q. (?x:A. P x /\\ Q) <=> (?x:A. P x) /\\ Q") ITAUT_TAC : IO (Except String thm))
  let RIGHT_EXISTS_AND_THM ← (prove (← pt "!P Q. (?x:A. P /\\ Q x) <=> P /\\ (?x:A. Q x)") ITAUT_TAC : IO (Except String thm))
  let TRIV_EXISTS_AND_THM ← (prove (← pt "!P Q. (?x:A. P /\\ Q) <=> (?x:A. P) /\\ (?x:A. Q)") ITAUT_TAC : IO (Except String thm))
  let LEFT_AND_EXISTS_THM ← (prove (← pt "!P Q. (?x:A. P x) /\\ Q <=> (?x:A. P x /\\ Q)") ITAUT_TAC : IO (Except String thm))
  let RIGHT_AND_EXISTS_THM ← (prove (← pt "!P Q. P /\\ (?x:A. Q x) <=> (?x:A. P /\\ Q x)") ITAUT_TAC : IO (Except String thm))
  let TRIV_AND_EXISTS_THM ← (prove (← pt "!P Q. (?x:A. P) /\\ (?x:A. Q) <=> (?x:A. P /\\ Q)") ITAUT_TAC : IO (Except String thm))
  -- Only trivial instances of universal quantifier and disjunction.
  let TRIV_FORALL_OR_THM ← (prove (← pt "!P Q. (!x:A. P \\/ Q) <=> (!x:A. P) \\/ (!x:A. Q)") ITAUT_TAC : IO (Except String thm))
  let TRIV_OR_FORALL_THM ← (prove (← pt "!P Q. (!x:A. P) \\/ (!x:A. Q) <=> (!x:A. P \\/ Q)") ITAUT_TAC : IO (Except String thm))
  -- Implication and quantifiers.
  let RIGHT_IMP_FORALL_THM ← (prove (← pt "!P Q. (P ==> !x:A. Q x) <=> (!x. P ==> Q x)") ITAUT_TAC : IO (Except String thm))
  let RIGHT_FORALL_IMP_THM ← (prove (← pt "!P Q. (!x. P ==> Q x) <=> (P ==> !x:A. Q x)") ITAUT_TAC : IO (Except String thm))
  let LEFT_IMP_EXISTS_THM ← (prove (← pt "!P Q. ((?x:A. P x) ==> Q) <=> (!x. P x ==> Q)") ITAUT_TAC : IO (Except String thm))
  let LEFT_FORALL_IMP_THM ← (prove (← pt "!P Q. (!x. P x ==> Q) <=> ((?x:A. P x) ==> Q)") ITAUT_TAC : IO (Except String thm))
  let TRIV_FORALL_IMP_THM ← (prove (← pt "!P Q. (!x:A. P ==> Q) <=> ((?x:A. P) ==> (!x:A. Q))") ITAUT_TAC : IO (Except String thm))
  let TRIV_EXISTS_IMP_THM ← (prove (← pt "!P Q. (?x:A. P ==> Q) <=> ((!x:A. P) ==> (?x:A. Q))") ITAUT_TAC : IO (Except String thm))

  -- Monotonicity theorems for logical operations w.r.t. implication.
  let MONO_AND ← ITAUT "(A ==> B) /\\ (C ==> D) ==> (A /\\ C ==> B /\\ D)"
  let MONO_OR ← ITAUT "(A ==> B) /\\ (C ==> D) ==> (A \\/ C ==> B \\/ D)"
  let MONO_IMP ← ITAUT "(B ==> A) /\\ (C ==> D) ==> ((A ==> C) ==> (B ==> D))"
  let MONO_NOT ← ITAUT "(B ==> A) ==> (~A ==> ~B)"
  let MONO_FORALL ← (prove (← pt "(!x:A. P x ==> Q x) ==> ((!x. P x) ==> (!x. Q x))")
      (THEN (REPEAT STRIP_TAC) (THEN (FIRST_ASSUM MATCH_MP_TAC) (ASM_REWRITE_TAC []))) : IO (Except String thm))
  let MONO_EXISTS ← (prove (← pt "(!x:A. P x ==> Q x) ==> ((?x. P x) ==> (?x. Q x))")
      (THEN DISCH_TAC (THEN (DISCH_THEN (X_CHOOSE_TAC (← pt "x:A")))
        (THEN (EXISTS_TAC (← pt "x:A")) (THEN (FIRST_ASSUM MATCH_MP_TAC) (ASM_REWRITE_TAC [])))))
      : IO (Except String thm))

  -- WLOG + alternative unique existence.
  let ASSUME_TAC := Tactics.ASSUME_TAC B
  let AP_TERM_TAC := Tactics.AP_TERM_TAC B
  let ABS_TAC := Tactics.ABS_TAC B
  let SIMP_TAC := Simp.SIMP_TAC B
  let GEN_REWRITE_TAC := Simp.GEN_REWRITE_TAC B
  let CONJUNCTS_THEN := Tactics.CONJUNCTS_THEN B
  -- SUBST1_TAC o SYM : rewrite using the symmetric equation (SYM runs FIRST).
  let SUBST1_SYM : thm_tactic := SUBST1_TAC oT SYM
  -- A generic "without loss of generality" lemma for symmetry.
  let WLOG_RELATION ← (prove (← pt
      "!R P. (!x y. P x y ==> P y x) /\\ (!x y. R x y \\/ R y x) /\\ (!x y. R x y ==> P x y) ==> !x y:A. P x y")
      (THEN (REPEAT GEN_TAC)
        (THEN (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)))
          (THEN (REPEAT (THEN (MATCH_MP_TAC MONO_FORALL) GEN_TAC))
            (THEN STRIP_TAC (ASM_SIMP_TAC []))))) : IO (Except String thm))
  -- Alternative versions of unique existence.
  let EXISTS_UNIQUE_ALT ← (prove (← pt "!P:A->bool. (?!x. P x) <=> (?x. !y. P y <=> (x = y))")
      (THEN GEN_TAC (THEN (REWRITE_TAC [EXISTS_UNIQUE_THM]) (THENL EQ_TAC
        [THEN (DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← pt "x:A")) ASSUME_TAC))
          (THEN (EXISTS_TAC (← pt "x:A")) (THEN GEN_TAC (THENL EQ_TAC
            [THEN DISCH_TAC (THEN (FIRST_ASSUM MATCH_MP_TAC) (ASM_REWRITE_TAC [])),
             THEN (DISCH_THEN SUBST1_SYM) (FIRST_ASSUM MATCH_ACCEPT_TAC)]))),
         THEN (DISCH_THEN (X_CHOOSE_TAC (← pt "x:A")))
          (THEN (ASM_REWRITE_TAC [(← liftExcept (GSYM EXISTS_REFL))])
            (THEN (REPEAT GEN_TAC)
              (THEN (DISCH_THEN (CONJUNCTS_THEN SUBST1_SYM)) REFL_TAC)))])))
      : IO (Except String thm))
  let iffSplit ← ITAUT "(a <=> b) <=> (a ==> b) /\\ (b ==> a)"
  let EXISTS_UNIQUE ← (prove (← pt "!P:A->bool. (?!x. P x) <=> (?x. P x /\\ !y. P y ==> (y = x))")
      (THEN GEN_TAC
        (THEN (REWRITE_TAC [EXISTS_UNIQUE_ALT])
          (THEN AP_TERM_TAC
            (THEN ABS_TAC
              (THEN (GEN_REWRITE_TAC (fun c => Simp.landConvIO (Simp.binderConvIO c)) [iffSplit])
                (THEN (GEN_REWRITE_TAC (fun c => Simp.landConvIO (Simp.onceDepthConvIO c)) [EQ_SYM_EQ])
                  (THEN (REWRITE_TAC [FORALL_AND_THM])
                    (THEN (SIMP_TAC [])
                      (THEN (REWRITE_TAC [LEFT_FORALL_IMP_THM, EXISTS_REFL])
                        (REWRITE_TAC [CONJ_ACI])))))))))) : IO (Except String thm))

  return { EQ_REFL, REFL_CLAUSE, EQ_SYM, EQ_SYM_EQ, EQ_TRANS, BETA_THM, ABS_SIMP,
           CONJ_ASSOC, CONJ_SYM, CONJ_ACI, DISJ_ASSOC, DISJ_SYM, DISJ_ACI,
           IMP_CONJ, IMP_IMP, IMP_CONJ_ALT, LEFT_OR_DISTRIB, RIGHT_OR_DISTRIB,
           FORALL_SIMP, EXISTS_SIMP, EQ_IMP,
           EQ_CLAUSES, NOT_CLAUSES_WEAK, AND_CLAUSES, OR_CLAUSES, IMP_CLAUSES,
           EXISTS_UNIQUE_THM, EXISTS_REFL, EXISTS_UNIQUE_REFL, UNWIND_THM1, UNWIND_THM2,
           FORALL_UNWIND_THM2, FORALL_UNWIND_THM1, SWAP_FORALL_THM, SWAP_EXISTS_THM,
           FORALL_AND_THM, AND_FORALL_THM, LEFT_AND_FORALL_THM, RIGHT_AND_FORALL_THM,
           EXISTS_OR_THM, OR_EXISTS_THM, LEFT_OR_EXISTS_THM, RIGHT_OR_EXISTS_THM,
           LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM, TRIV_EXISTS_AND_THM,
           LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM, TRIV_AND_EXISTS_THM,
           TRIV_FORALL_OR_THM, TRIV_OR_FORALL_THM, RIGHT_IMP_FORALL_THM, RIGHT_FORALL_IMP_THM,
           LEFT_IMP_EXISTS_THM, LEFT_FORALL_IMP_THM, TRIV_FORALL_IMP_THM, TRIV_EXISTS_IMP_THM,
           MONO_AND, MONO_OR, MONO_IMP, MONO_NOT, MONO_FORALL, MONO_EXISTS,
           WLOG_RELATION, EXISTS_UNIQUE_ALT, EXISTS_UNIQUE }

/- ---------------------------------------------------------------------- -/
/- The following is a common special case of ordered rewriting.           -/
/- ---------------------------------------------------------------------- -/

/-- Associative-commutative normalisation rule (`theorems.ml` `AC`):
    `AC acsuite = EQT_ELIM o PURE_REWRITE_CONV[acsuite; REFL_CLAUSE]`.
    Given an AC-equation `tm`, rewrite it to `T` with the AC suite (plus
    `REFL_CLAUSE`), then `EQT_ELIM`. `REFL_CLAUSE` is passed explicitly (it is a
    `TheoremThms` field). -/
def AC (B : BoolThms) (REFL_CLAUSE : thm) (acsuite : thm) (tm : term) :
    IO (Except String thm) := do
  match ← (Simp.PURE_REWRITE_CONV B [acsuite, REFL_CLAUSE] : IO (Except String ioconv)) with
  | .error e => return .error e
  | .ok cnv =>
    match ← (cnv tm : IO (Except String thm)) with
    | .error e => return .error e
    | .ok eqth => return (B.EQT_ELIM eqth)

/- ======================================================================= -/
/- DESTRUCT_TAC, FIX_TAC, INTRO_TAC and HYP_TAC, giving more brief and       -/
/- elegant ways of naming introduced variables and assumptions (from Marco   -/
/- Maggesi).                                                                 -/
/- Here (plus CLAIM_TAC): a tactic DSL built from parser combinators over    -/
/- lexed tokens.                                                             -/
/- ======================================================================= -/

/-- First-character alpha test for an identifier string. -/
private def isAlphaId (s : String) : Bool :=
  match s.toList with
  | c :: _ => (Printer.charClassifiers.2.2.2.2.1) (String.singleton c)
  | []     => false

/-- First-character alphanumeric test for an identifier string. -/
private def isAlnumId (s : String) : Bool :=
  match s.toList with
  | c :: _ => (Printer.charClassifiers.2.2.2.2.2.2) (String.singleton c)
  | []     => false

/-- Like GEN_TAC but fails instead of generating a primed variant when the
    variable occurs free in the context. -/
def PURE_GEN_TAC (B : BoolThms) : tactic := fun (asl, w) => do
  match dest_forall w with
  | .error _ => return .error "PURE_GEN_TAC"
  | .ok (x, _) =>
    let avoids := itlist (fun (p : String × thm) acc => union (thm_frees p.2) acc) asl (frees w)
    if mem x avoids then return .error "PURE_GEN_TAC"
    else
      -- theorems.ml 425-428: the `try` covers X_GEN_TAC too, so ITS failure is
      -- also reported as "PURE_GEN_TAC".
      match ← (X_GEN_TAC B x (asl, w) : IO (Except String goalstate)) with
      | .ok r => return .ok r
      | .error _ => return .error "PURE_GEN_TAC"

/-- Like X_GEN_TAC but needs only the name of the variable, not the type. -/
def NAME_GEN_TAC (B : BoolThms) (s : String) : tactic := fun gl => do
  match dest_forall gl.2 with
  | .error e => return .error e
  | .ok (v, _) =>
    match dest_var v with
    | .error e => return .error e
    | .ok (_, ty) => (X_GEN_TAC B (mk_var s ty) gl : IO (Except String goalstate))

/-- Choose an existential witness named `v`, then apply `ttac`. -/
def OBTAIN_THEN (B : BoolThms) (v : String) (ttac : thm_tactic) (th : thm) : tactic := fun gl => do
  match dest_exists (concl th) with
  | .error e => return .error e
  | .ok (x, _) =>
    match dest_var x with
    | .error e => return .error e
    | .ok (_, ty) => (X_CHOOSE_THEN B (mk_var v ty) ttac th gl : IO (Except String goalstate))

/-- `CONJ_LIST_TAC [t1; …; tn]`: split conjunctions, applying each tactic to the
    corresponding conjunct. -/
def CONJ_LIST_TAC (B : BoolThms) (tacs : List tactic) : tactic :=
  match end_itlist (fun t1 t2 => THENL B (CONJ_TAC B) [t1, t2]) tacs with
  | .ok t => t
  | .error e => fun _ => return .error e

/-- `NUM_DISJ_TAC n`: select the `n`-th disjunct (1-based) of a disjunction. -/
def NUM_DISJ_TAC (B : BoolThms) (n : Int) : tactic :=
  if n <= 0 then (fun _ => return .error "NUM_DISJ_TAC")
  else THEN B (REPLICATE_TAC B (n - 1).toNat (DISJ2_TAC B)) (REPEAT B (DISJ1_TAC B))

/-- `NAME_PULL_FORALL_CONV s`: pull the universally-quantified variable named
    `s` to the front, commuting past `!`, `==>`, and `/\`. -/
partial def NAME_PULL_FORALL_CONV (B : BoolThms)
    (SWAP_FORALL_THM AND_FORALL_THM RIGHT_IMP_FORALL_THM : thm) (s : String) : ioconv :=
  let SWAP_FORALL_CONV : ioconv := REWR_CONV B SWAP_FORALL_THM
  let AND_FORALL_CONV : ioconv := fun t => do
    match ← (GEN_REWRITE_CONV B id [AND_FORALL_THM] : IO (Except String ioconv)) with
    | .error e => return .error e
    | .ok c => (c t : IO (Except String thm))
  let RIGHT_IMP_FORALL_CONV : ioconv := fun t => do
    match ← (GEN_REWRITE_CONV B id [RIGHT_IMP_FORALL_THM] : IO (Except String ioconv)) with
    | .error e => return .error e
    | .ok c => (c t : IO (Except String thm))
  let rec PULL_FORALL : ioconv := fun tm => do
    if is_forall tm then
      match dest_forall tm with
      | .error e => return .error e
      | .ok (v, _) =>
        if Printer.name_of v == s then return (.ok (REFL tm))
        else (thencIO (binderConvIO PULL_FORALL) SWAP_FORALL_CONV tm : IO (Except String thm))
    else if is_imp tm then
      (thencIO (randConvIO PULL_FORALL) RIGHT_IMP_FORALL_CONV tm : IO (Except String thm))
    else if is_conj tm then
      (thencIO (binopConvIO PULL_FORALL) AND_FORALL_CONV tm : IO (Except String thm))
    else return .error ""   -- `fail ()` (theorems.ml 457): Failure ""
  PULL_FORALL

/-- A token parser matching an `Ident s` satisfying `p`, yielding `s`. -/
private def pa_ident (p : String → Bool) : ParserT lexcode String := fun _ inp =>
  match inp with
  | .Ident s :: rest => if p s then .ok (s, rest) else .error .noparse
  | _ => .error .noparse

private def pa_label : ParserT lexcode String := pa_ident isAlnumId
private def pa_var : ParserT lexcode String := pa_ident isAlphaId

/-- `fix_tac`: parse a FIX pattern into a tactic. -/
def fix_tac (B : BoolThms) (SWAP_FORALL_THM AND_FORALL_THM RIGHT_IMP_FORALL_THM : thm) :
    ParserT lexcode tactic :=
  let npf := NAME_PULL_FORALL_CONV B SWAP_FORALL_THM AND_FORALL_THM RIGHT_IMP_FORALL_THM
  let fix_var (v : String) : tactic := THEN B (CONV_TAC B (npf v)) (PURE_GEN_TAC B)
  let fix_rename : String × List String → tactic
    | (u, [v]) => THEN B (CONV_TAC B (npf v)) (NAME_GEN_TAC B u)
    | (u, _)   => NAME_GEN_TAC B u
  -- pa_rename = "[" var ("/" var)? "]"
  let pa_rename : ParserT lexcode (String × List String) :=
    pmap (pseq (pmap (pseq (pa (.Resword "[")) pa_var) Prod.snd)
               (pmap (pseq (ppossibly (pmap (pseq (pa (.Ident "/")) pa_var) Prod.snd))
                           (pa (.Resword "]"))) Prod.fst))
         id
  let vars : ParserT lexcode tactic :=
    pmap (pmany (por (pmap pa_rename fix_rename) (pmap pa_var fix_var)))
         (fun ts => EVERY B ts)
  let star : ParserT lexcode (List Unit) := ppossibly (pmap (pa (.Ident "*")) (fun _ => ()))
  pmap (pseq vars star)
       (fun (tac, st) => match st with
                         | [] => tac
                         | _  => THEN B tac (REPEAT B (GEN_TAC B)))

/-- `end_itlist` for thm_tacticals, defaulting to a failing thm_tactic on the
    (impossible, non-empty) empty case. -/
private def endThmTac (f : thm_tactic → thm_tactic → thm_tactic) (xs : List thm_tactic) :
    thm_tactic :=
  match end_itlist f xs with
  | .ok t => t
  | .error _ => fun _ _ => return .error "empty destruct pattern"

/-- The DESTRUCT pattern parser: parses a `thm_tactic` continuation. -/
partial def destruct_tac (B : BoolThms) : ParserT lexcode thm_tactic :=
  destruct
where
  -- destruct = disj
  destruct : ParserT lexcode thm_tactic := fun c inp => disj c inp
  -- disj = listof conj "|"  >> end_itlist DISJ_CASES_THEN2
  disj : ParserT lexcode thm_tactic := fun c inp =>
    (pmap (plistof conj (pa (.Resword "|")) "Disjunction")
          (fun ts => endThmTac (DISJ_CASES_THEN2 B) ts)) c inp
  -- conj = atleast 1 atom >> end_itlist CONJUNCTS_THEN2
  conj : ParserT lexcode thm_tactic := fun c inp =>
    (pmap (patleast 1 atom) (fun ts => endThmTac (CONJUNCTS_THEN2 B) ts)) c inp
  -- obtain = ("@" var+ ".") ++ destruct >> uncurry OBTAINL_THEN
  obtain : ParserT lexcode thm_tactic := fun c inp =>
    (pmap (pseq obtain_prfx destruct)
          (fun (vs, d) => (EVERY_TCL (vs.map (OBTAIN_THEN B))) d)) c inp
  obtain_prfx : ParserT lexcode (List String) := fun c inp =>
    (pmap (pseq (pmap (pseq (pa (.Ident "@")) (patleast 1 pa_var)) Prod.snd)
                (pa (.Resword "."))) Prod.fst) c inp
  -- atom = obtain ||| label ||| paren
  atom : ParserT lexcode thm_tactic := fun c inp =>
    (por obtain (por label paren)) c inp
  label : ParserT lexcode thm_tactic := fun _ inp =>
    match inp with
    | .Ident "_" :: res => .ok ((fun _ => ALL_TAC), res)
    | .Ident "+" :: res => .ok (MP_TAC B, res)
    | .Ident s :: res   => if isAlnumId s then .ok (LABEL_TAC B s, res) else .error .noparse
    | _ => .error .noparse
  paren : ParserT lexcode thm_tactic := fun c inp =>
    (pmap (pseq (pmap (pseq (pa (.Resword "(")) destruct) Prod.snd)
                (pa (.Resword ")"))) Prod.fst) c inp

/-- The INTRO pattern parser: parses a `tactic`. -/
partial def intro_tac (B : BoolThms) (SWAP_FORALL_THM AND_FORALL_THM RIGHT_IMP_FORALL_THM : thm) :
    ParserT lexcode tactic :=
  pa_intro
where
  number : ParserT lexcode Int := fun _ inp =>
    match inp with
    | .Ident s :: rest =>
      match s.toInt? with
      | some n => if 1 <= n then .ok (n, rest) else .error .noparse
      | none   => .error .noparse
    | _ => .error .noparse
  pa_fix : ParserT lexcode tactic := fun c inp =>
    (pmap (pseq (pa (.Ident "!")) (fix_tac B SWAP_FORALL_THM AND_FORALL_THM RIGHT_IMP_FORALL_THM))
          Prod.snd) c inp
  pa_dest : ParserT lexcode tactic := fun c inp =>
    (pmap (destruct_tac B) (fun ttac => DISCH_THEN B ttac)) c inp
  pa_prefix : ParserT lexcode (List tactic) := fun c inp =>
    (pelistof (por pa_fix pa_dest) (pa (.Resword ";")) "Prefix intro pattern") c inp
  pa_intro : ParserT lexcode tactic := fun c inp =>
    (pmap (pseq pa_prefix (ppossibly pa_postfix))
          (fun (pfx, post) => EVERY B (pfx ++ post))) c inp
  pa_postfix : ParserT lexcode tactic := fun c inp =>
    (por pa_conj pa_disj) c inp
  pa_conj : ParserT lexcode tactic := fun c inp =>
    (pmap (pseq (pmap (pseq (pa (.Resword "{"))
                            (pmap (plistof pa_intro (pa (.Ident "&")) "Intro pattern")
                                  (fun ts => CONJ_LIST_TAC B ts))) Prod.snd)
                (pa (.Resword "}"))) Prod.fst) c inp
  pa_disj : ParserT lexcode tactic := fun c inp =>
    (pmap (pseq (pmap (pseq (pa (.Ident "#")) (pmap number (fun n => NUM_DISJ_TAC B n))) Prod.snd)
                pa_intro)
          (fun (dtac, itac) => THEN B dtac itac)) c inp

/-- The HYP pattern parser (parameterized by a `rule : thm → thm`). -/
def hyp_tac (B : BoolThms) (rule : thm → Except String thm) : ParserT lexcode tactic :=
  let pa_action : ParserT lexcode (String → thm_tactic → tactic) := fun _ inp =>
    match inp with
    | .Resword ":"  :: rest => .ok (REMOVE_THEN, rest)
    | .Resword "->" :: rest => .ok (USE_THEN, rest)
    | _ => .error .noparse
  -- `tac o rule` : compose the parsed thm_tactic with the rule.  This is exactly
  -- the shared `oT` operator (the rule runs FIRST and its failure is sequenced
  -- inside the produced tactic), so use it rather than a local re-implementation.
  let compRule (tac : thm_tactic) : thm_tactic := tac oT rule
  pmap (pseq pa_label (ppossibly (pseq pa_action (destruct_tac B))))
       (fun (lbl, opt) =>
         match opt with
         | (action, tac) :: _ => action lbl (compRule tac)
         -- `lbl,_ -> REMOVE_THEN lbl (LABEL_TAC lbl o rule)` (theorems.ml 528):
         -- a failing `rule` must fail the tactic, exactly as in the branch
         -- above.
         | [] => REMOVE_THEN lbl (compRule (LABEL_TAC B lbl)))

/-- `(p o lex o explode) s`, then `if rest=[] then r else failwith garbage`:
    lexer and parser failures keep their own messages. -/
private def runDSL (garbage : String) (p : ParserT lexcode α) (s : String) : IO (Except String α) := do
  let c ← mkCtx
  match lex c (explode s) with
  | .error e => return .error (perrMsg e)
  | .ok toks =>
    match p c toks with
    | .error e => return .error (perrMsg e)
    | .ok (r, rest) => if rest.isEmpty then return .ok r
                       else return .error garbage

/-- Parse-and-run bundle: the five DSL entry points, closed over `B` and the
    three quantifier-commuting theorems needed by `fix_tac`. -/
structure DSLThms where
  DESTRUCT_TAC : String → thm_tactic
  FIX_TAC      : String → tactic
  INTRO_TAC    : String → tactic
  HYP_TAC      : String → (thm → Except String thm) → tactic
  CLAIM_TAC    : String → term → tactic

/-- Build the DSL entry points. Errors from parsing surface when the resulting
    tactic runs (as a `.error` goalstate). -/
def setupTacticDSL (B : BoolThms)
    (SWAP_FORALL_THM AND_FORALL_THM RIGHT_IMP_FORALL_THM : thm) : DSLThms :=
  let DESTRUCT_TAC (s : String) : thm_tactic := fun th g => do
    match ← runDSL "Garbage after destruct pattern" (pfix "Destruct pattern" (destruct_tac B)) s with
    | .error e => return .error e
    | .ok ttac => (ttac th g : IO (Except String goalstate))
  let FIX_TAC (s : String) : tactic := fun g => do
    match ← runDSL "FIX_TAC: invalid pattern" (fix_tac B SWAP_FORALL_THM AND_FORALL_THM RIGHT_IMP_FORALL_THM) s with
    | .error e => return .error e
    | .ok tac => (tac g : IO (Except String goalstate))
  let INTRO_TAC (s : String) : tactic := fun g => do
    match ← runDSL "Garbage after intro pattern"
        (pfix "Introduction pattern" (intro_tac B SWAP_FORALL_THM AND_FORALL_THM RIGHT_IMP_FORALL_THM)) s with
    | .error e => return .error e
    | .ok tac => (tac g : IO (Except String goalstate))
  let HYP_TAC (s : String) (rule : thm → Except String thm) : tactic := fun g => do
    match ← runDSL "HYP_TAC: invalid pattern" (hyp_tac B rule) s with
    | .error e => return .error e
    | .ok tac => (tac g : IO (Except String goalstate))
  let CLAIM_TAC (s : String) (tm : term) : tactic := SUBGOAL_THEN B tm (DESTRUCT_TAC s)
  { DESTRUCT_TAC, FIX_TAC, INTRO_TAC, HYP_TAC, CLAIM_TAC }

end HolCore.Theorems
