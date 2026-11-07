/- File: Hol100/Lhopital.lean
Translation of HOL Light's 100/lhopital.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Analysis
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionLibrary.Analysis
namespace Hol100.Lhopital

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def rf (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_FIELD tm)

/- ========================================================================= -/
/- #64: L'Hopital's rule.                                                    -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/analysis.ml";;
#eval SessionLibrary.Analysis.ensureAnalysis

#eval phrase 2
-- override_interface ("-->",`(tends_real_real)`);;
#eval (do discard <| override_interface "-->" [[(tends_real_real)]] : IO Unit)

#eval phrase 3
#eval Session.prioritize_real

/- ------------------------------------------------------------------------- -/
/- Cauchy mean value theorem.                                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def MVT2 : thm := keep "MVT2" fun _ => (do
  let o3 ← HolLight.ONCE_REWRITE_RULE [REAL_MUL_SYM] SessionLibrary.Analysis.DIFF_CMUL
  let h1 ← rr (← ExceptT.mk [[(fb * (gb - ga) - gb * (fb - fa)) -
    (fa * (gb - ga) - ga * (fb - fa)) = y <=> y = &0]])
  let o1 ← HolLight.ONCE_REWRITE_RULE [REAL_MUL_SYM] SessionLibrary.Analysis.DIFF_CMUL
  prove ([[!f g a b.
        a < b /\
        (!x. a <= x /\ x <= b ==> f contl x /\ g contl x) /\
        (!x. a < x /\ x < b ==> f differentiable x /\ g differentiable x)
        ==> ?z f' g'. a < z /\ z < b /\ (f diffl f') z /\ (g diffl g') z /\
                      (f b - f a) * g' = (g b - g a) * f']])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [([[\x:real. f(x) * (g(b) - g(a)) - g(x) * (f(b) - f(a))]]),
                  ([[a:real]]), ([[b:real]])] SessionLibrary.Analysis.MVT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [SessionLibrary.Analysis.CONT_SUB, SessionLibrary.Analysis.CONT_MUL, SessionLibrary.Analysis.CONT_CONST] THEN
      X_GEN_TAC ([[x:real]]) THEN DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
      REWRITE_TAC [SessionLibrary.Analysis.differentiable] THEN
      DISCH_THEN (CONJUNCTS_THEN2
       (X_CHOOSE_TAC ([[f':real]])) (X_CHOOSE_TAC ([[g':real]]))) THEN
      EXISTS_TAC ([[f' * (g(b:real) - g a) - g' * (f b - f a)]]) THEN
      ASM_SIMP_TAC [o1, SessionLibrary.Analysis.DIFF_SUB],
      ALL_TAC] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [SWAP_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[z:real]]) THEN
    REWRITE_TAC [h1] THEN
    ASM_SIMP_TAC [REAL_ENTIRE, SessionLibrary.Analysis.REAL_SUB_0, SessionLibrary.Analysis.REAL_LT_IMP_NE] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[l:real]]) STRIP_ASSUME_TAC) THEN
    UNDISCH_THEN ([[l = &0]]) SUBST_ALL_TAC THEN
    UNDISCH_TAC
     ([[!x. a < x /\ x < b ==> f differentiable x /\ g differentiable x]]) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[z:real]])) THEN ASM_REWRITE_TAC [SessionLibrary.Analysis.differentiable] THEN
    DISCH_THEN (CONJUNCTS_THEN2
       (X_CHOOSE_TAC ([[f':real]])) (X_CHOOSE_TAC ([[g':real]]))) THEN
    MAP_EVERY EXISTS_TAC [([[f':real]]), ([[g':real]])] THEN
    ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    CONV_TAC HolLight.SYM_CONV THEN ONCE_REWRITE_TAC [(← HolLight.GSYM SessionLibrary.Analysis.REAL_SUB_0)] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.DIFF_UNIQ THEN
    EXISTS_TAC ([[\x:real. f(x) * (g(b) - g(a)) - g(x) * (f(b) - f(a))]]) THEN
    EXISTS_TAC ([[z:real]]) THEN
    ASM_SIMP_TAC [o3, SessionLibrary.Analysis.DIFF_SUB])
  : ExceptT String IO thm).run
#eval MVT2

/- ------------------------------------------------------------------------- -/
/- First, assume f and g actually take value zero at c.                      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
def LHOPITAL_WEAK : thm := keep "LHOPITAL_WEAK" fun _ => (do
  let h13 ← rr (← ExceptT.mk [[x < z /\ z < c /\ abs(x - c) < d
        ==> &0 < abs(z - c) /\ abs(z - c) < d]])
  let h12 ← rr (← ExceptT.mk [[x <= z /\ z < c /\ z < c /\ abs(x - c) < d
        ==> &0 < abs(z - c) /\ abs(z - c) < d]])
  let h11 ← rr (← ExceptT.mk [[c < z /\ z < x /\ abs(x - c) < d
        ==> &0 < abs(z - c) /\ abs(z - c) < d]])
  let h10 ← rr (← ExceptT.mk [[c < z /\ z <= x /\ abs(x - c) < d
        ==> &0 < abs(z - c) /\ abs(z - c) < d]])
  let h9 ← rr (← ExceptT.mk [[&0 < abs(x - c) ==> c < x \/ x < c]])
  let a8 ← HolLight.ASSUME ([[&0 < abs(x - c)]])
  let h7 ← rf (← ExceptT.mk [[~(gz = &0) /\ ~(gx = &0) /\ fx * gz = fz * gx ==> fz / gz = fx / gx]])
  let h6 ← rr (← ExceptT.mk [[x = y ==> abs(x - l) < e ==> abs(y - l) < e]])
  let h5 ← rr (← ExceptT.mk [[c - d < x /\ x < z /\ z < c
          ==> &0 < abs(z - c) /\ abs(z - c) < d]])
  let h4 ← rr (← ExceptT.mk [[c - d < x /\ x <= z /\ z < c ==> &0 < abs(z - c) /\ abs(z - c) < d]])
  let h3 ← rr (← ExceptT.mk [[c < z /\ z < x /\ x < c + d ==> &0 < abs(z - c) /\ abs(z - c) < d]])
  let h2 ← rr (← ExceptT.mk [[c < z /\ z <= x /\ x < c + d ==> &0 < abs(z - c) /\ abs(z - c) < d]])
  let h1 ← rr (← ExceptT.mk [[&0 < abs(x - c) /\ abs(x - c) < d
      ==> c < x /\ x < c + d \/ c - d < x /\ x < c]])
  prove ([[!f g f' g' c L d.
        &0 < d /\
        (!x. &0 < abs(x - c) /\ abs(x - c) < d
             ==> (f diffl f'(x)) x /\ (g diffl g'(x)) x /\ ~(g'(x) = &0)) /\
        f(c) = &0 /\ g(c) = &0 /\ (f --> &0) c /\ (g --> &0) c /\
        ((\x. f'(x) / g'(x)) --> L) c
        ==> ((\x. f(x) / g(x)) --> L) c]])
   (REPEAT STRIP_TAC THEN SUBGOAL_THEN
     ([[!x. &0 < abs(x - c) /\ abs(x - c) < d
        ==> ?z. &0 < abs(z - c) /\ abs(z - c) < abs(x - c) /\
                f(x) * g'(z) = f'(z) * g(x)]])
    (LABEL_TAC "*") THENL
     [X_GEN_TAC ([[x:real]]) THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP h1) THEN
      STRIP_TAC THENL
       [MP_TAC (← HolLight.SPECL
         [([[f:real->real]]), ([[g:real->real]]), ([[c:real]]), ([[x:real]])] MVT2) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC [] THEN
          GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.BINDER_CONV o HolCore.Lib.funpow 2 HolLight.LAND_CONV)
            [SessionLibrary.Analysis.REAL_LE_LT] THEN
          ASM_MESON_TAC [SessionLibrary.Analysis.CONTL_LIM, SessionLibrary.Analysis.DIFF_CONT, SessionLibrary.Analysis.REAL_LT_IMP_LE, SessionLibrary.Analysis.differentiable, h2],
          ALL_TAC] THEN
        ASM_REWRITE_TAC [SessionLibrary.Analysis.REAL_SUB_RZERO] THEN MATCH_MP_TAC MONO_EXISTS THEN
        GEN_TAC THEN GEN_REWRITE_TAC (HolCore.Lib.funpow 4 HolLight.RAND_CONV) [REAL_MUL_SYM] THEN
        REPEAT STRIP_TAC THENL
         [ASM_REAL_ARITH_TAC,
          ASM_REAL_ARITH_TAC,
          FIRST_X_ASSUM (fun th => MP_TAC th THEN
            MATCH_MP_TAC EQ_IMP THEN BINOP_TAC) THEN
          ASM_MESON_TAC [SessionLibrary.Analysis.DIFF_UNIQ, h3]],
        MP_TAC (← HolLight.SPECL
         [([[f:real->real]]), ([[g:real->real]]), ([[x:real]]), ([[c:real]])] MVT2) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC [] THEN
          GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.BINDER_CONV o HolLight.LAND_CONV o HolLight.RAND_CONV)
            [SessionLibrary.Analysis.REAL_LE_LT] THEN
          ASM_MESON_TAC [SessionLibrary.Analysis.CONTL_LIM, SessionLibrary.Analysis.DIFF_CONT, SessionLibrary.Analysis.REAL_LT_IMP_LE, SessionLibrary.Analysis.differentiable, h4],
          ALL_TAC] THEN
        ASM_REWRITE_TAC [SessionLibrary.Analysis.REAL_SUB_LZERO, REAL_MUL_LNEG, REAL_EQ_NEG2] THEN
        MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
        GEN_REWRITE_TAC (HolCore.Lib.funpow 4 HolLight.RAND_CONV) [REAL_MUL_SYM] THEN
        REPEAT STRIP_TAC THENL
         [ASM_REAL_ARITH_TAC,
          ASM_REAL_ARITH_TAC,
          FIRST_X_ASSUM (fun th => MP_TAC th THEN
           MATCH_MP_TAC EQ_IMP THEN BINOP_TAC) THEN
          ASM_MESON_TAC [SessionLibrary.Analysis.DIFF_UNIQ, h5]]],
      ALL_TAC] THEN
    REWRITE_TAC [SessionLibrary.Analysis.LIM] THEN X_GEN_TAC ([[e:real]]) THEN DISCH_TAC THEN
    UNDISCH_TAC ([[((\x. f' x / g' x) --> L) c]]) THEN REWRITE_TAC [SessionLibrary.Analysis.LIM] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[e:real]])) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[r:real]]) STRIP_ASSUME_TAC) THEN
    MP_TAC (← HolLight.SPECL [([[d:real]]), ([[r:real]])] REAL_DOWN2) THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[k:real]]) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN X_GEN_TAC ([[x:real]]) THEN STRIP_TAC THEN
    UNDISCH_TAC
     ([[!x. &0 < abs(x - c) /\ abs(x - c) < r ==> abs(f' x / g' x - L) < e]]) THEN
    REMOVE_THEN "*" (MP_TAC o HolLight.SPEC ([[x:real]])) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[z:real]]) STRIP_ASSUME_TAC) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[z:real]])) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    MATCH_MP_TAC h6 THEN
    MATCH_MP_TAC h7 THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [ASM_MESON_TAC [REAL_LT_TRANS], ALL_TAC] THEN
    MP_TAC a8 THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP h9) THEN
    REPEAT STRIP_TAC THENL
     [MP_TAC (← HolLight.SPECL [([[g:real->real]]), ([[c:real]]), ([[x:real]])] SessionLibrary.Analysis.ROLLE) THEN
      ASM_REWRITE_TAC [NOT_IMP, (← HolLight.GSYM CONJ_ASSOC)] THEN CONJ_TAC THENL
       [GEN_TAC THEN GEN_REWRITE_TAC (HolCore.Lib.funpow 2 HolLight.LAND_CONV) [SessionLibrary.Analysis.REAL_LE_LT] THEN
        ASM_MESON_TAC [SessionLibrary.Analysis.CONTL_LIM, SessionLibrary.Analysis.DIFF_CONT, REAL_LT_TRANS, h10],
        ALL_TAC] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC [SessionLibrary.Analysis.differentiable, REAL_LT_TRANS, h11],
        ALL_TAC] THEN
      REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC ([[w:real]]) THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[w:real]])) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      ASM_MESON_TAC [SessionLibrary.Analysis.DIFF_UNIQ],
      MP_TAC (← HolLight.SPECL [([[g:real->real]]), ([[x:real]]), ([[c:real]])] SessionLibrary.Analysis.ROLLE) THEN
      ASM_REWRITE_TAC [NOT_IMP, (← HolLight.GSYM CONJ_ASSOC)] THEN CONJ_TAC THENL
       [GEN_TAC THEN GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [SessionLibrary.Analysis.REAL_LE_LT] THEN
        ASM_MESON_TAC [SessionLibrary.Analysis.CONTL_LIM, SessionLibrary.Analysis.DIFF_CONT, REAL_LT_TRANS, h12],
        ALL_TAC] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC [SessionLibrary.Analysis.differentiable, REAL_LT_TRANS, h13],
        ALL_TAC] THEN
      REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC ([[w:real]]) THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[w:real]])) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      ASM_MESON_TAC [SessionLibrary.Analysis.DIFF_UNIQ]])
  : ExceptT String IO thm).run
#eval LHOPITAL_WEAK

/- ------------------------------------------------------------------------- -/
/- Now generalize by continuity extension.                                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 6
def LHOPITAL : thm := keep "LHOPITAL" fun _ => (do
  let h3 ← rr (← ExceptT.mk [[&0 < abs(x - c) /\ &0 < abs z /\ abs z < abs(x - c) ==> ~(x + z = c)]])
  let h2 ← rr (← ExceptT.mk [[&0 < abs(x - c) ==> ~(x = c)]])
  let h1 ← rr (← ExceptT.mk [[&0 < abs(x - c) ==> ~(x = c)]])
  prove ([[!f g f' g' c L d.
        &0 < d /\
        (!x. &0 < abs(x - c) /\ abs(x - c) < d
             ==> (f diffl f'(x)) x /\ (g diffl g'(x)) x /\ ~(g'(x) = &0)) /\
        (f --> &0) c /\ (g --> &0) c /\ ((\x. f'(x) / g'(x)) --> L) c
        ==> ((\x. f(x) / g(x)) --> L) c]])
   (REPEAT GEN_TAC THEN
    MP_TAC (← HolLight.SPECL [([[\x:real. if x = c then &0 else f(x)]]),
                  ([[\x:real. if x = c then &0 else g(x)]]),
                  ([[f':real->real]]), ([[g':real->real]]),
                  ([[c:real]]), ([[L:real]]), ([[d:real]])] LHOPITAL_WEAK) THEN
    SIMP_TAC [SessionLibrary.Analysis.LIM, h1] THEN
    REWRITE_TAC [SessionLibrary.Analysis.diffl] THEN STRIP_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [SessionLibrary.Analysis.diffl] THENL
     [MATCH_MP_TAC SessionLibrary.Analysis.LIM_TRANSFORM THEN EXISTS_TAC ([[\h. (f(x + h) - f x) / h]]),
      MATCH_MP_TAC SessionLibrary.Analysis.LIM_TRANSFORM THEN EXISTS_TAC ([[\h. (g(x + h) - g x) / h]]),
      ASM_MESON_TAC []] THEN
    ASM_SIMP_TAC [h2] THEN
    REWRITE_TAC [SessionLibrary.Analysis.LIM] THEN X_GEN_TAC ([[e:real]]) THEN DISCH_TAC THEN
    EXISTS_TAC ([[abs(x - c)]]) THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_SUB_RZERO] THEN
    ASM_SIMP_TAC [h3] THEN
    ASM_REWRITE_TAC [SessionLibrary.Analysis.REAL_SUB_REFL, REAL_ABS_NUM])
  : ExceptT String IO thm).run
#eval LHOPITAL

end Hol100.Lhopital
