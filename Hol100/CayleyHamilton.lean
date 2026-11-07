/- File: Hol100/CayleyHamilton.lean
Translation of HOL Light's 100/cayley_hamilton.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionMultiLib.Complexes
import SessionMultiLib.MSum
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Floor SessionLibrary.Wo SessionLibrary.Permutations SessionLibrary.Products SessionLibrary.Iter SessionLibrary.Card SessionLibrary.Matroids SessionMultiLib.Misc SessionMultiLib.Vectors SessionMultiLib.MSum SessionMultiLib.Metric SessionMultiLib.Determinants SessionMultiLib.Topology SessionMultiLib.Convex SessionMultiLib.Complexes
namespace Hol100.CayleyHamilton

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def ms (ths : List thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (MESON ths tm)
private def nc (tm : term) : ExceptT String IO thm := ExceptT.mk (num_CONV tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)

/- ========================================================================= -/
/- The Cayley-Hamilton theorem (for real matrices).                          -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Multivariate/complexes.ml";;
#eval SessionMultiLib.Complexes.ensureComplexes

#eval phrase 2
-- needs "Multivariate/msum.ml";;
#eval SessionMultiLib.MSum.ensureMsum

/- ------------------------------------------------------------------------- -/
/- Powers of a square matrix (mpow).                                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
-- parse_as_infix("mpow",(24,"left"));;
#eval (parse_as_infix ("mpow", (24, "left")) : IO Unit)

#eval phrase 4
def mpow : thm := keep "mpow" fun _ => define
 [[(!A:real^N^N. A mpow 0 = (mat 1 :real^N^N)) /\
   (!A:real^N^N n. A mpow (SUC n) = A ** A mpow n)]]
#eval mpow

#eval phrase 5
def MPOW_ADD : thm := keep "MPOW_ADD" fun _ => (do
  prove ([[!A:real^N^N m n. A mpow (m + n) = A mpow m ** A mpow n]])
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [ADD_CLAUSES, mpow, MATRIX_MUL_LID] THEN
    REWRITE_TAC [MATRIX_MUL_ASSOC])
  : ExceptT String IO thm).run
#eval MPOW_ADD

#eval phrase 6
def MPOW_1 : thm := keep "MPOW_1" fun _ => (do
  let h2 ← nc (← ExceptT.mk [[1]])
  let h1 ← nc (← ExceptT.mk [[1]])
  prove ([[!A:real^N^N. A mpow 1 = A]])
   (REWRITE_TAC [h1, mpow] THEN
    REWRITE_TAC [(← HolLight.SYM h2), MATRIX_MUL_RID])
  : ExceptT String IO thm).run
#eval MPOW_1

#eval phrase 7
def MPOW_SUC : thm := keep "MPOW_SUC" fun _ => (do
  prove ([[!A:real^N^N n. A mpow (SUC n) = A mpow n ** A]])
   (REWRITE_TAC [ADD1, MPOW_ADD, MPOW_1])
  : ExceptT String IO thm).run
#eval MPOW_SUC

/- ------------------------------------------------------------------------- -/
/- The main lemma underlying the proof.                                      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 8
def MATRIC_POLYFUN_EQ_0 : thm := keep "MATRIC_POLYFUN_EQ_0" fun _ => (do
  let h1 ← ms [] (← ExceptT.mk [[(!x i. P i ==> !j. Q j ==> R x i j) <=>
    (!i. P i ==> !j. Q j ==> !x. R x i j)]])
  prove ([[!n A:num->real^N^M.
        (!x. msum(0..n) (\i. x pow i %% A i) = mat 0) <=>
        (!i. i IN 0..n ==> A i = mat 0)]])
   (SIMP_TAC [CART_EQ, MSUM_COMPONENT, MAT_COMPONENT, LAMBDA_BETA,
             FINITE_NUMSEG, COND_ID,
             (← HolLight.ONCE_REWRITE_RULE [REAL_MUL_SYM] MATRIX_CMUL_COMPONENT)] THEN
    REWRITE_TAC [h1] THEN
    REWRITE_TAC [REAL_POLYFUN_EQ_0] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval MATRIC_POLYFUN_EQ_0

#eval phrase 9
def MATRIC_POLY_LEMMA : thm := keep "MATRIC_POLY_LEMMA" fun _ => (do
  let h10 ← ar (← ExceptT.mk [[n - m - 1 = n - SUC m]])
  let h9 ← ar (← ExceptT.mk [[n - m <= SUC n /\ n - m <= n]])
  let h8 ← ar (← ExceptT.mk [[m < n ==> ~(n - m = 0)]])
  let h7 ← ar (← ExceptT.mk [[n - SUC m = n - m \/ m < n]])
  let h6 ← ar (← ExceptT.mk [[~(SUC n <= n)]])
  let h5 ← nc (← ExceptT.mk [[1]])
  let h4 ← ar (← ExceptT.mk [[(0 <= i /\ i <= SUC n) /\ ~(i = 0) <=>
                  1 <= i /\ i <= SUC n]])
  let h3 ← ar (← ExceptT.mk [[(0 <= i /\ i <= SUC n) /\ i <= n <=> 0 <= i /\ i <= n]])
  let h2 ← ar (← ExceptT.mk [[(0 <= i /\ i <= SUC n) /\ i = 0 <=> i = 0]])
  let h1 ← ms [] (← ExceptT.mk [[(if p then mat 0 else x) = (if ~p then x else mat 0)]])
  prove ([[!(A:real^N^N) B (C:real^N^N) n.
        (!x. msum (0..n) (\i. (x pow i) %% B i) ** (A - x %% mat 1) = C)
        ==> C = mat 0]])
   (SIMP_TAC [(← HolLight.GSYM MSUM_MATRIX_RMUL), FINITE_NUMSEG, MATRIX_SUB_LDISTRIB] THEN
    REWRITE_TAC [MATRIX_MUL_RMUL] THEN ONCE_REWRITE_TAC [MATRIX_MUL_LMUL] THEN
    ONCE_REWRITE_TAC [MATRIX_CMUL_ASSOC] THEN
    REWRITE_TAC [(← HolLight.GSYM (← HolLight.CONJUNCT2 real_pow))] THEN
    SIMP_TAC [MSUM_SUB, FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[!x. msum(0..SUC n)
         (\i. x pow i %% (((if i = 0 then (--C:real^N^N) else mat 0) +
                           (if i <= n then B i ** (A:real^N^N) else mat 0)) -
                          (if i = 0 then mat 0 else B(i - 1) ** mat 1))) =
        mat 0]]) MP_TAC THENL
     [SIMP_TAC [MATRIX_CMUL_SUB_LDISTRIB, MSUM_SUB, FINITE_NUMSEG,
               MATRIX_CMUL_ADD_LDISTRIB, MSUM_ADD] THEN
      ONCE_REWRITE_TAC [COND_RAND] THEN REWRITE_TAC [MATRIX_CMUL_RZERO] THEN
      ONCE_REWRITE_TAC [h1] THEN
      REWRITE_TAC [(← HolLight.GSYM MSUM_RESTRICT_SET), IN_NUMSEG] THEN
      REWRITE_TAC [h2,
        h3,
        h4] THEN
      REWRITE_TAC [SING_GSPEC, (← HolLight.GSYM numseg), MSUM_SING, real_pow] THEN
      REWRITE_TAC [MATRIX_CMUL_LID] THEN
      FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.ONCE_DEPTH_CONV [(← HolLight.GSYM th)])) THEN
      REWRITE_TAC [MATRIX_NEG_SUB] THEN REWRITE_TAC [MATRIX_SUB, (← HolLight.AC MATRIX_ADD_AC ([[(((A:real^N^N) + --B) + B) + C = (--B + B) + A + C]]))] THEN
      REWRITE_TAC [MATRIX_ADD_LNEG, MATRIX_ADD_LID] THEN
      REWRITE_TAC [h5] THEN REWRITE_TAC [ADD1, MSUM_OFFSET] THEN
      REWRITE_TAC [ADD_CLAUSES, ADD_SUB, MATRIX_ADD_RNEG],
      REWRITE_TAC [MATRIC_POLYFUN_EQ_0, IN_NUMSEG, LE_0] THEN DISCH_TAC THEN
      SUBGOAL_THEN ([[!i:num. B(n - i) = (mat 0:real^N^N)]]) MP_TAC THENL
       [MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
         [FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[SUC n]])) THEN
          REWRITE_TAC [LE_REFL, SUB_0, NOT_SUC, h6] THEN
          REWRITE_TAC [MATRIX_ADD_LID, SUC_SUB1, MATRIX_MUL_RID] THEN
          REWRITE_TAC [MATRIX_SUB_LZERO, MATRIX_NEG_EQ_0],
          X_GEN_TAC ([[m:num]]) THEN DISCH_TAC THEN
          DISJ_CASES_TAC h7 THEN
          ASM_REWRITE_TAC [] THEN
          FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[n - m:num]])) THEN
          ASM_SIMP_TAC [h8,
                       h9] THEN
          REWRITE_TAC [MATRIX_MUL_LZERO, MATRIX_ADD_LID, MATRIX_SUB_LZERO] THEN
          REWRITE_TAC [MATRIX_MUL_RID, MATRIX_NEG_EQ_0] THEN
          ASM_SIMP_TAC [h10]],
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[n:num]])) THEN REWRITE_TAC [SUB_REFL] THEN
        DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[0]])) THEN
        ASM_REWRITE_TAC [LE_0, MATRIX_MUL_LZERO, MATRIX_ADD_RID] THEN
        REWRITE_TAC [MATRIX_SUB_RZERO, MATRIX_NEG_EQ_0]]])
  : ExceptT String IO thm).run
#eval MATRIC_POLY_LEMMA

/- ------------------------------------------------------------------------- -/
/- Show that cofactor and determinant are n-1 and n degree polynomials.      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 10
def POLYFUN_N_CONST : thm := keep "POLYFUN_N_CONST" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[(0 <= i /\ i <= n) /\ i = 0 <=> i = 0]])
  prove ([[!c n. ?b. !x. c = sum(0..n) (\i. b i * x pow i)]])
   (REPEAT STRIP_TAC THEN
    EXISTS_TAC ([[\i. if i = 0 then c else &0]]) THEN
    REWRITE_TAC [COND_RAND, COND_RATOR, REAL_MUL_LZERO] THEN
    REWRITE_TAC [(← HolLight.GSYM SUM_RESTRICT_SET), IN_NUMSEG] THEN
    REWRITE_TAC [h1] THEN
    REWRITE_TAC [SING_GSPEC, SUM_SING, real_pow, REAL_MUL_RID])
  : ExceptT String IO thm).run
#eval POLYFUN_N_CONST

#eval phrase 11
def POLYFUN_N_ADD : thm := keep "POLYFUN_N_ADD" fun _ => (do
  prove ([[!f g. (?b. !x. f(x) = sum(0..n) (\i. b i * x pow i)) /\
         (?c. !x. g(x) = sum(0..n) (\i. c i * x pow i))
         ==> ?d. !x. f(x) + g(x) = sum(0..n) (\i. d i * x pow i)]])
   (REPEAT STRIP_TAC THEN
    EXISTS_TAC ([[\i. (b:num->real) i + c i]]) THEN
    ASM_REWRITE_TAC [SUM_ADD_NUMSEG, REAL_ADD_RDISTRIB])
  : ExceptT String IO thm).run
#eval POLYFUN_N_ADD

#eval phrase 12
def POLYFUN_N_CMUL : thm := keep "POLYFUN_N_CMUL" fun _ => (do
  prove ([[!f c. (?b. !x. f(x) = sum(0..n) (\i. b i * x pow i))
         ==> ?b. !x. c * f(x) = sum(0..n) (\i. b i * x pow i)]])
   (REPEAT STRIP_TAC THEN
    EXISTS_TAC ([[\i. c * (b:num->real) i]]) THEN
    ASM_REWRITE_TAC [SUM_LMUL, (← HolLight.GSYM REAL_MUL_ASSOC)])
  : ExceptT String IO thm).run
#eval POLYFUN_N_CMUL

#eval phrase 13
def POLYFUN_N_SUM : thm := keep "POLYFUN_N_SUM" fun _ => (do
  prove ([[!f s. FINITE s /\
         (!a. a IN s ==> ?b. !x. f x a = sum(0..n) (\i. b i * x pow i))
         ==> ?b. !x. sum s (f x) = sum(0..n) (\i. b i * x pow i)]])
   (GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [SUM_CLAUSES, FORALL_IN_INSERT, NOT_IN_EMPTY, POLYFUN_N_CONST] THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC POLYFUN_N_ADD THEN ASM_SIMP_TAC [])
  : ExceptT String IO thm).run
#eval POLYFUN_N_SUM

#eval phrase 14
def POLYFUN_N_PRODUCT : thm := keep "POLYFUN_N_PRODUCT" fun _ => (do
  let h2 ← nc (← ExceptT.mk [[1]])
  let h3 ← ms [h2, ADD1] (← ExceptT.mk [[1..SUC n = 0+1..n+1]])
  let h1 ← ar (← ExceptT.mk [[((0 <= i /\ i <= SUC n) /\ i <= n <=> 0 <= i /\ i <= n) /\
    ((0 <= i /\ i <= SUC n) /\ ~(i = 0) <=> 1 <= i /\ i <= SUC n)]])
  prove ([[!f s n. FINITE s /\
           (!a:A. a IN s ==> ?c d. !x. f x a = c + d * x) /\ CARD(s) <= n
           ==> ?b. !x. product s (f x) = sum(0..n) (\i. b i * x pow i)]])
   (GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [PRODUCT_CLAUSES, POLYFUN_N_CONST, FORALL_IN_INSERT] THEN
    REPEAT GEN_TAC THEN DISCH_THEN (fun th => DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN MP_TAC th) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    ASM_SIMP_TAC [CARD_CLAUSES] THEN
    INDUCT_TAC THENL [ARITH_TAC, REWRITE_TAC [LE_SUC]] THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[n:num]])) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_TAC ([[b:num->real]])) THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN ([[c:real]]) (X_CHOOSE_TAC ([[d:real]]))) THEN
    ASM_REWRITE_TAC [] THEN
    EXISTS_TAC ([[\i. (if i <= n then c * b i else &0) +
                  (if ~(i = 0) then d * b(i - 1) else &0)]]) THEN
    X_GEN_TAC ([[x:real]]) THEN
    REWRITE_TAC [REAL_ADD_RDISTRIB, SUM_ADD_NUMSEG] THEN
    REWRITE_TAC [COND_RAND, COND_RATOR, (← HolLight.GSYM SUM_LMUL), REAL_MUL_LZERO] THEN
    REWRITE_TAC [(← HolLight.GSYM SUM_RESTRICT_SET), IN_NUMSEG] THEN
    REWRITE_TAC [h1] THEN
    REWRITE_TAC [(← HolLight.GSYM numseg)] THEN
    REWRITE_TAC [h3] THEN
    REWRITE_TAC [SUM_OFFSET, ADD_SUB, REAL_POW_ADD] THEN
    BINOP_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval POLYFUN_N_PRODUCT

#eval phrase 15
def COFACTOR_ENTRY_AS_POLYFUN : thm := keep "COFACTOR_ENTRY_AS_POLYFUN" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[a - x * d:real = a + (--d) * x]])
  prove ([[!A:real^N^N x i j.
        1 <= i /\ i <= dimindex(:N) /\
        1 <= j /\ j <= dimindex(:N)
        ==> ?c. !x. cofactor(A - x %% mat 1)$i$j =
                    sum(0..dimindex(:N)-1) (\i. c(i) * x pow i)]])
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [cofactor, LAMBDA_BETA, det] THEN
    MATCH_MP_TAC POLYFUN_N_SUM THEN
    SIMP_TAC [FINITE_PERMUTATIONS, FINITE_NUMSEG, FORALL_IN_GSPEC] THEN
    X_GEN_TAC ([[p:num->num]]) THEN DISCH_TAC THEN
    MATCH_MP_TAC POLYFUN_N_CMUL THEN
    SUBGOAL_THEN ([[1..dimindex(:N) = i INSERT ((1..dimindex(:N)) DELETE i)]]) SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_INSERT, IN_DELETE, IN_NUMSEG] THEN ASM_ARITH_TAC,
      SIMP_TAC [PRODUCT_CLAUSES, FINITE_DELETE, FINITE_NUMSEG]] THEN
    ASM_REWRITE_TAC [IN_DELETE, IN_NUMSEG] THEN
    MATCH_MP_TAC POLYFUN_N_CMUL THEN
    MATCH_MP_TAC POLYFUN_N_PRODUCT THEN
    SIMP_TAC [CARD_DELETE, FINITE_DELETE, FINITE_NUMSEG] THEN
    ASM_REWRITE_TAC [IN_NUMSEG, IN_DELETE, CARD_NUMSEG_1, LE_REFL] THEN
    X_GEN_TAC ([[k:num]]) THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[(p:num->num) k IN 1..dimindex(:N)]]) MP_TAC THENL
     [ASM_MESON_TAC [PERMUTES_IN_IMAGE, IN_NUMSEG], ALL_TAC] THEN
    ASM_SIMP_TAC [IN_NUMSEG, LAMBDA_BETA] THEN STRIP_TAC THEN
    ASM_CASES_TAC ([[(p:num->num) k = j]]) THEN ASM_REWRITE_TAC [] THENL
     [REPEAT (EXISTS_TAC ([[&0]])) THEN REAL_ARITH_TAC2, ALL_TAC] THEN
    ASM_SIMP_TAC [MATRIX_SUB_COMPONENT, MATRIX_CMUL_COMPONENT, MAT_COMPONENT] THEN
    REWRITE_TAC [h1] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval COFACTOR_ENTRY_AS_POLYFUN

#eval phrase 16
def DETERMINANT_AS_POLYFUN : thm := keep "DETERMINANT_AS_POLYFUN" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[a - x * d:real = a + (--d) * x]])
  prove ([[!A:real^N^N.
        ?c. !x. det(A - x %% mat 1) =
                sum(0..dimindex(:N)) (\i. c(i) * x pow i)]])
   (GEN_TAC THEN REWRITE_TAC [det] THEN
    MATCH_MP_TAC POLYFUN_N_SUM THEN
    SIMP_TAC [FINITE_PERMUTATIONS, FINITE_NUMSEG, FORALL_IN_GSPEC] THEN
    X_GEN_TAC ([[p:num->num]]) THEN DISCH_TAC THEN
    MATCH_MP_TAC POLYFUN_N_CMUL THEN MATCH_MP_TAC POLYFUN_N_PRODUCT THEN
    SIMP_TAC [FINITE_NUMSEG, CARD_NUMSEG_1, LE_REFL, IN_NUMSEG] THEN
    X_GEN_TAC ([[k:num]]) THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[(p:num->num) k IN 1..dimindex(:N)]]) MP_TAC THENL
     [ASM_MESON_TAC [PERMUTES_IN_IMAGE, IN_NUMSEG], ALL_TAC] THEN
    ASM_SIMP_TAC [IN_NUMSEG, LAMBDA_BETA] THEN STRIP_TAC THEN
    ASM_SIMP_TAC [MATRIX_SUB_COMPONENT, MATRIX_CMUL_COMPONENT, MAT_COMPONENT] THEN
    REWRITE_TAC [h1] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval DETERMINANT_AS_POLYFUN

/- ------------------------------------------------------------------------- -/
/- Hence define characteristic polynomial coefficients.                      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 17
def char_poly : thm := keep "char_poly" fun _ => (do
  ExceptT.mk (Session.new_specification ["char_poly"] (← HolLight.REWRITE_RULE [SKOLEM_THM] DETERMINANT_AS_POLYFUN))
  : ExceptT String IO thm).run
#eval char_poly

/- ------------------------------------------------------------------------- -/
/- Now the Cayley-Hamilton proof.                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 18
def COFACTOR_AS_MATRIC_POLYNOMIAL : thm := keep "COFACTOR_AS_MATRIC_POLYNOMIAL" fun _ => (do
  prove ([[!A:real^N^N. ?C.
      !x. cofactor(A - x %% mat 1) =
          msum(0..dimindex(:N)-1) (\i. x pow i %% C i)]])
   (GEN_TAC THEN SIMP_TAC [CART_EQ, MSUM_COMPONENT, FINITE_NUMSEG] THEN
    MP_TAC (← HolLight.ISPEC ([[A:real^N^N]]) COFACTOR_ENTRY_AS_POLYFUN) THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC [IMP_IMP] THEN REWRITE_TAC [LAMBDA_SKOLEM] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[c:(num->real)^N^N]]) ASSUME_TAC) THEN
    EXISTS_TAC ([[(\i. lambda j k. ((c:(num->real)^N^N)$j$k) i):num->real^N^N]]) THEN
    MAP_EVERY X_GEN_TAC [([[x:real]]), ([[i:num]])] THEN STRIP_TAC THEN
    X_GEN_TAC ([[j:num]]) THEN STRIP_TAC THEN ASM_SIMP_TAC [] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [MATRIX_CMUL_COMPONENT, LAMBDA_BETA] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval COFACTOR_AS_MATRIC_POLYNOMIAL

#eval phrase 19
def MATRIC_POWER_DIFFERENCE : thm := keep "MATRIC_POWER_DIFFERENCE" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[i <= n ==> SUC n - i = SUC(n - i)]])
  prove ([[!A:real^N^N x n.
        A mpow (SUC n) - x pow (SUC n) %% mat 1 =
        msum (0..n) (\i. x pow i %% A mpow (n - i)) ** (A - x %% mat 1)]])
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
     [REWRITE_TAC [MSUM_CLAUSES_NUMSEG, real_pow, SUB_0, mpow] THEN
      REWRITE_TAC [MATRIX_MUL_RID, MATRIX_CMUL_LID, MATRIX_MUL_LID] THEN
      REWRITE_TAC [REAL_MUL_RID],
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC ([[(A mpow SUC n - x pow SUC n %% mat 1) ** A +
      (x pow (SUC n) %% mat 1 :real^N^N) ** (A - x %% mat 1:real^N^N)]]) THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [MPOW_SUC] THEN
        REWRITE_TAC [MATRIX_SUB_RDISTRIB, MATRIX_SUB_LDISTRIB] THEN
        REWRITE_TAC [MATRIX_SUB, MATRIX_MUL_LMUL, MATRIX_MUL_LID] THEN
        REWRITE_TAC [(← HolLight.GSYM MATRIX_ADD_ASSOC)] THEN AP_TERM_TAC THEN
        REWRITE_TAC [MATRIX_ADD_ASSOC, MATRIX_ADD_LNEG, MATRIX_ADD_LID] THEN
        REWRITE_TAC [real_pow, MATRIX_CMUL_ASSOC] THEN REWRITE_TAC [REAL_MUL_AC],
        ASM_REWRITE_TAC [MSUM_CLAUSES_NUMSEG, LE_0] THEN
        REWRITE_TAC [SUB_REFL, mpow, MATRIX_ADD_RDISTRIB] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        SIMP_TAC [(← HolLight.GSYM MSUM_MATRIX_RMUL), FINITE_NUMSEG] THEN
        MATCH_MP_TAC MSUM_EQ THEN REWRITE_TAC [FINITE_NUMSEG] THEN
        X_GEN_TAC ([[i:num]]) THEN REWRITE_TAC [IN_NUMSEG] THEN STRIP_TAC THEN
        ASM_SIMP_TAC [MATRIX_MUL_LMUL] THEN AP_TERM_TAC THEN
        ASM_SIMP_TAC [h1] THEN
        REWRITE_TAC [MPOW_SUC, (← HolLight.GSYM MATRIX_MUL_ASSOC)] THEN AP_TERM_TAC THEN
        REWRITE_TAC [MATRIX_SUB_LDISTRIB, MATRIX_SUB_RDISTRIB] THEN
        REWRITE_TAC [MATRIX_MUL_RMUL, MATRIX_MUL_LMUL] THEN
        REWRITE_TAC [MATRIX_MUL_LID, MATRIX_MUL_RID]]])
  : ExceptT String IO thm).run
#eval MATRIC_POWER_DIFFERENCE

#eval phrase 20
def MATRIC_CHARPOLY_DIFFERENCE : thm := keep "MATRIC_CHARPOLY_DIFFERENCE" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[(0 <= i /\ i <= n) /\ i <= n - 1 <=> 0 <= i /\ i <= n - 1]])
  prove ([[!A:real^N^N. ?B.
      !x. msum(0..dimindex(:N)) (\i. char_poly A i %% A mpow i) -
          sum(0..dimindex(:N)) (\i. char_poly A i * x pow i) %% mat 1 =
          msum(0..(dimindex(:N)-1)) (\i. x pow i %% B i) ** (A - x %% mat 1)]])
   (GEN_TAC THEN SPEC_TAC (([[dimindex(:N)]]), ([[n:num]])) THEN
    SPEC_TAC (([[char_poly(A:real^N^N)]]), ([[c:num->real]])) THEN
    GEN_TAC THEN INDUCT_TAC THEN
    SIMP_TAC [MSUM_CLAUSES_NUMSEG, SUM_CLAUSES_NUMSEG, LE_0] THENL
     [EXISTS_TAC ([[(\i. mat 0):num->real^N^N]]) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [MSUM_CLAUSES_NUMSEG] THEN
      REWRITE_TAC [real_pow, MATRIX_MUL_LMUL, MATRIX_MUL_LZERO, mpow,
                  REAL_MUL_RID, MATRIX_CMUL_RZERO, MATRIX_SUB_REFL],
      FIRST_X_ASSUM (X_CHOOSE_TAC ([[B:num->real^N^N]])) THEN
      REWRITE_TAC [MATRIX_SUB, MATRIX_NEG_ADD, MATRIX_CMUL_ADD_RDISTRIB] THEN
      ONCE_REWRITE_TAC [(← HolLight.AC MATRIX_ADD_AC ([[(A + B) + (C + D):real^N^N = (A + C) + (B + D)]]))] THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM MATRIX_SUB)] THEN
      REWRITE_TAC [(← HolLight.GSYM MATRIX_CMUL_ASSOC), (← HolLight.GSYM MATRIX_CMUL_SUB_LDISTRIB)] THEN
      REWRITE_TAC [MATRIC_POWER_DIFFERENCE, SUC_SUB1] THEN
      EXISTS_TAC ([[(\i. (if i <= n - 1 then B i else mat 0) +
                     c(SUC n) %% A mpow (n - i)):num->real^N^N]]) THEN
      X_GEN_TAC ([[x:real]]) THEN REWRITE_TAC [MATRIX_CMUL_ADD_LDISTRIB] THEN
      SIMP_TAC [MSUM_ADD, FINITE_NUMSEG, MATRIX_ADD_RDISTRIB] THEN
      REWRITE_TAC [(← HolLight.GSYM MATRIX_MUL_LMUL)] THEN
      BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THENL
       [REWRITE_TAC [COND_RAND, COND_RATOR, MATRIX_CMUL_RZERO] THEN
        REWRITE_TAC [(← HolLight.GSYM MSUM_RESTRICT_SET), IN_NUMSEG] THEN
        REWRITE_TAC [numseg, h1],
        SIMP_TAC [(← HolLight.GSYM MSUM_LMUL), FINITE_NUMSEG, MATRIX_CMUL_ASSOC] THEN
        REWRITE_TAC [REAL_MUL_SYM]]])
  : ExceptT String IO thm).run
#eval MATRIC_CHARPOLY_DIFFERENCE

#eval phrase 21
def CAYLEY_HAMILTON : thm := keep "CAYLEY_HAMILTON" fun _ => (do
  let h1 ← ms [] (← ExceptT.mk [[!g. (!x. g x = k) /\ (?a b c. !x. f a b c x = g x)
        ==> ?a b c. !x. f a b c x = k]])
  prove ([[!A:real^N^N. msum(0..dimindex(:N)) (\i. char_poly A i %% A mpow i) = mat 0]])
   (GEN_TAC THEN MATCH_MP_TAC MATRIC_POLY_LEMMA THEN MATCH_MP_TAC h1 THEN
    EXISTS_TAC ([[\x. (msum(0..dimindex(:N)) (\i. char_poly A i %% (A:real^N^N) mpow i) -
         sum(0..dimindex(:N)) (\i. char_poly A i * x pow i) %% mat 1) +
        sum(0..dimindex(:N)) (\i. char_poly A i * x pow i) %% mat 1]]) THEN
    REWRITE_TAC [] THEN CONJ_TAC THENL
     [REWRITE_TAC [MATRIX_SUB, (← HolLight.GSYM MATRIX_ADD_ASSOC), MATRIX_ADD_LNEG] THEN
      REWRITE_TAC [MATRIX_ADD_RID],
      X_CHOOSE_THEN ([[B:num->real^N^N]]) (fun th => ONCE_REWRITE_TAC [th]) (← HolLight.ISPEC ([[A:real^N^N]]) MATRIC_CHARPOLY_DIFFERENCE) THEN
      REWRITE_TAC [(← HolLight.GSYM char_poly), (← HolLight.GSYM MATRIX_MUL_LEFT_COFACTOR)] THEN
      REWRITE_TAC [(← HolLight.GSYM MATRIX_ADD_RDISTRIB)] THEN
      REWRITE_TAC [(← HolLight.GSYM COFACTOR_TRANSP), TRANSP_MATRIX_SUB] THEN
      REWRITE_TAC [TRANSP_MATRIX_CMUL, TRANSP_MAT] THEN
      X_CHOOSE_THEN ([[C:num->real^N^N]]) (fun th => ONCE_REWRITE_TAC [th]) (← HolLight.ISPEC ([[transp A:real^N^N]]) COFACTOR_AS_MATRIC_POLYNOMIAL) THEN
      MAP_EVERY EXISTS_TAC [([[A:real^N^N]]), ([[(\i. B i + C i):num->real^N^N]]), ([[dimindex(:N)-1]])] THEN
      SIMP_TAC [(← HolLight.GSYM MSUM_ADD), FINITE_NUMSEG, MATRIX_CMUL_ADD_LDISTRIB]])
  : ExceptT String IO thm).run
#eval CAYLEY_HAMILTON

end Hol100.CayleyHamilton
