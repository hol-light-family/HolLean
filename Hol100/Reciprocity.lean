/- File: Hol100/Reciprocity.lean
Translation of HOL Light's 100/reciprocity.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Products
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Prime SessionLibrary.Products SessionLibrary.Iter SessionLibrary.Pocklington
namespace Hol100.Reciprocity

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def ng (tm : term) : ExceptT String IO thm := ExceptT.mk (NUM_RING tm)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/- ========================================================================= -/
/- Quadratic reciprocity.                                                    -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/prime.ml";;
#eval SessionLibrary.Prime.ensurePrime

#eval phrase 2
-- needs "Library/pocklington.ml";;
#eval SessionLibrary.Pocklington.ensurePocklington

#eval phrase 3
-- needs "Library/products.ml";;
#eval SessionLibrary.Products.ensureProducts

#eval phrase 4
#eval Session.prioritize_num

/- ------------------------------------------------------------------------- -/
/- Misc. lemmas.                                                             -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
def IN_NUMSEG_1 : thm := keep "IN_NUMSEG_1" fun _ => (do
  prove ([[!p i. i IN 1..p - 1 <=> 0 < i /\ i < p]])
   (REWRITE_TAC [IN_NUMSEG] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval IN_NUMSEG_1

#eval phrase 6
def EVEN_DIV : thm := keep "EVEN_DIV" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[~(2 = 0)]])
  prove ([[!n. EVEN n <=> n = 2 * (n DIV 2)]])
   (GEN_TAC THEN REWRITE_TAC [EVEN_MOD] THEN
    MP_TAC (← HolLight.SPEC ([[n:num]]) (← HolLight.MATCH_MP DIVISION h1)) THEN
    ARITH_TAC)
  : ExceptT String IO thm).run
#eval EVEN_DIV

#eval phrase 7
def CONG_MINUS1_SQUARE : thm := keep "CONG_MINUS1_SQUARE" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[(2 + x) - 1 = x + 1]])
  prove ([[2 <= p ==> ((p - 1) * (p - 1) == 1) (mod p)]])
   (SIMP_TAC [LE_EXISTS, LEFT_IMP_EXISTS_THM] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [cong, nat_mod, h1] THEN
    MAP_EVERY EXISTS_TAC [([[0]]), ([[d:num]])] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval CONG_MINUS1_SQUARE

#eval phrase 8
def CONG_EXP_MINUS1 : thm := keep "CONG_EXP_MINUS1" fun _ => (do
  prove ([[!p n. 2 <= p ==> ((p - 1) EXP n == if EVEN n then 1 else p - 1) (mod p)]])
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    INDUCT_TAC THEN REWRITE_TAC [EXP, ARITH, CONG_REFL] THEN
    MATCH_MP_TAC CONG_TRANS THEN
    EXISTS_TAC ([[(p - 1) * (if EVEN n then 1 else p - 1)]]) THEN
    ASM_SIMP_TAC [CONG_MULT, CONG_REFL, EVEN] THEN
    ASM_CASES_TAC ([[EVEN n]]) THEN
    ASM_SIMP_TAC [MULT_CLAUSES, CONG_REFL, CONG_MINUS1_SQUARE])
  : ExceptT String IO thm).run
#eval CONG_EXP_MINUS1

#eval phrase 9
def NOT_CONG_MINUS1 : thm := keep "NOT_CONG_MINUS1" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[3 <= p ==> (p - 1) + 2 = p + 1]])
  prove ([[!p. 3 <= p ==> ~(p - 1 == 1) (mod p)]])
   (REPEAT STRIP_TAC THEN SUBGOAL_THEN ([[(2 == 0) (mod p)]]) MP_TAC THENL
     [MATCH_MP_TAC CONG_ADD_LCANCEL THEN EXISTS_TAC ([[p - 1]]) THEN
      ONCE_REWRITE_TAC [CONG_SYM] THEN
      ASM_SIMP_TAC [ADD_CLAUSES, h1] THEN
      MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC ([[0 + 1]]) THEN CONJ_TAC THENL
       [ASM_MESON_TAC [ADD_CLAUSES], ALL_TAC] THEN
      MATCH_MP_TAC CONG_ADD THEN
      MESON_TAC [CONG_0, CONG_SYM, DIVIDES_REFL, CONG_REFL],
      REWRITE_TAC [CONG_0] THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP DIVIDES_LE) THEN
      ASM_ARITH_TAC])
  : ExceptT String IO thm).run
#eval NOT_CONG_MINUS1

#eval phrase 10
def CONG_COND_LEMMA : thm := keep "CONG_COND_LEMMA" fun _ => (do
  prove ([[!p x y. 3 <= p /\
           ((if x then 1 else p - 1) == (if y then 1 else p - 1)) (mod p)
           ==> (x <=> y)]])
   (REPEAT GEN_TAC THEN REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    ASM_MESON_TAC [CONG_SYM, NOT_CONG_MINUS1])
  : ExceptT String IO thm).run
#eval CONG_COND_LEMMA

#eval phrase 11
def FINITE_SUBCROSS : thm := keep "FINITE_SUBCROSS" fun _ => (do
  prove ([[!s:A->bool t:B->bool.
       FINITE s /\ FINITE t ==> FINITE {x,y | x IN s /\ y IN t /\ P x y}]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC ([[(s:A->bool) CROSS (t:B->bool)]]) THEN
    ASM_SIMP_TAC [FINITE_CROSS, SUBSET, IN_CROSS, FORALL_PAIR_THM,
                 IN_ELIM_PAIR_THM])
  : ExceptT String IO thm).run
#eval FINITE_SUBCROSS

#eval phrase 12
def CARD_SUBCROSS_DETERMINATE : thm := keep "CARD_SUBCROSS_DETERMINATE" fun _ => (do
  prove ([[FINITE s /\ FINITE t /\ (!x. x IN s /\ p(x) ==> f(x) IN t)
   ==> CARD {(x:A),(y:B) | x IN s /\ y IN t /\ y = f x /\ p x} =
       CARD {x | x IN s /\ p(x)}]])
   (REPEAT STRIP_TAC THEN CONV_TAC HolLight.SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ_EQ THEN EXISTS_TAC ([[\(x:A,y:B). x]]) THEN
    ASM_SIMP_TAC [FINITE_SUBCROSS, FORALL_PAIR_THM, EXISTS_UNIQUE_THM] THEN
    REWRITE_TAC [EXISTS_PAIR_THM, IN_ELIM_PAIR_THM] THEN
    SIMP_TAC [IN_ELIM_THM, PAIR_EQ] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval CARD_SUBCROSS_DETERMINATE

#eval phrase 13
def CARD_SUBCROSS_SWAP : thm := keep "CARD_SUBCROSS_SWAP" fun _ => (do
  prove ([[CARD {y,x | y IN 1..m /\ x IN 1..n /\ P x y} =
   CARD {x,y | x IN 1..n /\ y IN 1..m /\ P x y}]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ_EQ THEN
    EXISTS_TAC ([[\(x:num,y:num). (y,x)]]) THEN
    ASM_SIMP_TAC [FINITE_SUBCROSS, FINITE_NUMSEG] THEN
    REWRITE_TAC [EXISTS_UNIQUE_THM, FORALL_PAIR_THM, EXISTS_PAIR_THM] THEN
    SIMP_TAC [IN_ELIM_PAIR_THM, PAIR_EQ] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval CARD_SUBCROSS_SWAP

/- ------------------------------------------------------------------------- -/
/- What it means to be a quadratic residue. I keep in the "mod p" as what    -/
/- I think is a more intuitive notation.                                     -/
/-                                                                           -/
/- We might explicitly assume that the two numbers are coprime, ruling out   -/
/- the degenerate case of 0 as a quadratic residue. But this seems simpler.  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 14
-- parse_as_infix("is_quadratic_residue",(12,"right"));;
#eval (parse_as_infix ("is_quadratic_residue", (12, "right")) : IO Unit)

#eval phrase 15
def is_quadratic_residue : thm := keep "is_quadratic_residue" fun _ => new_definition
 [[y is_quadratic_residue rel <=> ?x. (x EXP 2 == y) (rel)]]
#eval is_quadratic_residue

/- ------------------------------------------------------------------------- -/
/- Alternative formulation for special cases.                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 16
def IS_QUADRATIC_RESIDUE : thm := keep "IS_QUADRATIC_RESIDUE" fun _ => (do
  prove ([[!a p. ~(p = 0) /\ ~(p divides a)
         ==> (a is_quadratic_residue (mod p) <=>
                 ?x. 0 < x /\ x < p /\ (x EXP 2 == a) (mod p))]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [is_quadratic_residue, EXP_2] THEN
    DISCH_TAC THEN EQ_TAC THENL [ALL_TAC, MESON_TAC []] THEN
    DISCH_THEN (X_CHOOSE_TAC ([[x:num]])) THEN EXISTS_TAC ([[x MOD p]]) THEN
    ASM_SIMP_TAC [DIVISION] THEN CONJ_TAC THENL
     [ASM_MESON_TAC [LT_NZ, (← HolLight.GSYM DIVIDES_MOD), CONG_DIVIDES, DIVIDES_LMUL],
      UNDISCH_TAC ([[(x * x == a) (mod p)]]) THEN
      ASM_SIMP_TAC [CONG, MOD_MULT_MOD2]])
  : ExceptT String IO thm).run
#eval IS_QUADRATIC_RESIDUE

#eval phrase 17
def IS_QUADRATIC_RESIDUE_COMMON : thm := keep "IS_QUADRATIC_RESIDUE_COMMON" fun _ => (do
  prove ([[!a p. prime p /\ coprime(a,p)
         ==> (a is_quadratic_residue (mod p) <=>
                 ?x. 0 < x /\ x < p /\ (x EXP 2 == a) (mod p))]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC IS_QUADRATIC_RESIDUE THEN
    ASM_MESON_TAC [COPRIME_PRIME, DIVIDES_REFL, PRIME_0])
  : ExceptT String IO thm).run
#eval IS_QUADRATIC_RESIDUE_COMMON

/- ------------------------------------------------------------------------- -/
/- Some lemmas about dual pairs; these would be more natural over Z.         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 18
def QUADRATIC_RESIDUE_PAIR_ADD : thm := keep "QUADRATIC_RESIDUE_PAIR_ADD" fun _ => (do
  let h1 ← ng (← ExceptT.mk [[(x + y) EXP 2 = y * (y + 2 * x) + x EXP 2]])
  prove ([[!p x y. prime p
           ==> (((x + y) EXP 2 == x EXP 2) (mod p) <=>
                 p divides y \/ p divides (2 * x + y))]])
   (REWRITE_TAC [h1] THEN
    SIMP_TAC [CONG_ADD_RCANCEL_EQ_0, CONG_0, PRIME_DIVPROD_EQ, ADD_SYM])
  : ExceptT String IO thm).run
#eval QUADRATIC_RESIDUE_PAIR_ADD

#eval phrase 19
def QUADRATIC_RESIDUE_PAIR : thm := keep "QUADRATIC_RESIDUE_PAIR" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[x + x + d = 2 * x + d]])
  prove ([[!p x y. prime p
           ==> ((x EXP 2 == y EXP 2) (mod p) <=>
                 p divides (x + y) \/ p divides (dist(x,y)))]])
   (GEN_TAC THEN MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
     [MESON_TAC [Session.distThms.DIST_SYM, CONG_SYM, ADD_SYM], ALL_TAC] THEN
    REWRITE_TAC [LE_EXISTS] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [CONG_SYM] THEN ASM_SIMP_TAC [QUADRATIC_RESIDUE_PAIR_ADD] THEN
    REWRITE_TAC [Session.distThms.DIST_RADD_0, h1, DISJ_ACI])
  : ExceptT String IO thm).run
#eval QUADRATIC_RESIDUE_PAIR

#eval phrase 20
def IS_QUADRATIC_RESIDUE_PAIR : thm := keep "IS_QUADRATIC_RESIDUE_PAIR" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[x < p ==> x + (p - x) = p]])
  let h1 ← ar (← ExceptT.mk [[0 < x /\ x < p ==> 0 < p - x /\ p - x < p /\ x + (p - x) = p]])
  prove ([[!a p. prime p /\ coprime(a,p)
         ==> (a is_quadratic_residue (mod p) <=>
                 ?x y. 0 < x /\ x < p /\ 0 < y /\ y < p /\ x + y = p /\
                       (x EXP 2 == a) (mod p) /\ (y EXP 2 == a) (mod p) /\
                       !z. 0 < z /\ z < p /\ (z EXP 2 == a) (mod p)
                           ==> z = x \/ z = y)]])
   (SIMP_TAC [IS_QUADRATIC_RESIDUE_COMMON] THEN REPEAT STRIP_TAC THEN
    EQ_TAC THENL [ALL_TAC, MESON_TAC []] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[x:num]]) STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [([[x:num]]), ([[p - x:num]])] THEN
    ASM_SIMP_TAC [h1] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP QUADRATIC_RESIDUE_PAIR) THENL
     [DISCH_THEN (MP_TAC o HolLight.SPECL [([[x:num]]), ([[p - x:num]])]) THEN
      ASM_SIMP_TAC [h2, DIVIDES_REFL] THEN
      ASM_MESON_TAC [CONG_TRANS, CONG_SYM],
      DISCH_THEN (MP_TAC o HolLight.SPECL [([[x:num]]), ([[z:num]])]) THEN
      SUBGOAL_THEN ([[(x EXP 2 == z EXP 2) (mod p)]]) (fun th => SIMP_TAC [th]) THENL
       [ASM_MESON_TAC [CONG_TRANS, CONG_SYM], ALL_TAC] THEN
      DISCH_THEN (DISJ_CASES_THEN (MP_TAC o HolLight.MATCH_MP DIVIDES_CASES)) THEN
      REWRITE_TAC [ADD_EQ_0, Session.distThms.DIST_EQ_0] THEN REWRITE_TAC [Session.distThms.dist] THEN
      ASM_ARITH_TAC])
  : ExceptT String IO thm).run
#eval IS_QUADRATIC_RESIDUE_PAIR

#eval phrase 21
def QUADRATIC_RESIDUE_PAIR_PRODUCT : thm := keep "QUADRATIC_RESIDUE_PAIR_PRODUCT" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[x < p ==> 1 <= p]])
  prove ([[!p x. 0 < x /\ x < p /\ (x EXP 2 == a) (mod p)
         ==> (x * (p - x) == (p - 1) * a) (mod p)]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o HolLight.MP h1) THEN
    SUBGOAL_THEN ([[(x * (p - x) + x EXP 2 == a * (p - 1) + a * 1) (mod p)]]) MP_TAC THENL
     [ASM_SIMP_TAC [LEFT_SUB_DISTRIB, EXP_2, SUB_ADD,
                   LE_MULT_LCANCEL, LT_IMP_LE] THEN
      REWRITE_TAC [cong, nat_mod] THEN ASM_MESON_TAC [ADD_SYM, MULT_SYM],
      REWRITE_TAC [MULT_CLAUSES] THEN
      ASM_MESON_TAC [CONG_ADD, CONG_TRANS, CONG_SYM, CONG_REFL, MULT_SYM,
                    CONG_ADD_RCANCEL]])
  : ExceptT String IO thm).run
#eval QUADRATIC_RESIDUE_PAIR_PRODUCT

/- ------------------------------------------------------------------------- -/
/- Define the Legendre symbol.                                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 22
def legendre : thm := keep "legendre" fun _ => new_definition
 [[(legendre:num#num->int)(a,p) =
        if ~(coprime(a,p)) then &0
        else if a is_quadratic_residue (mod p) then &1
        else --(&1)]]
#eval legendre

/- ------------------------------------------------------------------------- -/
/- Definition of iterated product.                                           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 23
def nproduct : thm := keep "nproduct" fun _ => new_definition
 [[nproduct = iterate ( * )]]
#eval nproduct

#eval phrase 24
def CONG_NPRODUCT : thm := keep "CONG_NPRODUCT" fun _ => (do
  prove ([[!f g s. FINITE s /\ (!x. x IN s ==> (f x == g x) (mod n))
           ==> (nproduct s f == nproduct s g) (mod n)]])
   (REWRITE_TAC [nproduct] THEN
    MATCH_MP_TAC (← HolLight.MATCH_MP ITERATE_RELATED MONOIDAL_MUL) THEN
    SIMP_TAC [CONG_REFL, CONG_MULT])
  : ExceptT String IO thm).run
#eval CONG_NPRODUCT

#eval phrase 25
def NPRODUCT_DELTA_CONST : thm := keep "NPRODUCT_DELTA_CONST" fun _ => (do
  let lemma1 ← prove ([[{x | x IN a INSERT s /\ p(x)} =
     if p(a) then a INSERT {x | x IN s /\ p(x)}
     else {x | x IN s /\ p(x)}]])
     (COND_CASES_TAC THEN ASM_REWRITE_TAC [EXTENSION, IN_INSERT, IN_ELIM_THM] THEN
      ASM_MESON_TAC [])
  let lemma2 ← prove ([[FINITE s ==> FINITE {x | x IN s /\ p(x)}]])
     (MATCH_MP_TAC (← HolLight.ONCE_REWRITE_RULE [(← tt (← ExceptT.mk [[a /\ b ==> c <=> b ==> a ==> c]]))] FINITE_SUBSET) THEN
      SIMP_TAC [SUBSET, IN_ELIM_THM])
  let h1 ← sr (← ExceptT.mk [[{x | F} = {}]])
  prove ([[!c s. FINITE s
         ==> nproduct s (\x. if p(x) then c else 1) =
             c EXP (CARD {x | x IN s /\ p(x)})]])
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [NPRODUCT_CLAUSES, CARD_CLAUSES, EXP, NOT_IN_EMPTY,
             h1, lemma1] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [CARD_CLAUSES, IN_ELIM_THM, lemma2, EXP, MULT_CLAUSES])
  : ExceptT String IO thm).run
#eval NPRODUCT_DELTA_CONST

#eval phrase 26
def COPRIME_NPRODUCT : thm := keep "COPRIME_NPRODUCT" fun _ => (do
  prove ([[!f p s. FINITE s /\ (!x. x IN s ==> coprime(p,f x))
           ==> coprime(p,nproduct s f)]])
   (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [NPRODUCT_CLAUSES, COPRIME_1, IN_INSERT, COPRIME_MUL])
  : ExceptT String IO thm).run
#eval COPRIME_NPRODUCT

/- ------------------------------------------------------------------------- -/
/- Factorial in terms of products.                                           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 27
def FACT_NPRODUCT : thm := keep "FACT_NPRODUCT" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[1 <= SUC n]])
  prove ([[!n. FACT(n) = nproduct(1..n) (\i. i)]])
   (INDUCT_TAC THEN
    REWRITE_TAC [FACT, NUMSEG_CLAUSES, ARITH, NPRODUCT_CLAUSES] THEN
    ASM_SIMP_TAC [h1, NPRODUCT_CLAUSES, FINITE_NUMSEG] THEN
    REWRITE_TAC [IN_NUMSEG] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval FACT_NPRODUCT

/- ------------------------------------------------------------------------- -/
/- General "pairing up" theorem for products.                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 28
def NPRODUCT_PAIRUP_INDUCT : thm := keep "NPRODUCT_PAIRUP_INDUCT" fun _ => (do
  let h3 ← ar (← ExceptT.mk [[~(n = 0) ==> n = SUC(n - 1)]])
  let h2 ← ar (← ExceptT.mk [[~(n = 0) ==> n - 1 < n]])
  let h1 ← ar (← ExceptT.mk [[2 * n = 0 <=> n = 0]])
  prove ([[!f r n s k. s HAS_SIZE (2 * n) /\
               (!x:A. x IN s ==> ?!y. y IN s /\ ~(y = x) /\
                                      (f(x) * f(y) == k) (mod r))
               ==> (nproduct s f == k EXP n) (mod r)]])
   (GEN_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC num_WF THEN X_GEN_TAC ([[n:num]]) THEN DISCH_TAC THEN
    X_GEN_TAC ([[s:A->bool]]) THEN GEN_TAC THEN ASM_CASES_TAC ([[n = 0]]) THENL
     [ASM_SIMP_TAC [MULT_CLAUSES, HAS_SIZE_0, NPRODUCT_CLAUSES, EXP, CONG_REFL],
      ALL_TAC] THEN
    ASM_CASES_TAC ([[s:A->bool = {}]]) THENL
     [ASM_MESON_TAC [HAS_SIZE_0, h1, HAS_SIZE],
      ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM (X_CHOOSE_TAC ([[a:A]]) o
      HolLight.GEN_REWRITE_RULE HolCore.Lib.I [(← HolLight.GSYM MEMBER_NOT_EMPTY)]) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[n - 1]])) THEN
    ASM_SIMP_TAC [h2] THEN
    FIRST_ASSUM (MP_TAC o HolLight.SPEC ([[a:A]])) THEN REWRITE_TAC [(← HolLight.ASSUME ([[(a:A) IN s]]))] THEN
    REWRITE_TAC [EXISTS_UNIQUE] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[b:A]]) STRIP_ASSUME_TAC) THEN
    DISCH_THEN (MP_TAC o HolLight.SPECL [([[(s DELETE a) DELETE (b:A)]]), ([[k:num]])]) THEN
    SUBGOAL_THEN ([[s = (a:A) INSERT (b INSERT (s DELETE a DELETE b))]]) (ASSUME_TAC o HolLight.SYM) THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC ([[(s:A->bool) HAS_SIZE 2 * n]]) THEN
        FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.LAND_CONV) [(← HolLight.SYM th)])) THEN
        SIMP_TAC [HAS_SIZE, FINITE_INSERT, CARD_CLAUSES, FINITE_DELETE,
                 IMP_CONJ, IN_DELETE, IN_INSERT] THEN
        ASM_REWRITE_TAC [] THEN ARITH_TAC,
        ALL_TAC] THEN
      X_GEN_TAC ([[x:A]]) THEN ASM_REWRITE_TAC [IN_DELETE] THEN STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o HolCore.Lib.C HolLight.MATCH_MP (← HolLight.ASSUME ([[(x:A) IN s]]))) THEN
      REWRITE_TAC [EXISTS_UNIQUE] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC ([[y:A]]) THEN STRIP_TAC THEN CONJ_TAC THENL
       [ALL_TAC, ASM_MESON_TAC []] THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
       [ASM_MESON_TAC [MULT_SYM], ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o HolCore.Lib.C HolLight.MATCH_MP (← HolLight.ASSUME ([[(b:A) IN s]]))) THEN
      REWRITE_TAC [EXISTS_UNIQUE_THM] THEN
      DISCH_THEN (MP_TAC o HolLight.SPECL [([[a:A]]), ([[x:A]])] o HolLight.CONJUNCT2) THEN
      ASM_MESON_TAC [MULT_SYM],
      ALL_TAC] THEN
    DISCH_TAC THEN EXPAND_TAC "s" THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.CONJUNCT1 o HolLight.REWRITE_RULE [HAS_SIZE]) THEN
    SIMP_TAC [NPRODUCT_CLAUSES, FINITE_INSERT, FINITE_DELETE] THEN
    REWRITE_TAC [IN_INSERT, IN_DELETE, MULT_CLAUSES] THEN
    FIRST_ASSUM (SUBST1_TAC o HolLight.MATCH_MP h3) THEN
    ASM_REWRITE_TAC [MULT_ASSOC, EXP] THEN DISCH_TAC THEN
    MATCH_MP_TAC CONG_MULT THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval NPRODUCT_PAIRUP_INDUCT

/- ------------------------------------------------------------------------- -/
/- The two cases.                                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 29
def QUADRATIC_NONRESIDUE_FACT : thm := keep "QUADRATIC_NONRESIDUE_FACT" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[~(p = 0) ==> (x <= p - 1 <=> x < p)]])
  let h1 ← ar (← ExceptT.mk [[1 <= x <=> 0 < x]])
  prove ([[!a p. prime p /\ ODD(p) /\
         coprime(a,p) /\ ~(a is_quadratic_residue (mod p))
         ==> (a EXP ((p - 1) DIV 2) == FACT(p - 1)) (mod p)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [FACT_NPRODUCT] THEN
    ONCE_REWRITE_TAC [CONG_SYM] THEN MATCH_MP_TAC NPRODUCT_PAIRUP_INDUCT THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM (CHOOSE_THEN SUBST1_TAC o
        HolLight.GEN_REWRITE_RULE HolCore.Lib.I [ODD_EXISTS]) THEN
      SIMP_TAC [SUC_SUB1, DIV_MULT, ARITH] THEN
      REWRITE_TAC [HAS_SIZE, FINITE_NUMSEG, CARD_NUMSEG, ADD_SUB],
      ALL_TAC] THEN
    ASM_CASES_TAC ([[p = 0]]) THENL [ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN
    ASM_SIMP_TAC [IN_NUMSEG, h1,
                 h2] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [([[a:num]]), ([[p:num]]), ([[x:num]])] CONG_SOLVE_UNIQUE_NONTRIVIAL) THEN
    ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [FUN_EQ_THM] THEN ASM_MESON_TAC [is_quadratic_residue, EXP_2])
  : ExceptT String IO thm).run
#eval QUADRATIC_NONRESIDUE_FACT

#eval phrase 30
def QUADRATIC_RESIDUE_FACT : thm := keep "QUADRATIC_RESIDUE_FACT" fun _ => (do
  let h5 ← ar (← ExceptT.mk [[3 <= p ==> SUC(p - 2) = p - 1]])
  let h4 ← ar (← ExceptT.mk [[3 <= p ==> p - 1 = SUC(p - 2)]])
  let h3 ← ar (← ExceptT.mk [[3 <= p ==> SUC((p - 3) DIV 2) = (p - 1) DIV 2]])
  let h2 ← ar (← ExceptT.mk [[x + y = p ==> p - x = y]])
  let h1 ← ar (← ExceptT.mk [[p - 1 - 1 - 1 = p - 3]])
  prove ([[!a p. prime p /\ ODD(p) /\
         coprime(a,p) /\ a is_quadratic_residue (mod p)
         ==> (a EXP ((p - 1) DIV 2) == FACT(p - 2)) (mod p)]])
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [CONG_SYM] THEN
    SUBGOAL_THEN ([[3 <= p /\ ~(p = 0)]]) STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP PRIME_GE_2) THEN UNDISCH_TAC ([[ODD(p)]]) THEN
      ASM_CASES_TAC ([[p = 2]]) THEN ASM_REWRITE_TAC [ARITH] THEN
      UNDISCH_TAC ([[~(p = 2)]]) THEN ARITH_TAC,
      ALL_TAC] THEN
    UNDISCH_TAC ([[a is_quadratic_residue (mod p)]]) THEN
    ASM_SIMP_TAC [EXP_2, IS_QUADRATIC_RESIDUE_PAIR, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[x:num]]), ([[y:num]])] THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[~(x:num = y)]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [ODD_ADD], ALL_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[\i:num. i]]), ([[p:num]]), ([[(p - 3) DIV 2]]),
     ([[(1..p-1) DELETE x DELETE y]]), ([[a:num]])] NPRODUCT_PAIRUP_INDUCT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [HAS_SIZE, FINITE_DELETE, FINITE_NUMSEG, IN_NUMSEG_1,
                   CARD_DELETE, IN_DELETE, CARD_NUMSEG_1] THEN
      SIMP_TAC [h1] THEN
      ASM_SIMP_TAC [(← HolLight.GSYM EVEN_DIV), EVEN_SUB, ARITH, NOT_EVEN] THEN
      X_GEN_TAC ([[u:num]]) THEN REPEAT STRIP_TAC THEN
      MP_TAC (← HolLight.SPECL [([[a:num]]), ([[p:num]]), ([[u:num]])] CONG_SOLVE_UNIQUE_NONTRIVIAL) THEN
      ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC (HolLight.ONCE_REWRITE_RULE [MULT_SYM]) THEN
      ASM_MESON_TAC [CONG_SOLVE_UNIQUE, PRIME_0, PRIME_COPRIME_LT],
      ALL_TAC] THEN
    MP_TAC (← HolLight.SPECL [([[p:num]]), ([[x:num]])] QUADRATIC_RESIDUE_PAIR_PRODUCT) THEN
    ASM_SIMP_TAC [EXP_2, IMP_IMP, h2] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP CONG_MULT) THEN
    ASM_SIMP_TAC [NPRODUCT_DELETE, (← HolLight.GSYM MULT_ASSOC), IN_DELETE,
                 FINITE_DELETE, IN_NUMSEG_1, FINITE_NUMSEG] THEN
    ASM_SIMP_TAC [(← HolLight.GSYM (← HolLight.CONJUNCT2 EXP)), (← HolLight.GSYM FACT_NPRODUCT), h3] THEN
    ASM_SIMP_TAC [FACT, h4] THEN
    ASM_SIMP_TAC [h5] THEN
    ASM_MESON_TAC [COPRIME_MINUS1, CONG_MULT_LCANCEL, CONG_SYM])
  : ExceptT String IO thm).run
#eval QUADRATIC_RESIDUE_FACT

/- ------------------------------------------------------------------------- -/
/- We immediately get one part of Wilson's theorem.                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 31
def WILSON_LEMMA : thm := keep "WILSON_LEMMA" fun _ => (do
  prove ([[!p. prime(p) ==> (FACT(p - 2) == 1) (mod p)]])
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [CONG_SYM] THEN
    FIRST_ASSUM (DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC o HolLight.MATCH_MP PRIME_ODD) THENL [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC CONG_CONV, ALL_TAC] THEN
    MP_TAC (← HolLight.SPECL [([[1]]), ([[p:num]])] QUADRATIC_RESIDUE_FACT) THEN
    ASM_MESON_TAC [is_quadratic_residue, COPRIME_SYM, COPRIME_1, CONG_REFL,
                  EXP_ONE, CONG_SYM])
  : ExceptT String IO thm).run
#eval WILSON_LEMMA

#eval phrase 32
def WILSON_IMP : thm := keep "WILSON_IMP" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[2 <= p ==> p - 1 = SUC(p - 2)]])
  prove ([[!p. prime(p) ==> (FACT(p - 1) == p - 1) (mod p)]])
   (SIMP_TAC [FACT, PRIME_GE_2, h1] THEN
    MESON_TAC [CONG_MULT, MULT_CLAUSES, WILSON_LEMMA, CONG_REFL])
  : ExceptT String IO thm).run
#eval WILSON_IMP

#eval phrase 33
def WILSON : thm := keep "WILSON" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[~(n = 0) ==> n - 1 + 1 = n]])
  let h1 ← ar (← ExceptT.mk [[x < y ==> x <= y - 1]])
  prove ([[!p. ~(p = 1) ==> (prime p <=> (FACT(p - 1) == p - 1) (mod p))]])
   (X_GEN_TAC ([[n:num]]) THEN DISCH_TAC THEN EQ_TAC THEN SIMP_TAC [WILSON_IMP] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP PRIME_FACTOR) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[p:num]]) STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP DIVIDES_LE) THEN
    ASM_CASES_TAC ([[n = 0]]) THEN ASM_REWRITE_TAC [] THENL
     [ASM_REWRITE_TAC [CONG_MOD_0] THEN CONV_TAC NUM_REDUCE_CONV, ALL_TAC] THEN
    REWRITE_TAC [LE_LT] THEN ASM_CASES_TAC ([[n:num = p]]) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP h1) THEN
    ASM_SIMP_TAC [(← HolLight.GSYM DIVIDES_FACT_PRIME)] THEN
    DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN
    SUBGOAL_THEN ([[p divides FACT(n - 1) <=> p divides (n - 1)]]) SUBST1_TAC THENL
     [MATCH_MP_TAC CONG_DIVIDES THEN
      MATCH_MP_TAC CONG_DIVIDES_MODULUS THEN EXISTS_TAC ([[n:num]]) THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    DISCH_TAC THEN SUBGOAL_THEN ([[p divides 1]]) MP_TAC THENL
     [MATCH_MP_TAC DIVIDES_ADD_REVR THEN EXISTS_TAC ([[n - 1]]) THEN
      ASM_SIMP_TAC [h2],
      REWRITE_TAC [DIVIDES_ONE] THEN ASM_MESON_TAC [PRIME_1]])
  : ExceptT String IO thm).run
#eval WILSON

/- ------------------------------------------------------------------------- -/
/- Using Wilson's theorem we can get the Euler criterion.                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 34
def EULER_CRITERION : thm := keep "EULER_CRITERION" fun _ => (do
  prove ([[!a p. prime p /\ coprime(a,p)
         ==> (a EXP ((p - 1) DIV 2) ==
              (if a is_quadratic_residue (mod p) then 1 else p - 1)) (mod p)]])
   (REPEAT STRIP_TAC THEN FIRST_ASSUM (DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC o
      HolLight.MATCH_MP PRIME_ODD) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC [COND_ID, EXP, CONG_REFL] THEN
    ASM_MESON_TAC [WILSON_LEMMA, WILSON_IMP, CONG_TRANS, CONG_SYM,
                  QUADRATIC_RESIDUE_FACT, QUADRATIC_NONRESIDUE_FACT])
  : ExceptT String IO thm).run
#eval EULER_CRITERION

/- ------------------------------------------------------------------------- -/
/- Gauss's Lemma.                                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 35
def GAUSS_LEMMA_1 : thm := keep "GAUSS_LEMMA_1" fun _ => (do
  let h7 ← ar (← ExceptT.mk [[1 <= i ==> ~(i + j = 0)]])
  let h6 ← ar (← ExceptT.mk [[(if a then x else p - x) = (if b then y else p - y) ==> x < p /\ y < p
    ==> x = y \/ x + y = p]])
  let h5 ← ar (← ExceptT.mk [[i <= r ==> i < 2 * r + 1]])
  let h4 ← ar (← ExceptT.mk [[~(2 * r + 1 <= i /\ i <= r)]])
  let h3 ← ar (← ExceptT.mk [[~(1 <= 0)]])
  let h2 ← ar (← ExceptT.mk [[1 <= x <=> ~(x = 0)]])
  let h1 ← tt (← ExceptT.mk [[a /\ (a ==> b) ==> a /\ b]])
  prove ([[prime p /\ coprime(a,p) /\ 2 * r + 1 = p
   ==> nproduct(1..r) (\x. let b = (a * x) MOD p in
                           if b <= r then b else p - b) =
       nproduct(1..r) (\x. x)]])
   (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP PRIME_IMP_NZ) THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [(← HolLight.SYM (← HolLight.CONJUNCT1 (← HolLight.SPEC_ALL I_O_ID)))] THEN
    REWRITE_TAC [I_DEF] THEN MATCH_MP_TAC NPRODUCT_INJECTION THEN
    REWRITE_TAC [FINITE_NUMSEG] THEN
    ABBREV_TAC ([[f = \x. let b = (a * x) MOD p in
                      if b <= r then b else p - b]]) THEN
    MATCH_MP_TAC h1 THEN CONJ_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "f" THEN REWRITE_TAC [IN_NUMSEG] THEN
      LET_TAC THEN REWRITE_TAC [LET_DEF, LET_END_DEF] THEN REPEAT STRIP_TAC THENL
       [ALL_TAC, EXPAND_TAC "p" THEN ARITH_TAC] THEN
      REWRITE_TAC [h2] THEN COND_CASES_TAC THENL
       [ALL_TAC, ASM_MESON_TAC [DIVISION, NOT_LE, SUB_EQ_0, PRIME_0]] THEN
      EXPAND_TAC "b" THEN ASM_SIMP_TAC [(← HolLight.GSYM DIVIDES_MOD), PRIME_IMP_NZ] THEN
      ASM_SIMP_TAC [PRIME_DIVPROD_EQ] THEN STRIP_TAC THENL
       [ASM_MESON_TAC [coprime, DIVIDES_REFL, PRIME_1],
        ASM_MESON_TAC [DIVIDES_LE, h3,
                      h4]],
      REWRITE_TAC [LET_DEF, LET_END_DEF] THEN DISCH_TAC] THEN
    MAP_EVERY X_GEN_TAC [([[i:num]]), ([[j:num]])] THEN REWRITE_TAC [IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC ([[p:num]]) THEN
    REPEAT (CONJ_TAC THENL
     [ASM_MESON_TAC [h5], ALL_TAC]) THEN
    MATCH_MP_TAC CONG_MULT_LCANCEL THEN EXISTS_TAC ([[a:num]]) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP h6) THEN ASM_SIMP_TAC [DIVISION] THEN
    DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL [ASM_MESON_TAC [CONG], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o HolCore.Lib.C HolLight.AP_THM ([[p:num]]) o HolLight.AP_TERM ([[(MOD)]])) THEN
    ASM_SIMP_TAC [MOD_ADD_MOD] THEN ASM_SIMP_TAC [(← HolLight.GSYM CONG)] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP CONG_DIVIDES) THEN
    ASM_SIMP_TAC [(← HolLight.GSYM LEFT_ADD_DISTRIB), PRIME_DIVPROD_EQ, DIVIDES_REFL] THEN
    STRIP_TAC THENL
     [ASM_MESON_TAC [coprime, DIVIDES_REFL, PRIME_1], ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP DIVIDES_LE) THEN
    ASM_SIMP_TAC [h7] THEN
    MAP_EVERY UNDISCH_TAC [([[i <= r]]), ([[j <= r]]), ([[2 * r + 1 = p]])] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval GAUSS_LEMMA_1

#eval phrase 36
def GAUSS_LEMMA_2 : thm := keep "GAUSS_LEMMA_2" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[2 <= p ==> ~(p = 0)]])
  let h1 ← ar (← ExceptT.mk [[b <= p /\ (1 <= p \/ b = 0) <=> b <= p]])
  prove ([[prime p /\ coprime(a,p) /\ 2 * r + 1 = p
   ==> (nproduct(1..r) (\x. let b = (a * x) MOD p in
                            if b <= r then b else p - b) ==
        (p - 1) EXP (CARD {x | x IN 1..r /\ r < (a * x) MOD p}) *
        a EXP r * nproduct(1..r) (\x. x)) (mod p)]])
   (REPEAT STRIP_TAC THEN
    ABBREV_TAC ([[s = {x | x IN 1..r /\ (a * x) MOD p <= r}]]) THEN
    MATCH_MP_TAC CONG_TRANS THEN
    EXISTS_TAC ([[nproduct(1..r) (\x. (if x IN s then 1 else p - 1) * (a * x) MOD p)]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONG_NPRODUCT THEN REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN
      X_GEN_TAC ([[i:num]]) THEN STRIP_TAC THEN LET_TAC THEN
      EXPAND_TAC "s" THEN REWRITE_TAC [IN_ELIM_THM] THEN
      ASM_REWRITE_TAC [IN_NUMSEG] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [MULT_CLAUSES, CONG_REFL] THEN
      REWRITE_TAC [RIGHT_SUB_DISTRIB] THEN MATCH_MP_TAC CONG_SUB THEN
      ASM_REWRITE_TAC [LE_MULT_RCANCEL, MULT_CLAUSES, CONG_REFL] THEN
      REWRITE_TAC [h1] THEN
      FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP PRIME_GE_2) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[a * i:num]]) o HolLight.MATCH_MP DIVISION o
       HolLight.MATCH_MP h2) THEN
      ASM_SIMP_TAC [LT_IMP_LE, cong, nat_mod] THEN DISCH_THEN ((fun _ => ALL_TAC)) THEN
      MAP_EVERY EXISTS_TAC [([[b:num]]), ([[1]])] THEN ARITH_TAC,
      ALL_TAC] THEN
    ASM_SIMP_TAC [NPRODUCT_MUL, FINITE_NUMSEG] THEN
    MATCH_MP_TAC CONG_MULT THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC [(← HolLight.GSYM COND_SWAP)] THEN
      SIMP_TAC [NPRODUCT_DELTA_CONST, FINITE_NUMSEG] THEN
      MATCH_MP_TAC EQ_IMP_CONG THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      EXPAND_TAC "s" THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
      MESON_TAC [NOT_LT],
      ALL_TAC] THEN
    MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC ([[nproduct(1..r) (\x. a * x)]]) THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC [CONG_MOD, PRIME_IMP_NZ, CONG_NPRODUCT, FINITE_NUMSEG],
      SIMP_TAC [NPRODUCT_MUL, FINITE_NUMSEG, NPRODUCT_CONST, CARD_NUMSEG_1] THEN
      REWRITE_TAC [CONG_REFL]])
  : ExceptT String IO thm).run
#eval GAUSS_LEMMA_2

#eval phrase 37
def GAUSS_LEMMA_3 : thm := keep "GAUSS_LEMMA_3" fun _ => (do
  prove ([[prime p /\ coprime(a,p) /\ 2 * r + 1 = p
   ==> ((p - 1) EXP CARD {x | x IN 1..r /\ r < (a * x) MOD p} *
        (if a is_quadratic_residue mod p then 1 else p - 1) == 1) (mod p)]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC ([[(p - 1) EXP CARD {x | x IN 1..r /\ r < (a * x) MOD p} * a EXP r]]) THEN
    ONCE_REWRITE_TAC [CONG_SYM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONG_MULT THEN REWRITE_TAC [CONG_REFL] THEN
      SUBGOAL_THEN ([[r = (p - 1) DIV 2]]) (fun th => ASM_SIMP_TAC [th, EULER_CRITERION]) THEN
      EXPAND_TAC "p" THEN ARITH_TAC,
      ALL_TAC] THEN
    MATCH_MP_TAC CONG_MULT_RCANCEL THEN
    EXISTS_TAC ([[nproduct (1..r) (\x. x)]]) THEN
    ASM_SIMP_TAC [MULT_CLAUSES, (← HolLight.GSYM MULT_ASSOC),
                 (← ExceptT.mk (Session.SIMP_RULE [GAUSS_LEMMA_1] GAUSS_LEMMA_2))] THEN
    ONCE_REWRITE_TAC [COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_NPRODUCT THEN
    REWRITE_TAC [IN_NUMSEG, FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [COPRIME_SYM] THEN MATCH_MP_TAC PRIME_COPRIME_LT THEN
    ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC)
  : ExceptT String IO thm).run
#eval GAUSS_LEMMA_3

#eval phrase 38
def GAUSS_LEMMA_4 : thm := keep "GAUSS_LEMMA_4" fun _ => (do
  prove ([[prime p /\ coprime(a,p) /\ 2 * r + 1 = p
   ==> ((if EVEN(CARD{x | x IN 1..r /\ r < (a * x) MOD p}) then 1 else p - 1) *
        (if a is_quadratic_residue mod p then 1 else p - 1) == 1) (mod p)]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_TRANS THEN
    EXISTS_TAC ([[(p - 1) EXP CARD {x | x IN 1..r /\ r < (a * x) MOD p} *
              (if a is_quadratic_residue mod p then 1 else p - 1)]]) THEN
    ASM_SIMP_TAC [GAUSS_LEMMA_3] THEN ONCE_REWRITE_TAC [CONG_SYM] THEN
    ASM_SIMP_TAC [CONG_EXP_MINUS1, CONG_MULT, CONG_REFL, PRIME_GE_2])
  : ExceptT String IO thm).run
#eval GAUSS_LEMMA_4

#eval phrase 39
def GAUSS_LEMMA : thm := keep "GAUSS_LEMMA" fun _ => (do
  prove ([[!a p r. prime p /\ coprime(a,p) /\ 2 * r + 1 = p
           ==> (a is_quadratic_residue (mod p) <=>
                EVEN(CARD {x | x IN 1..r /\ r < (a * x) MOD p}))]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC CONG_COND_LEMMA THEN EXISTS_TAC ([[p:num]]) THEN CONJ_TAC THENL
     [FIRST_X_ASSUM (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
      EXPAND_TAC "p" THEN ASM_CASES_TAC ([[r = 0]]) THENL
       [REWRITE_TAC [(← HolLight.ASSUME ([[r = 0]])), ARITH, PRIME_1],
        UNDISCH_TAC ([[~(r = 0)]]) THEN ARITH_TAC],
      FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP GAUSS_LEMMA_4) THEN
      REPEAT (COND_CASES_TAC THEN ASM_SIMP_TAC [CONG_REFL]) THEN
      REWRITE_TAC [MULT_CLAUSES] THEN MESON_TAC [CONG_SYM]])
  : ExceptT String IO thm).run
#eval GAUSS_LEMMA

/- ------------------------------------------------------------------------- -/
/- A more symmetrical version.                                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 40
def GAUSS_LEMMA_SYM : thm := keep "GAUSS_LEMMA_SYM" fun _ => (do
  let h6 ← ar (← ExceptT.mk [[~(x <= y) /\ ~(y + 2 <= x) ==> x = y + 1]])
  let h5 ← ar (← ExceptT.mk [[!p d. 2 * r + 1 = p /\ p * (d + 1) <= (d * p + m) + r ==> r < m]])
  let h4 ← tt (← ExceptT.mk [[a /\ (a ==> b) ==> a /\ b]])
  let h3 ← ar (← ExceptT.mk [[x < y ==> x + 1 <= y]])
  let h2 ← ar (← ExceptT.mk [[(2 * r + 1) * d + r < (2 * s + 1) * r
                    ==> (2 * r) * d < (2 * r) * s]])
  let h1 ← ar (← ExceptT.mk [[1 <= x + 1]])
  prove ([[!p q r s. prime p /\ prime q /\ coprime(p,q) /\
             2 * r + 1 = p /\ 2 * s + 1 = q
             ==> (q is_quadratic_residue (mod p) <=>
                  EVEN(CARD {x,y | x IN 1..r /\ y IN 1..s /\
                                   q * x < p * y /\ p * y <= q * x + r}))]])
   (ONCE_REWRITE_TAC [COPRIME_SYM] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [([[q:num]]), ([[p:num]]), ([[r:num]])] GAUSS_LEMMA) THEN
    ASM_SIMP_TAC [] THEN DISCH_THEN ((fun _ => ALL_TAC)) THEN AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC ([[CARD {x,y | x IN 1..r /\ y IN 1..s /\
                y = (q * x) DIV p + 1 /\ r < (q * x) MOD p}]]) THEN
    CONJ_TAC THENL
     [CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC CARD_SUBCROSS_DETERMINATE THEN
      REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG, h1] THEN
      X_GEN_TAC ([[x:num]]) THEN STRIP_TAC THEN
      SUBGOAL_THEN ([[p * (q * x) DIV p + r < q * r]]) MP_TAC THENL
       [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC ([[q * x]]) THEN
        ASM_REWRITE_TAC [LE_MULT_LCANCEL] THEN
        GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [MULT_SYM] THEN
        ASM_MESON_TAC [PRIME_IMP_NZ, LT_ADD_LCANCEL, DIVISION],
        MAP_EVERY EXPAND_TAC ["p", "q"] THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP h2) THEN
        SIMP_TAC [LT_MULT_LCANCEL, h3]],
      AP_TERM_TAC THEN
      REWRITE_TAC [EXTENSION, IN_ELIM_PAIR_THM, FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [([[x:num]]), ([[y:num]])] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN EQ_TAC THEN DISCH_TAC THENL
       [MP_TAC (← HolLight.MATCH_MP PRIME_IMP_NZ (← HolLight.ASSUME ([[prime p]]))) THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[q * x]]) o HolLight.MATCH_MP DIVISION) THEN
        FIRST_ASSUM (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
        UNDISCH_TAC ([[2 * r + 1 = p]]) THEN ARITH_TAC,
        MATCH_MP_TAC h4 THEN CONJ_TAC THENL
         [ALL_TAC,
          DISCH_THEN SUBST_ALL_TAC THEN
          MATCH_MP_TAC h5 THEN
          MAP_EVERY EXISTS_TAC [([[p:num]]), ([[(q * x) DIV p]])] THEN
          ASM_MESON_TAC [DIVISION, PRIME_IMP_NZ]] THEN
        MATCH_MP_TAC h6 THEN
        REPEAT STRIP_TAC THENL
         [SUBGOAL_THEN ([[y * p <= ((q * x) DIV p) * p]]) MP_TAC THENL
           [ASM_SIMP_TAC [LE_MULT_RCANCEL, PRIME_IMP_NZ], ALL_TAC],
          SUBGOAL_THEN ([[((q * x) DIV p + 2) * p <= y * p]]) MP_TAC THENL
           [ASM_SIMP_TAC [LE_MULT_RCANCEL, PRIME_IMP_NZ], ALL_TAC]] THEN
        MP_TAC (← HolLight.MATCH_MP PRIME_IMP_NZ (← HolLight.ASSUME ([[prime p]]))) THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[q * x]]) o HolLight.MATCH_MP DIVISION) THEN
        ASM_ARITH_TAC]])
  : ExceptT String IO thm).run
#eval GAUSS_LEMMA_SYM

#eval phrase 41
def GAUSS_LEMMA_SYM' : thm := keep "GAUSS_LEMMA_SYM'" fun _ => (do
  prove ([[!p q r s. prime p /\ prime q /\ coprime(p,q) /\
             2 * r + 1 = p /\ 2 * s + 1 = q
             ==> (p is_quadratic_residue (mod q) <=>
                  EVEN(CARD {x,y | x IN 1..r /\ y IN 1..s /\
                                   p * y < q * x /\ q * x <= p * y + s}))]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [([[q:num]]), ([[p:num]]), ([[s:num]]), ([[r:num]])] GAUSS_LEMMA_SYM) THEN
    ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [CARD_SUBCROSS_SWAP] THEN
    AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, FORALL_PAIR_THM] THEN
    REWRITE_TAC [IN_ELIM_PAIR_THM, CONJ_ACI])
  : ExceptT String IO thm).run
#eval GAUSS_LEMMA_SYM'

/- ------------------------------------------------------------------------- -/
/- The main result.                                                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 42
def RECIPROCITY_SET_LEMMA : thm := keep "RECIPROCITY_SET_LEMMA" fun _ => (do
  let h1 ← sr (← ExceptT.mk [[a INTER (b UNION c) = {} <=> a INTER b = {} /\ a INTER c = {}]])
  prove ([[!a b c d r s.
        a UNION b UNION c UNION d = (1..r) CROSS (1..s) /\
        PAIRWISE DISJOINT [a;b;c;d] /\ CARD b = CARD c
        ==> ((EVEN(CARD a) <=> EVEN(CARD d)) <=> ~(ODD r /\ ODD s))]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[CARD(a:num#num->bool) + CARD(b:num#num->bool) +
                CARD(c:num#num->bool) + CARD(d:num#num->bool) = r * s]]) (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.AP_TERM ([[EVEN]]) th) THEN
                ASM_REWRITE_TAC [EVEN_ADD, (← HolLight.GSYM NOT_EVEN), EVEN_MULT] THEN
                CONV_TAC TAUT)) THEN
    SUBGOAL_THEN ([[FINITE(a:num#num->bool) /\ FINITE(b:num#num->bool) /\
    FINITE(c:num#num->bool) /\ FINITE(d:num#num->bool)]]) STRIP_ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC ([[(1..r) CROSS (1..s)]]) THEN
      SIMP_TAC [FINITE_CROSS, FINITE_NUMSEG] THEN
      FIRST_X_ASSUM (SUBST_ALL_TAC o HolLight.SYM) THEN HolLight.ASM SET_TAC [],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.AP_TERM ([[CARD:(num#num->bool)->num]])) THEN
    SIMP_TAC [CARD_CROSS, CARD_NUMSEG_1, FINITE_NUMSEG] THEN
    DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [Session.listDefs.PAIRWISE]) THEN
    REWRITE_TAC [Session.listDefs.PAIRWISE, DISJOINT, Session.listDefs.ALL] THEN
    ASM_SIMP_TAC [CARD_UNION, FINITE_UNION, h1])
  : ExceptT String IO thm).run
#eval RECIPROCITY_SET_LEMMA

#eval phrase 43
def RECIPROCITY_SIMPLE : thm := keep "RECIPROCITY_SIMPLE" fun _ => (do
  let h5 ← ar (← ExceptT.mk [[a + x < y + a <=> x < y]])
  let h4 ← ar (← ExceptT.mk [[x <= r ==> x <= r + 1]])
  let h3 ← ar (← ExceptT.mk [[x <= y /\ v + y + z < x + u ==> (y - x) + z < u - v]])
  let h2 ← ar (← ExceptT.mk [[1 <= x /\ x <= y ==> 1 <= (y + 1) - x /\ (y + 1) - x <= y]])
  let h1 ← ar (← ExceptT.mk [[x <= y ==> (y + 1) - ((y + 1) - x) = x]])
  prove ([[!p q r s.
        prime p /\
        prime q /\
        coprime (p,q) /\
        2 * r + 1 = p /\
        2 * s + 1 = q
        ==> ((q is_quadratic_residue (mod p) <=>
              p is_quadratic_residue (mod q)) <=>
             ~(ODD r /\ ODD s))]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [([[p:num]]), ([[q:num]]), ([[r:num]]), ([[s:num]])] GAUSS_LEMMA_SYM) THEN
    MP_TAC (← HolLight.SPECL [([[p:num]]), ([[q:num]]), ([[r:num]]), ([[s:num]])] GAUSS_LEMMA_SYM') THEN
    ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_REWRITE_TAC [] THEN
    REPEAT (DISCH_THEN SUBST1_TAC) THEN MATCH_MP_TAC RECIPROCITY_SET_LEMMA THEN
    EXISTS_TAC ([[{x,y | x IN 1..r /\ y IN 1..s /\ q * x + r < p * y}]]) THEN
    EXISTS_TAC ([[{x,y | x IN 1..r /\ y IN 1..s /\ p * y + s < q * x}]]) THEN
    REPEAT CONJ_TAC THEN
    REWRITE_TAC [Session.listDefs.PAIRWISE, DISJOINT, EXTENSION, NOT_IN_EMPTY, FORALL_PAIR_THM,
                Session.listDefs.ALL, IN_UNION, IN_CROSS, IN_ELIM_PAIR_THM, IN_INTER] THENL
     [MAP_EVERY X_GEN_TAC [([[x:num]]), ([[y:num]])] THEN
      MAP_EVERY ASM_CASES_TAC [([[x IN 1..r]]), ([[y IN 1..s]])] THEN ASM_SIMP_TAC [] THEN
      SUBGOAL_THEN ([[~(q * x = p * y)]]) (fun th => MP_TAC th THEN ARITH_TAC) THEN
      DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[(divides) p]])) THEN
      ASM_SIMP_TAC [PRIME_DIVPROD_EQ, DIVIDES_REFL] THEN STRIP_TAC THENL
       [ASM_MESON_TAC [DIVIDES_REFL, PRIME_1, coprime], ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP DIVIDES_LE) THEN
      UNDISCH_TAC ([[x IN 1..r]]) THEN REWRITE_TAC [IN_NUMSEG] THEN
      EXPAND_TAC "p" THEN ARITH_TAC,
      ARITH_TAC,
      MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
      REPEAT (EXISTS_TAC ([[\(x,y). (r + 1) - x,(s + 1) - y]])) THEN
      SIMP_TAC [FINITE_SUBCROSS, FINITE_NUMSEG] THEN
      REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_PAIR_THM, IN_NUMSEG, PAIR_EQ] THEN
      CONJ_TAC THEN MAP_EVERY X_GEN_TAC [([[x:num]]), ([[y:num]])] THEN
      SIMP_TAC [h1] THEN
      SIMP_TAC [h2] THEN
      REWRITE_TAC [LEFT_SUB_DISTRIB] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC h3 THEN
      ASM_SIMP_TAC [LE_MULT_LCANCEL, h4] THEN
      REWRITE_TAC [h5] THEN
      REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o HolLight.SYM)) THEN
      ASM_ARITH_TAC])
  : ExceptT String IO thm).run
#eval RECIPROCITY_SIMPLE

/- ------------------------------------------------------------------------- -/
/- In terms of the Legendre symbol.                                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 44
def RECIPROCITY_LEGENDRE : thm := keep "RECIPROCITY_LEGENDRE" fun _ => (do
  let h2 ← tt (← ExceptT.mk [[~(a <=> b) <=> (a <=> ~b)]])
  let h1 ← ar (← ExceptT.mk [[((2 * s + 1) - 1) DIV 2 = s]])
  prove ([[!p q. prime p /\ prime q /\ ODD p /\ ODD q /\ ~(p = q)
         ==> legendre(p,q) * legendre(q,p) =
             --(&1) pow ((p - 1) DIV 2 * (q - 1) DIV 2)]])
   (REPEAT STRIP_TAC THEN MAP_EVERY UNDISCH_TAC [([[ODD q]]), ([[ODD p]])] THEN
    REWRITE_TAC [ODD_EXISTS, LEFT_IMP_EXISTS_THM, RIGHT_IMP_FORALL_THM] THEN
    MAP_EVERY X_GEN_TAC [([[r:num]]), ([[s:num]])] THEN REWRITE_TAC [ADD1] THEN
    REPEAT (DISCH_THEN (fun th => HolLight.tactic_of do
        pure (SUBST1_TAC th THEN ASSUME_TAC (← HolLight.SYM th)))) THEN
    REWRITE_TAC [h1] THEN
    MP_TAC (← HolLight.SPECL [([[p:num]]), ([[q:num]]), ([[r:num]]), ([[s:num]])] RECIPROCITY_SIMPLE) THEN
    ASM_SIMP_TAC [DISTINCT_PRIME_COPRIME, INT_POW_NEG, EVEN_MULT, legendre] THEN
    REWRITE_TAC [DE_MORGAN_THM, NOT_ODD, INT_POW_ONE] THEN
    MAP_EVERY ASM_CASES_TAC [([[EVEN r]]), ([[EVEN s]])] THEN ASM_REWRITE_TAC [] THEN
    SIMP_TAC [h2] THEN DISCH_THEN ((fun _ => ALL_TAC)) THEN
    ASM_CASES_TAC ([[p is_quadratic_residue (mod q)]]) THEN
    ASM_REWRITE_TAC [INT_MUL_LNEG, INT_MUL_RNEG, INT_NEG_NEG, INT_MUL_LID])
  : ExceptT String IO thm).run
#eval RECIPROCITY_LEGENDRE

end Hol100.Reciprocity
