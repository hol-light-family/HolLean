/- File: Hol100/Unsolvability.lean
Translation of HOL Light's 100/unsolvability.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionMultiLib.Cauchy
import SessionLibrary.Galois
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Binomial SessionLibrary.Iter SessionLibrary.Permutations SessionLibrary.Frag SessionLibrary.Prime SessionLibrary.Wo SessionLibrary.Products SessionLibrary.Floor SessionLibrary.Card SessionLibrary.Matroids SessionLibrary.Pocklington SessionMultiLib.Misc SessionLibrary.GroupTheory SessionMultiLib.Vectors SessionLibrary.SymmetricGroup SessionLibrary.RingTheory SessionMultiLib.Metric SessionLibrary.RingDet SessionMultiLib.Determinants SessionLibrary.FieldTheory SessionMultiLib.Homology SessionMultiLib.Topology SessionMultiLib.Convex SessionMultiLib.Complexes SessionLibrary.Galois SessionMultiLib.Paths SessionMultiLib.Polytope SessionMultiLib.Degree SessionMultiLib.Derivatives SessionMultiLib.Integration SessionMultiLib.Measure SessionMultiLib.Canal SessionMultiLib.Transcendentals SessionMultiLib.RealAnalysis SessionMultiLib.MoreTop SessionMultiLib.Cauchy
namespace Hol100.Unsolvability

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
/-- Run an `IO (Except String α)` once, caching under `name` (OCaml's `let`
    evaluates its right-hand side once), for the `let X,Y,Z = e` bindings
    whose result is a tuple. -/
private def keepIO {α : Type} [Inhabited α] (name : String) (f : Unit → IO (Except String α)) : α :=
  keep name fun _ =>
    match runIO (f ()) with
    | .ok (.ok v) => v
    | .ok (.error e) => panic! s!"keepIO {name}: {e}"
    | .error e => panic! s!"keepIO {name}: {e}"
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/- ========================================================================= -/
/- Unsolvability by radicals of a particular quintic: x^5 - 4 * x + 2 = 0.   -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Multivariate/cauchy.ml";;
#eval SessionMultiLib.Cauchy.ensureCauchy

#eval phrase 2
-- needs "Library/galois.ml";;
#eval SessionLibrary.Galois.ensureGalois

#eval phrase 3
#eval (do let _ ← SessionMultiLib.Complexes.prioritize_complex.run : IO Unit)

/- ------------------------------------------------------------------------- -/
/- The polynomial x^5 - 4 * x + 2 is irreducible over the rationals by the   -/
/- Eisenstein criterion and has exactly 3 real roots (sign changes, Rolle),  -/
/- so exactly 2 of its 5 distinct complex roots are not real. Complex        -/
/- conjugation is an automorphism of C over the rationals that swaps these   -/
/- two and fixes the others, so the general corollary                        -/
/- PRIME_TRANSPOSITION_NO_RADICAL_ROOT_SPLITS of Library/galois.ml (prime    -/
/- degree at least 5, the Galois group is the full symmetric group) applies. -/
/- ------------------------------------------------------------------------- -/
/- ------------------------------------------------------------------------- -/
/- The field of complex numbers as a ring. The definition is the same as in  -/
/- 100/transcendence.ml, so loading both files is a benign redefinition.     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def complex_ring : thm := keep "complex_ring" fun _ => new_definition
 [[complex_ring = ring((:complex),Cx(&0),Cx(&1),( -- ),( + ),( * ))]]
#eval complex_ring

#eval phrase 5
def COMPLEX_RING_CLAUSES : thm := keep "COMPLEX_RING_CLAUSES" fun _ => (do
  prove ([[ring_carrier complex_ring = (:complex) /\
   ring_0 complex_ring = Cx(&0) /\
   ring_1 complex_ring = Cx(&1) /\
   ring_neg complex_ring = ( -- ) /\
   ring_add complex_ring = ( + ) /\
   ring_mul complex_ring = ( * )]])
   (PURE_REWRITE_TAC [(← HolLight.GSYM PAIR_EQ), ring_carrier, ring_0, ring_1, ring_neg, ring_add, ring_mul,
      BETA_THM, PAIR] THEN
    PURE_REWRITE_TAC [complex_ring, (← HolLight.GSYM (← HolLight.CONJUNCT2 ring_tybij))] THEN
    REWRITE_TAC [IN_UNIV] THEN CONV_TAC COMPLEX_RING)
  : ExceptT String IO thm).run
#eval COMPLEX_RING_CLAUSES

#eval phrase 6
def FIELD_COMPLEX_RING : thm := keep "FIELD_COMPLEX_RING" fun _ => (do
  prove ([[field complex_ring]])
   (REWRITE_TAC [field, COMPLEX_RING_CLAUSES, IN_UNIV, CX_INJ] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN MESON_TAC [COMPLEX_MUL_RINV])
  : ExceptT String IO thm).run
#eval FIELD_COMPLEX_RING

#eval phrase 7
def COMPLEX_RING_OF_NUM : thm := keep "COMPLEX_RING_OF_NUM" fun _ => (do
  prove ([[ring_of_num complex_ring = \n. Cx(&n)]])
   (REWRITE_TAC [FUN_EQ_THM] THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [ring_of_num, COMPLEX_RING_CLAUSES, (← HolLight.GSYM REAL_OF_NUM_SUC),
                    CX_ADD])
  : ExceptT String IO thm).run
#eval COMPLEX_RING_OF_NUM

#eval phrase 8
def COMPLEX_RING_OF_INT : thm := keep "COMPLEX_RING_OF_INT" fun _ => (do
  prove ([[ring_of_int complex_ring = \n. Cx(real_of_int n)]])
   (REWRITE_TAC [FUN_EQ_THM, RING_OF_INT_CASES, FORALL_INT_CASES] THEN
    REWRITE_TAC [int_neg_th, int_of_num_th, COMPLEX_RING_OF_NUM] THEN
    REWRITE_TAC [COMPLEX_RING_CLAUSES, CX_NEG])
  : ExceptT String IO thm).run
#eval COMPLEX_RING_OF_INT

#eval phrase 9
def COMPLEX_RING_CHAR : thm := keep "COMPLEX_RING_CHAR" fun _ => (do
  prove ([[ring_char complex_ring = 0]])
   (REWRITE_TAC [RING_CHAR_EQ_0, COMPLEX_RING_OF_NUM, COMPLEX_RING_CLAUSES,
                CX_INJ, REAL_OF_NUM_EQ])
  : ExceptT String IO thm).run
#eval COMPLEX_RING_CHAR

#eval phrase 10
def COMPLEX_RING_INV : thm := keep "COMPLEX_RING_INV" fun _ => (do
  prove ([[ring_inv complex_ring = inv]])
   (REWRITE_TAC [FUN_EQ_THM, ring_inv, COMPLEX_RING_CLAUSES] THEN
    SIMP_TAC [FIELD_UNIT, FIELD_COMPLEX_RING, COMPLEX_RING_CLAUSES,
             IN_UNIV, COND_SWAP] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [COMPLEX_INV_0] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN POP_ASSUM MP_TAC THEN
    CONV_TAC COMPLEX_FIELD)
  : ExceptT String IO thm).run
#eval COMPLEX_RING_INV

#eval phrase 11
def COMPLEX_RING_POW : thm := keep "COMPLEX_RING_POW" fun _ => (do
  prove ([[ring_pow complex_ring = (pow)]])
   (REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [ring_pow, complex_pow, COMPLEX_RING_CLAUSES])
  : ExceptT String IO thm).run
#eval COMPLEX_RING_POW

#eval phrase 12
def COMPLEX_RING_SUM : thm := keep "COMPLEX_RING_SUM" fun _ => (do
  prove ([[!s (f:A->complex). FINITE s ==> ring_sum complex_ring s f = vsum s f]])
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [RING_SUM_CLAUSES, VSUM_CLAUSES, COMPLEX_RING_CLAUSES, IN_UNIV,
             COMPLEX_VEC_0])
  : ExceptT String IO thm).run
#eval COMPLEX_RING_SUM

#eval phrase 13
def POLY_EVAL_COMPLEX_RING : thm := keep "POLY_EVAL_COMPLEX_RING" fun _ => (do
  prove ([[!p z. p IN ring_carrier(poly_ring complex_ring (:1))
         ==> poly_eval complex_ring p z =
             vsum(0..poly_deg complex_ring p) (\i. coeff i p * z pow i)]])
   (SIMP_TAC [POLY_EVAL_EXPAND, COMPLEX_RING_CLAUSES, IN_UNIV,
             COMPLEX_RING_SUM, FINITE_NUMSEG, COMPLEX_RING_POW])
  : ExceptT String IO thm).run
#eval POLY_EVAL_COMPLEX_RING

#eval phrase 14
def ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING : thm := keep "ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING" fun _ => (do
  prove ([[algebraically_closed_field complex_ring]])
   (REWRITE_TAC [algebraically_closed_field, FIELD_COMPLEX_RING] THEN
    X_GEN_TAC ([[p:(1->num)->complex]]) THEN STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[complex_ring]]), ([[p:(1->num)->complex]])] POLY_TOP_NONZERO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
      UNDISCH_TAC ([[~(poly_deg complex_ring (p:(1->num)->complex) = 0)]]) THEN
      ASM_REWRITE_TAC [POLY_RING_CLAUSES, POLY_DEG_0],
      REWRITE_TAC [COMPLEX_RING_CLAUSES] THEN DISCH_TAC] THEN
    ASM_SIMP_TAC [POLY_EVAL_COMPLEX_RING, COMPLEX_RING_CLAUSES, IN_UNIV] THEN
    MP_TAC (← HolLight.ISPECL [([[\i. coeff i (p:(1->num)->complex)]]),
                   ([[poly_deg complex_ring (p:(1->num)->complex)]])] FTA) THEN
    REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN DISJ2_TAC THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[poly_deg complex_ring (p:(1->num)->complex)]])) THEN
    ASM_SIMP_TAC [IN_NUMSEG, LE_REFL, LE_1])
  : ExceptT String IO thm).run
#eval ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING

#eval phrase 15
def RING_AUTOMORPHISM_CNJ : thm := keep "RING_AUTOMORPHISM_CNJ" fun _ => (do
  prove ([[ring_automorphism complex_ring cnj]])
   (REWRITE_TAC [ring_automorphism, ring_isomorphism, ring_isomorphisms] THEN
    EXISTS_TAC ([[cnj]]) THEN
    REWRITE_TAC [ring_homomorphism, COMPLEX_RING_CLAUSES, SUBSET_UNIV,
                IN_UNIV] THEN
    REWRITE_TAC [CNJ_NEG, CNJ_ADD, CNJ_MUL, CNJ_CX, CNJ_CNJ])
  : ExceptT String IO thm).run
#eval RING_AUTOMORPHISM_CNJ

#eval phrase 16
def PERMUTES_CNJ : thm := keep "PERMUTES_CNJ" fun _ => (do
  prove ([[cnj permutes (:complex)]])
   (REWRITE_TAC [PERMUTES_UNIV] THEN MESON_TAC [CNJ_CNJ])
  : ExceptT String IO thm).run
#eval PERMUTES_CNJ

/- ------------------------------------------------------------------------- -/
/- In characteristic zero an irreducible polynomial has as many roots as its -/
/- degree in any extension where it splits, for example in C.                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 17
def POLY_SPLITS_OVER_ALGEBRAICALLY_CLOSED_FIELD : thm := keep "POLY_SPLITS_OVER_ALGEBRAICALLY_CLOSED_FIELD" fun _ => (do
  prove ([[!(h:A->B) k l p.
        field_extension (k,l) h /\ algebraically_closed_field l /\
        p IN ring_carrier(poly_ring k (:1))
        ==> poly_splits_over (k,l) h p]])
   (REWRITE_TAC [field_extension, poly_splits_over] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ALGEBRAICALLY_CLOSED_FIELD_POLY_SPLITS THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC ([[k:A ring]]) THEN ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM])
  : ExceptT String IO thm).run
#eval POLY_SPLITS_OVER_ALGEBRAICALLY_CLOSED_FIELD

#eval phrase 18
def POLY_SPLITS_OVER_IRREDUCIBLE_ROOT_COUNT : thm := keep "POLY_SPLITS_OVER_IRREDUCIBLE_ROOT_COUNT" fun _ => (do
  prove ([[!(h:A->B) k l p.
        field_extension (k,l) h /\ ring_char k = 0 /\
        ring_irreducible (poly_ring k (:1)) p /\ poly_splits_over (k,l) h p
        ==> {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l}
            HAS_SIZE poly_deg k p]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [ring_irreducible]) THEN
    REWRITE_TAC [HAS_SIZE] THEN CONJ_TAC THENL
     [MP_TAC (← HolLight.ISPECL [([[h:A->B]]), ([[k:A ring]]), ([[l:B ring]]), ([[p:(1->num)->A]])] POLY_ROOT_BOUND_EXTENSION) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [ASM_MESON_TAC [POLY_RING_CLAUSES], SIMP_TAC []],
      MATCH_MP_TAC POLY_SPLITS_OVER_SEPARABLE_ROOT_COUNT THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC POLY_IRREDUCIBLE_IMP_SEPARABLE THEN
      ASM_MESON_TAC [field_extension]])
  : ExceptT String IO thm).run
#eval POLY_SPLITS_OVER_IRREDUCIBLE_ROOT_COUNT

#eval phrase 19
def RING_CHAR_FIELD_EXTENSION_COMPLEX_RING : thm := keep "RING_CHAR_FIELD_EXTENSION_COMPLEX_RING" fun _ => (do
  prove ([[!(h:A->complex) k. field_extension (k,complex_ring) h ==> ring_char k = 0]])
   (REWRITE_TAC [field_extension] THEN
    MESON_TAC [RING_CHAR_MONOMORPHIC_IMAGE, COMPLEX_RING_CHAR])
  : ExceptT String IO thm).run
#eval RING_CHAR_FIELD_EXTENSION_COMPLEX_RING

#eval phrase 20
def COMPLEX_ROOTS_IRREDUCIBLE : thm := keep "COMPLEX_ROOTS_IRREDUCIBLE" fun _ => (do
  prove ([[!(h:A->complex) k p.
        field_extension (k,complex_ring) h /\
        ring_irreducible (poly_ring k (:1)) p
        ==> {z | poly_eval complex_ring (h o p) z = Cx(&0)} HAS_SIZE
            poly_deg k p]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP RING_CHAR_FIELD_EXTENSION_COMPLEX_RING) THEN
    MP_TAC (← HolLight.ISPECL [([[h:A->complex]]), ([[k:A ring]]), ([[complex_ring]]), ([[p:(1->num)->A]])] POLY_SPLITS_OVER_IRREDUCIBLE_ROOT_COUNT) THEN
    ASM_SIMP_TAC [POLY_SPLITS_OVER_ALGEBRAICALLY_CLOSED_FIELD,
                 ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING,
                 RING_IRREDUCIBLE_IN_CARRIER] THEN
    REWRITE_TAC [COMPLEX_RING_CLAUSES, IN_UNIV])
  : ExceptT String IO thm).run
#eval COMPLEX_ROOTS_IRREDUCIBLE

/- ------------------------------------------------------------------------- -/
/- Complex numbers expressible by radicals: generated from 0 and 1 by the    -/
/- field operations and the extraction of n-th roots. Over any field k       -/
/- embedded in C they are radical elements in the sense of galois.ml.        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 21
-- let radical_number_RULES,radical_number_INDUCT,radical_number_CASES = new_inductive_definition ...
def radical_number_RULES_defs : thm × thm × thm :=
  keepIO "radical_number_RULES_defs" fun _ => new_inductive_definition
  [[radical_number(Cx(&0)) /\
  radical_number(Cx(&1)) /\
  (!x y. radical_number x /\ radical_number y ==> radical_number(x + y)) /\
  (!x y. radical_number x /\ radical_number y ==> radical_number(x * y)) /\
  (!x. radical_number x ==> radical_number(--x)) /\
  (!x. radical_number x /\ ~(x = Cx(&0)) ==> radical_number(inv x)) /\
  (!x n. radical_number(x pow n) /\ 1 <= n ==> radical_number x)]]
def radical_number_RULES : thm := radical_number_RULES_defs.1
def radical_number_INDUCT : thm := radical_number_RULES_defs.2.1
def radical_number_CASES : thm := radical_number_RULES_defs.2.2
#eval do IO.println (repr radical_number_RULES); IO.println (repr radical_number_INDUCT); IO.println (repr radical_number_CASES)

#eval phrase 22
def RADICAL_NUMBER_IMP_RADICAL_ELEMENT : thm := keep "RADICAL_NUMBER_IMP_RADICAL_ELEMENT" fun _ => (do
  prove ([[!(h:A->complex) k z.
        field_extension(k,complex_ring) h /\ radical_number z
        ==> radical_element (k,complex_ring) h z]])
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    SPEC_TAC (([[z:complex]]), ([[z:complex]])) THEN
    MATCH_MP_TAC radical_number_INDUCT THEN
    FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM o
      HolLight.CONJUNCT2 o HolLight.CONJUNCT2 o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [field_extension]) THEN
    REWRITE_TAC [(← HolLight.GSYM COMPLEX_RING_INV)] THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM (SUBST1_TAC o HolLight.SYM o HolLight.REWRITE_RULE [COMPLEX_RING_CLAUSES] o
        HolLight.MATCH_MP RING_HOMOMORPHISM_0) THEN
      MATCH_MP_TAC RADICAL_ELEMENT_BASE THEN ASM_REWRITE_TAC [RING_0],
      FIRST_ASSUM (SUBST1_TAC o HolLight.SYM o HolLight.REWRITE_RULE [COMPLEX_RING_CLAUSES] o
        HolLight.MATCH_MP RING_HOMOMORPHISM_1) THEN
      MATCH_MP_TAC RADICAL_ELEMENT_BASE THEN ASM_REWRITE_TAC [RING_1],
      REWRITE_TAC [(← HolLight.GSYM COMPLEX_RING_CLAUSES)] THEN
      ASM_SIMP_TAC [RADICAL_ELEMENT_ADD],
      REWRITE_TAC [(← HolLight.GSYM COMPLEX_RING_CLAUSES)] THEN
      ASM_SIMP_TAC [RADICAL_ELEMENT_MUL],
      REWRITE_TAC [(← HolLight.GSYM COMPLEX_RING_CLAUSES)] THEN
      SIMP_TAC [RADICAL_ELEMENT_NEG],
      SIMP_TAC [RADICAL_ELEMENT_INV],
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RADICAL_ELEMENT_ROOT THEN
      EXISTS_TAC ([[n:num]]) THEN
      ASM_REWRITE_TAC [COMPLEX_RING_CLAUSES, COMPLEX_RING_POW, IN_UNIV] THEN
      ASM_ARITH_TAC])
  : ExceptT String IO thm).run
#eval RADICAL_NUMBER_IMP_RADICAL_ELEMENT

/- ------------------------------------------------------------------------- -/
/- An irreducible polynomial of prime degree at least 5, over a field whose  -/
/- image in C is real, with exactly two non-real roots has no root that is   -/
/- expressible by radicals: complex conjugation moves exactly two roots.     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 23
def NOT_RADICAL_ROOT_REAL_FIELD : thm := keep "NOT_RADICAL_ROOT_REAL_FIELD" fun _ => (do
  prove ([[!(h:A->complex) k p.
        field_extension (k,complex_ring) h /\
        (!x. x IN ring_carrier k ==> real(h x)) /\
        ring_irreducible (poly_ring k (:1)) p /\
        prime(poly_deg k p) /\ 5 <= poly_deg k p /\
        {z | poly_eval complex_ring (h o p) z = Cx(&0) /\ ~real z} HAS_SIZE 2
        ==> ~(?z. radical_number z /\
                  poly_eval complex_ring (h o p) z = Cx(&0))]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP RING_CHAR_FIELD_EXTENSION_COMPLEX_RING) THEN
    MP_TAC (← HolLight.ISPECL [([[h:A->complex]]), ([[cnj]]), ([[k:A ring]]), ([[complex_ring]]),
                   ([[p:(1->num)->A]])] PRIME_TRANSPOSITION_NO_RADICAL_ROOT_SPLITS) THEN
    ASM_SIMP_TAC [IN_GALOIS_GROUP, POLY_SPLITS_OVER_ALGEBRAICALLY_CLOSED_FIELD,
                 ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING,
                 RING_IRREDUCIBLE_IN_CARRIER] THEN
    REWRITE_TAC [COMPLEX_RING_CLAUSES, IN_UNIV, (← HolLight.GSYM REAL_CNJ)] THEN
    ASM_SIMP_TAC [PERMUTES_CNJ, RING_AUTOMORPHISM_CNJ] THEN
    MATCH_MP_TAC MONO_NOT THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_MESON_TAC [RADICAL_NUMBER_IMP_RADICAL_ELEMENT])
  : ExceptT String IO thm).run
#eval NOT_RADICAL_ROOT_REAL_FIELD

/- ------------------------------------------------------------------------- -/
/- The case of the rationals, the fraction field of the integers: every      -/
/- ring homomorphism into C is a field extension with real values.           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 24
def RING_HOMOMORPHISM_FRACTION_RING_INTEGER_RING : thm := keep "RING_HOMOMORPHISM_FRACTION_RING_INTEGER_RING" fun _ => (do
  prove ([[!(h:(int#int->bool)->A) r n.
        ring_homomorphism(fraction_ring integer_ring,r) h
        ==> h(ring_fractionate integer_ring
                {a | ring_regular integer_ring a} n) =
            ring_of_int r n]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[integer_ring]]), ([[fraction_ring integer_ring]]), ([[r:A ring]]),
                   ([[ring_fractionate integer_ring
                   {a | ring_regular integer_ring a}]]),
                   ([[h:(int#int->bool)->A]])] RING_HOMOMORPHISM_COMPOSE) THEN
    ASM_SIMP_TAC [fraction_ring, RING_HOMOMORPHISM_FRACTIONATE,
                 RING_MULTSYS_REGULAR] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[n:int]]) o
      HolLight.MATCH_MP RING_HOMOMORPHISM_RING_OF_INT) THEN
    REWRITE_TAC [INTEGER_RING_OF_INT, I_THM, o_THM])
  : ExceptT String IO thm).run
#eval RING_HOMOMORPHISM_FRACTION_RING_INTEGER_RING

#eval phrase 25
def RING_HOMOMORPHISM_FRACTION_RING_INTEGER_RING_EXISTS : thm := keep "RING_HOMOMORPHISM_FRACTION_RING_INTEGER_RING_EXISTS" fun _ => (do
  prove ([[?h. ring_homomorphism(fraction_ring integer_ring,complex_ring) h]])
   (MP_TAC (← HolLight.ISPECL [([[integer_ring]]), ([[complex_ring]]), ([[ring_of_int complex_ring]])] FRACTION_RING_UNIVERSAL) THEN
    REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN
    ANTS_TAC THENL [ALL_TAC, MESON_TAC []] THEN
    SIMP_TAC [INTEGRAL_DOMAIN_REGULAR, INTEGRAL_DOMAIN_INTEGER_RING, FIELD_UNIT,
             FIELD_COMPLEX_RING, INTEGER_RING, COMPLEX_RING_CLAUSES, IN_UNIV,
             COMPLEX_RING_OF_INT, CX_INJ] THEN
    REWRITE_TAC [(← HolLight.GSYM int_of_num_th), (← HolLight.GSYM int_eq)])
  : ExceptT String IO thm).run
#eval RING_HOMOMORPHISM_FRACTION_RING_INTEGER_RING_EXISTS

#eval phrase 26
def FIELD_EXTENSION_FRACTION_RING_INTEGER_RING : thm := keep "FIELD_EXTENSION_FRACTION_RING_INTEGER_RING" fun _ => (do
  let h1 ← tt (← ExceptT.mk [[~p ==> p \/ q ==> q]])
  prove ([[!h:(int#int->bool)->complex.
        ring_homomorphism(fraction_ring integer_ring,complex_ring) h
        ==> field_extension(fraction_ring integer_ring,complex_ring) h]])
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [field_extension, FRACTION_FIELD, INTEGRAL_DOMAIN_INTEGER_RING,
                FIELD_COMPLEX_RING] THEN
    MP_TAC (← HolLight.ISPECL [([[fraction_ring integer_ring]]), ([[complex_ring]]),
                   ([[h:(int#int->bool)->complex]])] FIELD_HOMOMORPHISM_IMP_MONOMORPHISM) THEN
    ASM_REWRITE_TAC [FRACTION_FIELD, INTEGRAL_DOMAIN_INTEGER_RING] THEN
    MATCH_MP_TAC h1 THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[ring_1(fraction_ring integer_ring)]])) THEN
    FIRST_ASSUM (SUBST1_TAC o HolLight.MATCH_MP RING_HOMOMORPHISM_1) THEN
    REWRITE_TAC [RING_1, COMPLEX_RING_CLAUSES, CX_INJ] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval FIELD_EXTENSION_FRACTION_RING_INTEGER_RING

#eval phrase 27
def REAL_FRACTION_RING_INTEGER_RING : thm := keep "REAL_FRACTION_RING_INTEGER_RING" fun _ => (do
  prove ([[!(h:(int#int->bool)->complex) x.
        ring_homomorphism(fraction_ring integer_ring,complex_ring) h /\
        x IN ring_carrier(fraction_ring integer_ring)
        ==> real(h x)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [REAL_CNJ] THEN
    MP_TAC (← HolLight.ISPECL [([[integer_ring]]), ([[{a:int | ring_regular integer_ring a}]]),
                   ([[complex_ring]]), ([[cnj o (h:(int#int->bool)->complex)]]),
                   ([[h:(int#int->bool)->complex]])] RING_LOCALIZATION_HOMOMORPHISM_UNIQUE) THEN
    ASM_REWRITE_TAC [(← HolLight.GSYM fraction_ring), RING_MULTSYS_REGULAR, o_THM] THEN
    ANTS_TAC THENL [ALL_TAC, ASM_SIMP_TAC []] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
      EXISTS_TAC ([[complex_ring]]) THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC RING_ISOMORPHISM_IMP_HOMOMORPHISM THEN
      REWRITE_TAC [(← HolLight.REWRITE_RULE [ring_automorphism] RING_AUTOMORPHISM_CNJ)],
      FIRST_ASSUM (fun th => HolLight.tactic_of do
        pure (REWRITE_TAC [(← HolLight.MATCH_MP RING_HOMOMORPHISM_FRACTION_RING_INTEGER_RING th)])) THEN
      REWRITE_TAC [COMPLEX_RING_OF_INT, CNJ_CX]])
  : ExceptT String IO thm).run
#eval REAL_FRACTION_RING_INTEGER_RING

#eval phrase 28
def NOT_RADICAL_ROOT_RATIONAL : thm := keep "NOT_RADICAL_ROOT_RATIONAL" fun _ => (do
  prove ([[!(h:(int#int->bool)->complex) p.
        ring_homomorphism(fraction_ring integer_ring,complex_ring) h /\
        ring_irreducible (poly_ring (fraction_ring integer_ring) (:1)) p /\
        prime(poly_deg (fraction_ring integer_ring) p) /\
        5 <= poly_deg (fraction_ring integer_ring) p /\
        {z | poly_eval complex_ring (h o p) z = Cx(&0) /\ ~real z} HAS_SIZE 2
        ==> ~(?z. radical_number z /\
                  poly_eval complex_ring (h o p) z = Cx(&0))]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC NOT_RADICAL_ROOT_REAL_FIELD THEN
    EXISTS_TAC ([[fraction_ring integer_ring]]) THEN
    ASM_SIMP_TAC [FIELD_EXTENSION_FRACTION_RING_INTEGER_RING,
                 REAL_FRACTION_RING_INTEGER_RING])
  : ExceptT String IO thm).run
#eval NOT_RADICAL_ROOT_RATIONAL

/- ------------------------------------------------------------------------- -/
/- The quintic is (the image of) an irreducible rational polynomial, by the  -/
/- Eisenstein criterion with the prime 2.                                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 29
def QUINTIC_RATIONAL_IRREDUCIBLE : thm := keep "QUINTIC_RATIONAL_IRREDUCIBLE" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[k < 5 <=> k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4]])
  prove ([[?p. ring_irreducible (poly_ring (fraction_ring integer_ring) (:1)) p /\
       poly_deg (fraction_ring integer_ring) p = 5 /\
       !h z. ring_homomorphism(fraction_ring integer_ring,complex_ring) h
             ==> poly_eval complex_ring (h o p) z =
                 z pow 5 - Cx(&4) * z + Cx(&2)]])
   (ABBREV_TAC ([[q = \m:1->num. if m one = 0 then &2 else if m one = 1 then -- &4
                   else if m one = 5 then &1 else &0:int]]) THEN
    SUBGOAL_THEN ([[!i. coeff i q = if i = 0 then &2 else if i = 1 then -- &4
                    else if i = 5 then &1 else &0:int]]) ASSUME_TAC THENL [EXPAND_TAC "q" THEN REWRITE_TAC [COEFF], ALL_TAC] THEN
    SUBGOAL_THEN ([[!d. ~(coeff d q = ring_0 integer_ring) ==> d <= 5]]) ASSUME_TAC THENL
     [ASM_REWRITE_TAC [INTEGER_RING] THEN GEN_TAC THEN
      REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[ring_powerseries integer_ring (q:(1->num)->int)]]) ASSUME_TAC THENL
     [REWRITE_TAC [RING_POWERSERIES_COEFF, INTEGER_RING, IN_UNIV], ALL_TAC] THEN
    SUBGOAL_THEN ([[ring_polynomial integer_ring (q:(1->num)->int)]]) ASSUME_TAC THENL
     [MATCH_MP_TAC RING_POLYNOMIAL_COEFF_BOUND THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[poly_deg integer_ring (q:(1->num)->int) = 5]]) ASSUME_TAC THENL
     [MATCH_MP_TAC POLY_DEG_EQ_COEFF THEN ASM_REWRITE_TAC [INTEGER_RING] THEN
      CONV_TAC (HolLight.DEPTH_CONV (NUM_RED_CONV ORELSEC INT_RED_CONV)),
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(q:(1->num)->int) monomial_1 = &2]]) ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN REWRITE_TAC [monomial_1], ALL_TAC] THEN
    EXISTS_TAC ([[ring_fractionate integer_ring {a | ring_regular integer_ring a} o
    (q:(1->num)->int)]]) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC EISENSTEIN_IRREDUCIBILITY_FRACTION_RING THEN
      EXISTS_TAC ([[&2:int]]) THEN
      ASM_REWRITE_TAC [UFD_INTEGER_RING, IN_POLY_RING_CARRIER,
                      SUBSET_UNIV, INTEGER_RING_DIVIDES, INTEGER_RING_POW] THEN
      CONV_TAC (HolLight.DEPTH_CONV (NUM_RED_CONV ORELSEC INT_RED_CONV)) THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC [ring_prime, INTEGER_RING, IN_UNIV, INTEGER_RING_UNIT,
                    INTEGER_RING_DIVIDES] THEN
        CONV_TAC INT_REDUCE_CONV THEN MESON_TAC [PRIME_INT_DIVPROD_EQ, PRIME_2],
        DISCH_THEN (MP_TAC o HolLight.MATCH_MP INT_DIVIDES_LE) THEN INT_ARITH_TAC,
        REWRITE_TAC [h1] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
        CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INTEGER_RULE,
        DISCH_THEN (MP_TAC o HolLight.MATCH_MP INT_DIVIDES_LE) THEN INT_ARITH_TAC],
      MP_TAC (← HolLight.ISPECL [([[integer_ring]]), ([[fraction_ring integer_ring]]),
                     ([[ring_fractionate integer_ring
                     {a | ring_regular integer_ring a}]]),
                     ([[q:(1->num)->int]])] POLY_DEG_MONOMORPHIC_IMAGE) THEN
      ASM_REWRITE_TAC [RING_MONOMORPHISM_FRACTIONATE],
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[(h:(int#int->bool)->complex) o
    ring_fractionate integer_ring {a | ring_regular integer_ring a} o
    (q:(1->num)->int) =
    ring_of_int complex_ring o q]]) SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, o_THM] THEN
      FIRST_ASSUM (fun th => HolLight.tactic_of do
        pure (REWRITE_TAC [(← HolLight.MATCH_MP RING_HOMOMORPHISM_FRACTION_RING_INTEGER_RING th)])),
      ALL_TAC] THEN
    SUBGOAL_THEN ([[ring_monomorphism(integer_ring,complex_ring) (ring_of_int complex_ring)]]) ASSUME_TAC THENL
     [REWRITE_TAC [RING_MONOMORPHISM_INTEGER_RING_OF_INT, COMPLEX_RING_CHAR],
      ALL_TAC] THEN
    HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand) POLY_EVAL_COMPLEX_RING o
      HolCore.Equal.lhand o HolLight.snd) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
      EXISTS_TAC ([[integer_ring]]) THEN
      ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM, IN_POLY_RING_CARRIER,
                   SUBSET_UNIV],
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[integer_ring]]), ([[complex_ring]]), ([[ring_of_int complex_ring]]),
                   ([[q:(1->num)->int]])] POLY_DEG_MONOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC [COEFF_COMPOSE] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV EXPAND_VSUM_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC [COMPLEX_RING_OF_INT, int_of_num_th, int_neg_th, CX_NEG] THEN
    CONV_TAC COMPLEX_RING)
  : ExceptT String IO thm).run
#eval QUINTIC_RATIONAL_IRREDUCIBLE

/- ------------------------------------------------------------------------- -/
/- The quintic has exactly 3 real roots: at least 3 by sign changes and the  -/
/- intermediate value theorem, at most 3 by Rolle, since the derivative      -/
/- 5 * x^4 - 4 has only two real roots.                                      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 30
#eval Session.prioritize_real

#eval phrase 31
def HAS_REAL_DERIVATIVE_QUINTIC : thm := keep "HAS_REAL_DERIVATIVE_QUINTIC" fun _ => (do
  prove ([[!x. ((\x. x pow 5 - &4 * x + &2)
        has_real_derivative (&5 * x pow 4 - &4)) (atreal x)]])
   (GEN_TAC THEN REAL_DIFF_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval HAS_REAL_DERIVATIVE_QUINTIC

#eval phrase 32
def REAL_CONTINUOUS_ON_QUINTIC : thm := keep "REAL_CONTINUOUS_ON_QUINTIC" fun _ => (do
  prove ([[!s. (\x. x pow 5 - &4 * x + &2) real_continuous_on s]])
   (GEN_TAC THEN MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
    REWRITE_TAC [real_differentiable_on] THEN
    MESON_TAC [HAS_REAL_DERIVATIVE_QUINTIC, HAS_REAL_DERIVATIVE_ATREAL_WITHIN])
  : ExceptT String IO thm).run
#eval REAL_CONTINUOUS_ON_QUINTIC

#eval phrase 33
def QUINTIC_AT_LEAST_3_REAL_ROOTS : thm := keep "QUINTIC_AT_LEAST_3_REAL_ROOTS" fun _ => (do
  prove ([[?a b c. a < b /\ b < c /\
           a pow 5 - &4 * a + &2 = &0 /\
           b pow 5 - &4 * b + &2 = &0 /\
           c pow 5 - &4 * c + &2 = &0]])
   (SUBGOAL_THEN ([[!a b. a <= b /\
          (a pow 5 - &4 * a + &2 < &0 /\ &0 < b pow 5 - &4 * b + &2 \/
           &0 < a pow 5 - &4 * a + &2 /\ b pow 5 - &4 * b + &2 < &0)
          ==> ?x. a < x /\ x < b /\ x pow 5 - &4 * x + &2 = &0]]) (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPECL [([[-- &2]]), ([[&0]])] th) THEN
               MP_TAC (← HolLight.SPECL [([[&0]]), ([[&1]])] th) THEN
               MP_TAC (← HolLight.SPECL [([[&1]]), ([[&2]])] th))) THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THENL
       [MP_TAC (← HolLight.ISPECL [([[\x. x pow 5 - &4 * x + &2]]), ([[a:real]]), ([[b:real]]), ([[&0]])] REAL_IVT_INCREASING),
        MP_TAC (← HolLight.ISPECL [([[\x. x pow 5 - &4 * x + &2]]), ([[a:real]]), ([[b:real]]), ([[&0]])] REAL_IVT_DECREASING)] THEN
      ASM_SIMP_TAC [REAL_CONTINUOUS_ON_QUINTIC, REAL_LT_IMP_LE,
                   IN_REAL_INTERVAL] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[x:real]]) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [REAL_LT_LE] THEN
      CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC,
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      DISCH_THEN (X_CHOOSE_THEN ([[c:real]]) STRIP_ASSUME_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[b:real]]) STRIP_ASSUME_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[a:real]]) STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [([[a:real]]), ([[b:real]]), ([[c:real]])] THEN
      ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC])
  : ExceptT String IO thm).run
#eval QUINTIC_AT_LEAST_3_REAL_ROOTS

#eval phrase 34
def QUINTIC_AT_MOST_3_REAL_ROOTS : thm := keep "QUINTIC_AT_MOST_3_REAL_ROOTS" fun _ => (do
  prove ([[~(?a b c d. a < b /\ b < c /\ c < d /\
               a pow 5 - &4 * a + &2 = &0 /\
               b pow 5 - &4 * b + &2 = &0 /\
               c pow 5 - &4 * c + &2 = &0 /\
               d pow 5 - &4 * d + &2 = &0)]])
   (REWRITE_TAC [NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[a:real]]), ([[b:real]]), ([[c:real]]), ([[d:real]])] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN ([[!u v. u < v /\ u pow 5 - &4 * u + &2 = &0 /\ v pow 5 - &4 * v + &2 = &0
          ==> ?x. u < x /\ x < v /\ &5 * x pow 4 - &4 = &0]]) (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPECL [([[a:real]]), ([[b:real]])] th) THEN
               MP_TAC (← HolLight.SPECL [([[b:real]]), ([[c:real]])] th) THEN
               MP_TAC (← HolLight.SPECL [([[c:real]]), ([[d:real]])] th))) THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC (← HolLight.ISPECL [([[\x. x pow 5 - &4 * x + &2]]), ([[\x. &5 * x pow 4 - &4]]),
                     ([[u:real]]), ([[v:real]])] REAL_ROLLE) THEN
      ASM_REWRITE_TAC [REAL_CONTINUOUS_ON_QUINTIC, HAS_REAL_DERIVATIVE_QUINTIC,
                      IN_REAL_INTERVAL, (← HolLight.GSYM CONJ_ASSOC)],
      ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM, NOT_EXISTS_THM] THEN
      X_GEN_TAC ([[z:real]]) THEN STRIP_TAC THEN
      X_GEN_TAC ([[y:real]]) THEN STRIP_TAC THEN
      X_GEN_TAC ([[x:real]]) THEN STRIP_TAC THEN
      MP_TAC (← HolLight.SPECL [([[4]]), ([[x:real]]), ([[y:real]])] REAL_POW_EQ_EQ) THEN
      MP_TAC (← HolLight.SPECL [([[4]]), ([[y:real]]), ([[z:real]])] REAL_POW_EQ_EQ) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC])
  : ExceptT String IO thm).run
#eval QUINTIC_AT_MOST_3_REAL_ROOTS

#eval phrase 35
def QUINTIC_REAL_ROOTS : thm := keep "QUINTIC_REAL_ROOTS" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[a < b /\ b < c /\ ~(x < a) /\ ~(a < x /\ x < b) /\
      ~(b < x /\ x < c) /\ ~(c < x)
      ==> x = a \/ x = b \/ x = c]])
  prove ([[{x | x pow 5 - &4 * x + &2 = &0} HAS_SIZE 3]])
   (X_CHOOSE_THEN ([[a:real]]) (X_CHOOSE_THEN ([[b:real]]) (X_CHOOSE_THEN ([[c:real]]) STRIP_ASSUME_TAC)) QUINTIC_AT_LEAST_3_REAL_ROOTS THEN
    SUBGOAL_THEN ([[{x | x pow 5 - &4 * x + &2 = &0} = {a,b,c}]]) SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_INSERT, NOT_IN_EMPTY, IN_ELIM_THM] THEN
      X_GEN_TAC ([[x:real]]) THEN EQ_TAC THENL
       [DISCH_TAC, STRIP_TAC THEN ASM_REWRITE_TAC []] THEN
      MP_TAC QUINTIC_AT_MOST_3_REAL_ROOTS THEN
      REWRITE_TAC [NOT_EXISTS_THM] THEN DISCH_TAC THEN
      MATCH_MP_TAC h1 THEN
      ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THEN STRIP_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[x:real]]), ([[a:real]]), ([[b:real]]), ([[c:real]])]),
        FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[a:real]]), ([[x:real]]), ([[b:real]]), ([[c:real]])]),
        FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[a:real]]), ([[b:real]]), ([[x:real]]), ([[c:real]])]),
        FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[a:real]]), ([[b:real]]), ([[c:real]]), ([[x:real]])])] THEN ASM_REWRITE_TAC [],
      SUBGOAL_THEN ([[~(a:real = b) /\ ~(a = c) /\ ~(b = c)]]) STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC,
        SIMP_TAC [HAS_SIZE, CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY,
                 IN_INSERT, NOT_IN_EMPTY] THEN
        ASM_REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV]])
  : ExceptT String IO thm).run
#eval QUINTIC_REAL_ROOTS

#eval phrase 36
#eval (do let _ ← SessionMultiLib.Complexes.prioritize_complex.run : IO Unit)

#eval phrase 37
def QUINTIC_COMPLEX_REAL_ROOTS : thm := keep "QUINTIC_COMPLEX_REAL_ROOTS" fun _ => (do
  prove ([[{z | z pow 5 - Cx(&4) * z + Cx(&2) = Cx(&0) /\ real z} HAS_SIZE 3]])
   (SUBGOAL_THEN ([[{z | z pow 5 - Cx(&4) * z + Cx(&2) = Cx(&0) /\ real z} =
    IMAGE Cx {x | x pow 5 - &4 * x + &2 = &0}]]) SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN
      X_GEN_TAC ([[z:complex]]) THEN ASM_CASES_TAC ([[real z]]) THEN
      ASM_REWRITE_TAC [] THENL
       [FIRST_X_ASSUM (X_CHOOSE_THEN ([[x:real]]) SUBST1_TAC o
          HolLight.GEN_REWRITE_RULE HolCore.Lib.I [REAL_EXISTS]) THEN
        REWRITE_TAC [(← HolLight.GSYM CX_POW), (← HolLight.GSYM CX_MUL), (← HolLight.GSYM CX_SUB), (← HolLight.GSYM CX_ADD),
                    CX_INJ] THEN
        MESON_TAC [],
        ASM_MESON_TAC [REAL_CX]],
      MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
      SIMP_TAC [CX_INJ, QUINTIC_REAL_ROOTS]])
  : ExceptT String IO thm).run
#eval QUINTIC_COMPLEX_REAL_ROOTS

#eval phrase 38
def QUINTIC_NONREAL_ROOTS : thm := keep "QUINTIC_NONREAL_ROOTS" fun _ => (do
  prove ([[{z | z pow 5 - Cx(&4) * z + Cx(&2) = Cx(&0) /\ ~real z} HAS_SIZE 2]])
   (X_CHOOSE_THEN ([[p:(1->num)->(int#int->bool)]]) STRIP_ASSUME_TAC QUINTIC_RATIONAL_IRREDUCIBLE THEN
    X_CHOOSE_TAC ([[h:(int#int->bool)->complex]]) RING_HOMOMORPHISM_FRACTION_RING_INTEGER_RING_EXISTS THEN
    MP_TAC (← HolLight.ISPECL [([[h:(int#int->bool)->complex]]), ([[fraction_ring integer_ring]]),
                   ([[p:(1->num)->(int#int->bool)]])] COMPLEX_ROOTS_IRREDUCIBLE) THEN
    ASM_SIMP_TAC [FIELD_EXTENSION_FRACTION_RING_INTEGER_RING] THEN
    DISCH_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[{z | z pow 5 - Cx(&4) * z + Cx(&2) = Cx(&0)}]]),
                   ([[{z | z pow 5 - Cx(&4) * z + Cx(&2) = Cx(&0) /\ real z}]]),
                   ([[5]]), ([[3]])] HAS_SIZE_DIFF) THEN
    ASM_REWRITE_TAC [QUINTIC_COMPLEX_REAL_ROOTS] THEN
    ANTS_TAC THENL [SET_TAC [], ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC [])
  : ExceptT String IO thm).run
#eval QUINTIC_NONREAL_ROOTS

/- ------------------------------------------------------------------------- -/
/- The main theorem.                                                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 39
def NOT_RADICAL_QUINTIC_ROOT : thm := keep "NOT_RADICAL_QUINTIC_ROOT" fun _ => (do
  prove ([[~(?z. radical_number z /\ z pow 5 - Cx(&4) * z + Cx(&2) = Cx(&0))]])
   (X_CHOOSE_THEN ([[p:(1->num)->(int#int->bool)]]) STRIP_ASSUME_TAC QUINTIC_RATIONAL_IRREDUCIBLE THEN
    X_CHOOSE_TAC ([[h:(int#int->bool)->complex]]) RING_HOMOMORPHISM_FRACTION_RING_INTEGER_RING_EXISTS THEN
    MP_TAC (← HolLight.ISPECL [([[h:(int#int->bool)->complex]]), ([[p:(1->num)->(int#int->bool)]])] NOT_RADICAL_ROOT_RATIONAL) THEN
    ASM_SIMP_TAC [QUINTIC_NONREAL_ROOTS] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV PRIME_CONV) THEN CONV_TAC NUM_REDUCE_CONV)
  : ExceptT String IO thm).run
#eval NOT_RADICAL_QUINTIC_ROOT

end Hol100.Unsolvability
