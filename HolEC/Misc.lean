/- ========================================================================= -/
/- A few extras to support proofs around elliptic curves.                  -/
/- ========================================================================= -/
/- File: HolEC/Misc.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/misc.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.Misc fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, INT_ARITH, TAUT, SET_RULE, ...) they are
  bound first, in OCaml's order.
-/

import HolLibrary.Iter
import HolLibrary.Prime
import HolLibrary.Pocklington
import HolLibrary.Integer
import HolLibrary.Isum
import HolLibrary.Binomial
import HolLibrary.Products
import HolLibrary.Multiplicative
import HolLibrary.Primitive
import HolLibrary.Frag
import HolLibrary.Wo
import HolLibrary.Card
import HolLibrary.GroupTheory
import HolLibrary.RingTheory

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolEC.Misc

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ARITH CARD_EQ_0 CAUCHY_GROUP_THEOREM CHOOSE_SUBSET_EQ CONG CONJ_ASSOC
   DIVIDES_2 EMPTY_SUBSET EQ_TRANS EVEN_MULT FINITE_CARD_LE_IMAGE
   FINITE_CARD_LE_SUBSET FINITE_CARD_LE_UNIONS FINITE_RESTRICT FORALL_PAIR_THM
   FORALL_UNWIND_THM1 GROUP_CARRIER_NONEMPTY
   GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER GROUP_ELEMENT_ORDER_EQ_2_ALT HAS_SIZE
   INSERT_SUBSET INTEGER_MOD_RING_CLAUSES INT_ABS_NUM INT_ABS_POS INT_ABS_POW
   INT_CONG_MOD_0 INT_EXISTS_POS INT_OF_NUM_CLAUSES INT_OF_NUM_POW
   INT_OF_NUM_REM INT_REM_0 IN_ELIM_PAIR_THM IN_ELIM_THM IN_UNIV
   LEFT_IMP_EXISTS_THM LE_1 LE_MULT_RCANCEL LE_REFL MOD_EXP_MOD MOD_LT MOD_LT_EQ
   MULT_CLAUSES MULT_SYM NOT_LT PRIME_2 RIGHT_FORALL_IMP_THM
   RING_CHAR_DIVIDES_MUL RING_CHAR_DIVIDES_PRIME SIMPLE_IMAGE_GEN SUBSET
   UNIONS_GSPEC divides num_congruent : thm)
  deriving Inhabited

/-- What misc.ml uses from Session besides theorems. -/
structure MiscDeps where
  new_definition : String → ExceptT String IO thm
  define : String → ExceptT String IO thm
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  METIS_TAC : List thm → tactic
  ASM_METIS_TAC : List thm → tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  TAUT : term → ExceptT String IO thm
  INDUCT_TAC : tactic
  INT_ARITH : term → ExceptT String IO thm
  INT_ARITH_TAC : tactic
  ASM_INT_ARITH_TAC : tactic
  INTEGER_RULE : term → ExceptT String IO thm  -- ints.ml's INTEGER_RULE
  INTEGER_TAC : tactic
  NUMBER_RULE : ioconv  -- ints.ml's NUMBER_RULE
  NUM_REDUCE_CONV : ioconv
  INT_REDUCE_CONV : ioconv
  INT_RED_CONV : ioconv
  INT_REM_DOWN_CONV : ioconv
  HAS_SIZE_CONV : ioconv  -- card.ml's HAS_SIZE_CONV
  let_CONV : ioconv
  num_CONV : ioconv
  mk_numeral : Rat → Except String term
  PRIME_CONV : term → ExceptT String IO thm  -- pocklington.ml's PRIME_CONV
  RING_RULE : term → ExceptT String IO thm  -- ringtheory.ml's RING_RULE
  INTEGRAL_DOMAIN_RULE : term → ExceptT String IO thm
  FIELD_TAC : tactic  -- ringtheory.ml's FIELD_TAC
  INTEGER_MOD_RING_RED_CONV : ioconv
  core1 : CoreThms1

/-- RingTheory's `wPart` (copied verbatim).  `W(MP_TAC o PART_MATCH f th o g
    o snd)`: match `th`'s part `f` against the part `g` of the goal, and
    MP_TAC the instance. -/
def wPart [HolBase] (g : term → Except String term) (f : term → Except String term)
    (th : thm) : tactic := fun gl =>
  ExceptT.run do
    let t ← liftExcept (g gl.2)
    ExceptT.mk (MP_TAC (← PART_MATCH f th t) gl)

/-- tactics.ml's NO_TAC. -/
def NO_TAC : tactic := HolCore.Tactics.NO_TAC



/- ------------------------------------------------------------------------- -/
/- A few extras to support proofs around elliptic curves.  (misc.ml 1-226)  -/
/- ------------------------------------------------------------------------- -/

structure MiscThms where
  -- @@FIELDS
  FINITE_QUADRATIC_CURVE : thm
  NOT_RING_CHAR_DIVIDES_TAC : tactic
  FIELD_CHAR_NOT2 : thm
  FIELD_CHAR_NOT3 : thm
  FIELD_CHAR_NOT23 : thm
  CAUCHY_GROUP_THEOREM_2 : thm
  GROUP_ADHOC_ORDER_UNIQUE_LEMMA : thm
  SYMMETRY_LEMMA : thm
  ASSOCIATIVITY_LEMMA : thm
  INTEGER_MOD_RING_ROOT_EXISTS : thm
  deriving Inhabited

@[nospecialize]
def setupMiscThms [HolBase] (D : MiscDeps) :
    ExceptT String IO MiscThms := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, HAS_SIZE_CONV, INTEGRAL_DOMAIN_RULE,
        MESON_TAC, METIS_TAC, NUM_REDUCE_CONV, PRIME_CONV, SET_TAC, TAUT, mk_numeral, .. } := D
  let { ARITH, CARD_EQ_0, CAUCHY_GROUP_THEOREM, CHOOSE_SUBSET_EQ, CONG, CONJ_ASSOC,
        DIVIDES_2, EMPTY_SUBSET, EQ_TRANS, EVEN_MULT, FINITE_CARD_LE_IMAGE,
        FINITE_CARD_LE_SUBSET, FINITE_CARD_LE_UNIONS, FINITE_RESTRICT, FORALL_PAIR_THM,
        FORALL_UNWIND_THM1, GROUP_CARRIER_NONEMPTY,
        GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER, GROUP_ELEMENT_ORDER_EQ_2_ALT,
        HAS_SIZE, INSERT_SUBSET, INTEGER_MOD_RING_CLAUSES, INT_ABS_NUM, INT_ABS_POS,
        INT_ABS_POW, INT_CONG_MOD_0, INT_EXISTS_POS, INT_OF_NUM_CLAUSES,
        INT_OF_NUM_POW, INT_OF_NUM_REM, INT_REM_0, IN_ELIM_PAIR_THM, IN_ELIM_THM,
        IN_UNIV, LEFT_IMP_EXISTS_THM, LE_1, LE_MULT_RCANCEL, LE_REFL, MOD_EXP_MOD,
        MOD_LT, MOD_LT_EQ, MULT_CLAUSES, MULT_SYM, NOT_LT, PRIME_2,
        RIGHT_FORALL_IMP_THM, RING_CHAR_DIVIDES_MUL, RING_CHAR_DIVIDES_PRIME,
        SIMPLE_IMAGE_GEN, SUBSET, UNIONS_GSPEC, divides, num_congruent, .. } := D.core1
  -- @@SCOPE END

  /- Bounds on size of any curve of the form y^2 = f(x) over finite field. -/

  let FINITE_QUADRATIC_CURVE ← prove
   r"!(r:A ring) h.
        integral_domain r /\ FINITE(ring_carrier r)
        ==> FINITE {x,y | x IN ring_carrier r /\ y IN ring_carrier r /\
                          ring_pow r y 2 = h x} /\
            CARD {x,y | x IN ring_carrier r /\ y IN ring_carrier r /\
                        ring_pow r y 2 = h x}
            <= 2 * CARD(ring_carrier r)"
   (← do
    -- right to left: the INTEGRAL_DOMAIN_RULE, the ARITH_RULE, then the TAUT
    let i3 ← INTEGRAL_DOMAIN_RULE
      (← q r"!x y:A. integral_domain r
    ==> (ring_pow r x 2 = ring_pow r y 2 <=> x = y \/ x = ring_neg r y)")
    let a2 ← ARITH_RULE (← q r"~(n <= 2) <=> 3 <= n")
    let t1 ← TAUT (← q r"p /\ q <=> p /\ ~(p ==> ~q)")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC [MULT_SYM] THEN
    MATCH_MP_TAC FINITE_CARD_LE_SUBSET THEN
    EXISTS_TAC
     (← q r"UNIONS {{x,y | y | y IN ring_carrier r /\ ring_pow r y 2 = h x} |x|
              (x:A) IN ring_carrier r}") THEN
    CONJ_TAC THENL
     [REWRITE_TAC [UNIONS_GSPEC, SUBSET, FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN
      SET_TAC [],
      MATCH_MP_TAC FINITE_CARD_LE_UNIONS THEN ASM_REWRITE_TAC [LE_REFL]] THEN
    X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
    MATCH_MP_TAC FINITE_CARD_LE_IMAGE THEN
    ONCE_REWRITE_TAC [t1] THEN
    REWRITE_TAC [a2, CHOOSE_SUBSET_EQ] THEN
    ASM_SIMP_TAC [FINITE_RESTRICT] THEN
    CONV_TAC (ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN (CHOOSE_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET] THEN
    MP_TAC i3 THEN
    ASM_REWRITE_TAC [IN_ELIM_THM] THEN ASM METIS_TAC []))

  /- Try to dispose of ring characteristic side-conditions. This in general
     requires external factorization tools for "multifactor" on large
     numbers. -/

  let NOT_RING_CHAR_DIVIDES_TAC : tactic ← do
    -- `let bops = .. and patcheck = .. in`, left to right
    let mul ← q r"( * ):num->num->num"
    let bops : List term → Except String term := list_mk_binop mul
    let pat ← q r"~(ring_char r divides NUMERAL n)"
    let patcheck (w : term) : IO Bool := do
      match ← (term_match [] pat w).run with
      | .ok _ => pure true
      | .error _ => pure false
    pure (W (fun (_asl, w) => tactic_of do
            if !(← patcheck w) then throw "NOT_RING_CHAR_DIVIDES_TAC"
            let n ← liftExcept (dest_numeral (← liftExcept (rand (← liftExcept (rand w)))))
            let ns ← HolLibrary.Pocklington.multifactor n
            let ntm ← liftExcept (bops (← liftExcept (ns.mapM mk_numeral)))
            pure (SUBST1_TAC (← SYM (← ExceptT.mk (NUM_REDUCE_CONV ntm))))) THEN
          ASM_SIMP_TAC [RING_CHAR_DIVIDES_MUL])

  /- Ad-hoc rewrites for equality versus divisibility of characteristic. -/

  let FIELD_CHAR_NOT2 ← prove
   r"!(f:A ring) P.
        field f /\ ~(ring_char f = 2) /\ P <=>
        field f /\ ~(ring_char f divides 2) /\ P"
   (← do
    pure (MESON_TAC [RING_CHAR_DIVIDES_PRIME, PRIME_2]))

  let FIELD_CHAR_NOT3 ← prove
   r"!(f:A ring) P.
        field f /\ ~(ring_char f = 3) /\ P <=>
        field f /\ ~(ring_char f divides 3) /\ P"
   (← do
    let p1 ← PRIME_CONV (← q r"prime 3")
    pure (MESON_TAC [RING_CHAR_DIVIDES_PRIME, p1]))

  let FIELD_CHAR_NOT23 ← prove
   r"!(f:A ring) P.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\ P <=>
        field f /\ ~(ring_char f divides 2) /\ ~(ring_char f divides 3) /\ P"
   (← do
    let p1 ← PRIME_CONV (← q r"prime 3")
    pure (MESON_TAC [RING_CHAR_DIVIDES_PRIME, PRIME_2, p1]))

  /- An ad-hoc way of confirming the size of a group to be n when there is a
     crude bound of < 3 * n and we also know there are no points of order 2. -/

  let CAUCHY_GROUP_THEOREM_2 ← prove
   r"!G:A group.
        FINITE(group_carrier G) /\ EVEN(CARD(group_carrier G))
        ==> ?x. x IN group_carrier G /\ group_element_order G x = 2"
   (← do
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC CAUCHY_GROUP_THEOREM THEN
    ASM_REWRITE_TAC [PRIME_2, DIVIDES_2]))

  let GROUP_ADHOC_ORDER_UNIQUE_LEMMA ← prove
   r"!G (a:A) p.
      FINITE(group_carrier G) /\ CARD(group_carrier G) < 3 * p /\
      (!x. x IN group_carrier G /\ group_inv G x = x ==> x = group_id G) /\
      a IN group_carrier G /\ group_element_order G a = p
      ==> (group_carrier G) HAS_SIZE p"
   (← do
    let t1 ← TAUT (← q r"~p ==> p ==> q")
    pure (SIMP_TAC [HAS_SIZE] THEN REPEAT STRIP_TAC THEN MP_TAC
     (← SPECL [← q r"G:A group", ← q r"a:A"] GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER) THEN
    ASM_REWRITE_TAC [divides, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"d:num") THEN
    ASM_CASES_TAC (← q r"d = 0") THEN
    ASM_SIMP_TAC [CARD_EQ_0, MULT_CLAUSES, GROUP_CARRIER_NONEMPTY] THEN
    ASM_CASES_TAC (← q r"d = 1") THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN
    ASM_CASES_TAC (← q r"d = 2") THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THENL
     [MP_TAC (← ISPEC (← q r"G:A group") CAUCHY_GROUP_THEOREM_2) THEN
      ASM_REWRITE_TAC [EVEN_MULT, ARITH, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"x:A") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_SIMP_TAC [GROUP_ELEMENT_ORDER_EQ_2_ALT] THEN ASM_MESON_TAC [],
      UNDISCH_TAC (← q r"CARD(group_carrier(G:A group)) < 3 * p") THEN
      MATCH_MP_TAC t1 THEN ASM_REWRITE_TAC [NOT_LT] THEN
      GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
      ASM_REWRITE_TAC [LE_MULT_RCANCEL] THEN ASM_ARITH_TAC]))

  /- Use some symmetry to ease algebraic reduction of associativity -/

  let SYMMETRY_LEMMA ← prove
   r"!P eq add.
     (!x y. P x /\ P y /\ eq x y ==> eq y x) /\
     (!x y. P x /\ P y ==> P(add x y)) /\
     (!x y. P x /\ P y ==> add x y = add y x) /\
     (!x y z. P x /\ P y /\ P z /\ (eq x y \/ eq (add x y) z)
              ==> add x (add y z) = add (add x y) z) /\
     (!x y z. P x /\ P y /\ P z /\
              ~(eq x y) /\ ~(eq y z) /\ ~(eq x z) /\
              ~(eq (add x y) z) /\ ~(eq (add y z) x)
              ==> add x (add y z) = add (add x y) z)
     ==> !x y z:A. P x /\ P y /\ P z ==> add x (add y z) = add (add x y) z"
   (← do
    pure (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"(eq:A->A->bool) x y") THEN ASM_SIMP_TAC [] THEN
    ASM_CASES_TAC (← q r"(eq:A->A->bool) y z") THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"(eq:A->A->bool) x z") THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"(eq:A->A->bool) ((add:A->A->A) x y) z") THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"(eq:A->A->bool) ((add:A->A->A) y z) x") THEN
    ASM_MESON_TAC []))

  let ASSOCIATIVITY_LEMMA ← prove
   r"!P add neg (id:A).
        P id /\
        (!x. P x ==> P(neg x)) /\
        (!x y. P x /\ P y ==> P(add x y)) /\
        (!x. P x ==> add id x = x) /\
        (!x. P x ==> add (neg x) x = id) /\
        (!x y. P x /\ P y ==> add x y = add y x) /\
        (!x. P x ==> neg(neg x) = x) /\
        (!x y. P x /\ P y ==> neg(add x y) = add (neg x) (neg y)) /\
        (!x y. P x /\ P y ==> add x (add x y) = add (add x x) y) /\
        (!x y. P x /\ P y ==> add (neg x) (add x y) = y) /\
        (!x y z u v.
            P x /\ P y /\ P z /\ P u /\ P v
            ==> ~(x = id) /\ ~(y = id) /\ ~(z = id) /\
                ~(u = id) /\ ~(v = id) /\
                ~(y = x \/ y = neg x) /\
                ~(z = y \/ z = neg y) /\
                ~(z = x \/ z = neg x) /\
                ~(z = u \/ z = neg u) /\
                ~(x = v \/ x = neg v)
                ==> add x y = u /\ add y z = v
                    ==> add x v = add u z)
     ==> !x y z. P x /\ P y /\ P z ==> add x (add y z) = add (add x y) z"
   (← do
    let t1 ← TAUT (← q r"p ==> q ==> r /\ s ==> t <=> r ==> s ==> p /\ q ==> t")
    pure (ONCE_REWRITE_TAC [t1] THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM, FORALL_UNWIND_THM1] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC SYMMETRY_LEMMA THEN
    EXISTS_TAC (← q r"\x y. y:A = x \/ y = neg x") THEN
    REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [],
      ASM_MESON_TAC [],
      ASM_MESON_TAC [],
      ALL_TAC,
      MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A", ← q r"z:A"] THEN STRIP_TAC THEN
      ASM_CASES_TAC (← q r"x:A = id") THENL
       [ASM_SIMP_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN
      ASM_CASES_TAC (← q r"y:A = id") THENL
       [ASM_SIMP_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN
      ASM_CASES_TAC (← q r"z:A = id") THENL
       [ASM_SIMP_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC []] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [],
      ASM_MESON_TAC [],
      ALL_TAC,
      TRANS_TAC EQ_TRANS (← q r"id:A") THEN
      CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
      TRANS_TAC EQ_TRANS (← q r"(add:A->A->A) x (neg x)") THEN
      CONJ_TAC THENL [AP_TERM_TAC, ASM_MESON_TAC []] THEN
      ASM_SIMP_TAC [] THEN ASM_MESON_TAC []] THEN
    TRANS_TAC EQ_TRANS
     (← q r"add (x:A) (add (neg x) (add (add x y) (add x y)))") THEN
    CONJ_TAC THENL [AP_TERM_TAC, ASM_MESON_TAC []] THEN
    TRANS_TAC EQ_TRANS (← q r"add (add (neg x) (add x y)) (add x y):A") THEN
    CONJ_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x y:A. P x /\ P y ==> add y (add x x) = add (add y x) x")
     (fun th => ASM_SIMP_TAC [th]) THEN
    ASM_MESON_TAC []))

  /- Formulate existence of roots in finite field as power residue over N.
     This is intuitively completely trivial but fiddly in the fine details,
     especially since we don't actually assume n is prime and so it's a
     field. -/

  let INTEGER_MOD_RING_ROOT_EXISTS ← prove
   r"!n a k. (?b. b IN ring_carrier (integer_mod_ring n) /\
                ring_pow (integer_mod_ring n) b k = &a) <=>
           (n = 0 \/ a < n) /\
           (?b. (b EXP k == a) (mod n))"
   (← do
    pure (REWRITE_TAC [num_congruent, ← GSYM INT_OF_NUM_REM, ← GSYM INT_OF_NUM_POW] THEN
    REWRITE_TAC [INT_EXISTS_POS] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"n = 0") THEN ASM_SIMP_TAC [INTEGER_MOD_RING_CLAUSES, LE_1] THENL
     [REWRITE_TAC [IN_UNIV, INT_REM_0, INT_CONG_MOD_0] THEN
      EQ_TAC THENL [DISCH_THEN (X_CHOOSE_TAC (← q r"b:int")), MESON_TAC []] THEN
      EXISTS_TAC (← q r"abs b:int") THEN
      ASM_REWRITE_TAC [INT_ABS_POS, ← GSYM INT_ABS_POW, INT_ABS_NUM],
      REWRITE_TAC [IN_ELIM_THM, ← GSYM CONJ_ASSOC] THEN
      REWRITE_TAC [← GSYM INT_EXISTS_POS, INT_OF_NUM_CLAUSES, INT_OF_NUM_REM] THEN
      REWRITE_TAC [← GSYM num_congruent, CONG] THEN
      ASM_MESON_TAC [MOD_LT, MOD_EXP_MOD, MOD_LT_EQ]]))

  -- @@RETURN BEGIN
  return { FINITE_QUADRATIC_CURVE, NOT_RING_CHAR_DIVIDES_TAC, FIELD_CHAR_NOT2,
           FIELD_CHAR_NOT3, FIELD_CHAR_NOT23, CAUCHY_GROUP_THEOREM_2,
           GROUP_ADHOC_ORDER_UNIQUE_LEMMA, SYMMETRY_LEMMA, ASSOCIATIVITY_LEMMA,
           INTEGER_MOD_RING_ROOT_EXISTS }
  -- @@RETURN END

end HolEC.Misc
