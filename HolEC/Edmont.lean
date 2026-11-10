/- ========================================================================= -/
/- Mapping from Edwards to Montgomery form (and back as applicable).       -/
/- ========================================================================= -/
/- File: HolEC/Edmont.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/edmont.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml, EC/edwards.ml, EC/montgomery.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.Edmont fills them).

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
import HolEC.Misc
import HolEC.Edwards
import HolEC.Montgomery

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolEC.Edmont

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ABELIAN_EDWARDS_GROUP ABELIAN_MONTGOMERY_GROUP CONJ_ASSOC CONTRAPOS_THM
   DE_MORGAN_THM DIVIDES_REFL EDWARDS_GROUP EDWARDS_NONSINGULAR_DENOMINATORS
   FIELD_CHAR_NOT2 FIELD_IMP_INTEGRAL_DOMAIN FIELD_INV_EQ_0 FIELD_MUL_EQ_0
   FIELD_POW_EQ_0 FORALL_IN_IMAGE FORALL_OPTION_THM FORALL_PAIR_THM
   GROUP_HOMOMORPHISM GROUP_INV GROUP_ISOMORPHISMS
   GROUP_ISOMORPHISMS_IMP_ISOMORPHISM GROUP_ISOMORPHISMS_SYM GROUP_LID_EQ
   GROUP_MUL GROUP_MUL_ASSOC GROUP_MUL_LCANCEL GROUP_MUL_LID GROUP_MUL_RID
   GROUP_RINV_EQ IMP_CONJ IMP_CONJ_ALT IMP_IMP IN ISOMORPHIC_GROUP_SYM
   LEFT_IMP_EXISTS_THM MONTGOMERY_GROUP MONTGOMERY_STRONGLY_NONSINGULAR
   MONTGOMERY_STRONGLY_NONSINGULAR_IMP_NONSINGULAR PAIR_EQ PRIME_2 RING_0 RING_1
   RING_ADD_LZERO RING_ADD_RZERO RING_CHAR_DIVIDES_PRIME RING_CLAUSES RING_DIV_1
   RING_INV RING_INV_MUL RING_MUL RING_MUL_LID RING_MUL_LNEG RING_MUL_LZERO
   RING_MUL_RID RING_MUL_RNEG RING_MUL_RZERO RING_NEG RING_NEG_EQ RING_NEG_EQ_0
   RING_NEG_NEG RING_OF_NUM_EQ_0 RING_POW RING_POW_2 RING_SUB RING_SUB_EQ_0
   RING_SUB_RZERO SUBSET abelian_group edwards_0 edwards_add edwards_curve
   edwards_neg edwards_nonsingular isomorphic_group montgomery_add
   montgomery_curve montgomery_neg montgomery_nonsingular
   montgomery_strongly_nonsingular option_DISTINCT option_INJ ring_div : thm)
  deriving Inhabited

/-- What edmont.ml uses from Session besides theorems. -/
structure EdmontDeps where
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
  RING_CARRIER_TAC : tactic
  RING_TAC : tactic
  RING_PULL_DIV_TAC : tactic
  LET_TAC : tactic
  GROUP_RULE : term → ExceptT String IO thm  -- grouptheory.ml's GROUP_RULE
  basic_ss : List thm → IO (Except String HolCore.Simp.simpset)
  INTEGER_MOD_RING_RED_CONV : ioconv
  NOT_RING_CHAR_DIVIDES_TAC : tactic  -- misc.ml's NOT_RING_CHAR_DIVIDES_TAC
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
/- The maps between Edwards(a,d) and Montgomery(A,B), with scaling factor c, -/
/- and how the curve mappings interact with singularity.  (edmont.ml 1-165)  -/
/- ------------------------------------------------------------------------- -/

structure EdmontDefs where
  -- @@FIELDS
  mcurve_of_ecurve : thm
  montgomery_of_edwards : thm
  ecurve_of_mcurve : thm
  edwards_of_montgomery : thm
  ECURVE_OF_MCURVE_OF_ECURVE : thm
  MCURVE_OF_ECURVE_OF_MCURVE : thm
  MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR_EQ : thm
  MCURVE_OF_ECURVE_NONSINGULAR_EQ : thm
  MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR : thm
  MCURVE_OF_ECURVE_NONSINGULAR : thm
  deriving Inhabited

@[nospecialize]
def setupEdmontDefs [HolBase] (D : EdmontDeps) :
    ExceptT String IO EdmontDefs := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, FIELD_TAC, NOT_RING_CHAR_DIVIDES_TAC, RING_CARRIER_TAC, TAUT,
        define, .. } := D
  let { CONTRAPOS_THM, FIELD_CHAR_NOT2, IMP_CONJ, LEFT_IMP_EXISTS_THM,
        MONTGOMERY_STRONGLY_NONSINGULAR_IMP_NONSINGULAR, PAIR_EQ, RING_POW_2,
        edwards_nonsingular, montgomery_nonsingular, montgomery_strongly_nonsingular, .. } := D.core1
  -- @@SCOPE END

  /- Map from Edwards(a,d) to Montgomery(A,B) where

             A = 2 * (a + d) / (a - d)
             B = (4 / (a - d)) / c^2

     defined by

             (x,y) |-> ((1 + y) / (1 - y), c * (1 + y) / ((1 - y) * x))

     Here c is an arbitrary (nonzero) parameter giving a scaling factor. -/

  let mcurve_of_ecurve ← define
   r"mcurve_of_ecurve (f,(a:A),d) c =
        (f,
         ring_div f (ring_mul f (ring_of_num f 2) (ring_add f a d))
                    (ring_sub f a d),
         ring_div f
          (ring_div f (ring_of_num f 4) (ring_sub f a d))
          (ring_pow f c 2))"

  let montgomery_of_edwards ← define
   r"montgomery_of_edwards(f:A ring) c (x,y) =
        if (x,y) = (ring_0 f,ring_1 f) then
           NONE
        else if (x,y) = (ring_0 f,ring_neg f (ring_1 f)) then
           SOME(ring_0 f,ring_0 f)
        else
           SOME(ring_div f (ring_add f (ring_1 f) y) (ring_sub f (ring_1 f) y),
                ring_mul f c
                 (ring_div f (ring_add f (ring_1 f) y)
                             (ring_mul f x (ring_sub f (ring_1 f) y))))"

  /- Mapping from Montgomery(A,B) to Edwards(a,d) where

             a = ((A + 2) / B) / c^2
             d = ((A - 2) / B) / c^2

     defined by
             (x,y) |-> (c * x / y, (x - 1) / (x + 1))

     Here c is an arbitrary (nonzero) parameter giving a scaling factor. -/

  let ecurve_of_mcurve ← define
   r"ecurve_of_mcurve (f,A:A,B) c =
        (f,
         ring_div f (ring_div f (ring_add f A (ring_of_num f 2)) B)
                    (ring_pow f c 2),
         ring_div f (ring_div f (ring_sub f A (ring_of_num f 2)) B)
                    (ring_pow f c 2))"

  let edwards_of_montgomery ← define
   r"edwards_of_montgomery(f:A ring) c NONE =
    (ring_0 f,ring_1 f) /\
  edwards_of_montgomery(f:A ring) c (SOME(x,y)) =
    if (x,y) = (ring_0 f,ring_0 f) then (ring_0 f,ring_neg f (ring_1 f))
    else ring_mul f c (ring_div f x y),
         ring_div f (ring_sub f x (ring_of_num f 1))
                    (ring_add f x (ring_of_num f 1))"

  /- Curve mapping interactions, in particular with respect to singularity. -/

  let ECURVE_OF_MCURVE_OF_ECURVE ← prove
   r"!f a d c:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        c IN ring_carrier f /\ ~(c = ring_0 f) /\
        ~(a = d)
        ==> ecurve_of_mcurve (mcurve_of_ecurve (f,a,d) c) c = (f,a,d)"
   (← do
    pure (REWRITE_TAC [FIELD_CHAR_NOT2] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [mcurve_of_ecurve, ecurve_of_mcurve, PAIR_EQ] THEN
    FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  let MCURVE_OF_ECURVE_OF_MCURVE ← prove
   r"!f A B c:A.
        field f /\ ~(ring_char f = 2) /\
        A IN ring_carrier f /\ B IN ring_carrier f /\
        c IN ring_carrier f /\ ~(c = ring_0 f) /\
        ~(B = ring_0 f)
        ==> mcurve_of_ecurve (ecurve_of_mcurve (f,A,B) c) c = (f,A,B)"
   (← do
    pure (REWRITE_TAC [FIELD_CHAR_NOT2] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [mcurve_of_ecurve, ecurve_of_mcurve, PAIR_EQ] THEN
    FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  let MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR_EQ ← prove
   r"!f a d c:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        c IN ring_carrier f /\ ~(c = ring_0 f)
        ==> (montgomery_strongly_nonsingular(mcurve_of_ecurve(f,a,d) c) <=>
             ~(?z. z IN ring_carrier f /\ ring_pow f z 2 = ring_mul f a d))"
   (← do
    let t1 ← TAUT
     (← q r"!p'. (p' <=> p) /\ (p' ==> r) /\ (~p' ==> (q <=> r))
         ==> (~p /\ ~q <=> ~r)")
    pure (REWRITE_TAC [FIELD_CHAR_NOT2] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [montgomery_strongly_nonsingular, mcurve_of_ecurve] THEN
    MATCH_MP_TAC t1 THEN
    EXISTS_TAC (← q r"a:A = d") THEN REPEAT CONJ_TAC THENL
     [FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC,
      ASM_MESON_TAC [RING_POW_2],
      DISCH_TAC] THEN
    EQ_TAC THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"z:A") STRIP_ASSUME_TAC) THENL
     [EXISTS_TAC
       (← q r"ring_mul f (z:A) (ring_div f (ring_sub f a d) (ring_of_num f 4))"),
      EXISTS_TAC
       (← q r"ring_mul f (z:A) (ring_div f (ring_of_num f 4) (ring_sub f a d) )")] THEN
    REPEAT CONJ_TAC THEN TRY RING_CARRIER_TAC THEN
    FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  let MCURVE_OF_ECURVE_NONSINGULAR_EQ ← prove
   r"!f a d c:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        c IN ring_carrier f /\ ~(c = ring_0 f)
        ==> (montgomery_nonsingular(mcurve_of_ecurve(f,a,d) c) <=>
             ~(a = d) /\ ~(a = ring_0 f) /\ ~(d = ring_0 f))"
   (← do
    pure (REWRITE_TAC [FIELD_CHAR_NOT2] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [montgomery_nonsingular, mcurve_of_ecurve] THEN
    FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  let MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR ← prove
   r"!f a d c:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        c IN ring_carrier f /\ ~(c = ring_0 f) /\
        ~(a = ring_0 f) /\ ~(d = ring_0 f) /\
        edwards_nonsingular(f,a,d)
        ==> montgomery_strongly_nonsingular(mcurve_of_ecurve(f,a,d) c)"
   (← do
    pure (SIMP_TAC [MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR_EQ] THEN
    REWRITE_TAC [FIELD_CHAR_NOT2] THEN REPEAT GEN_TAC THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_REWRITE_TAC [edwards_nonsingular, IMP_CONJ, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"b:A") THEN DISCH_TAC THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC [CONTRAPOS_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"z:A") THEN STRIP_TAC THEN EXISTS_TAC (← q r"ring_div f z b:A") THEN
     REPEAT CONJ_TAC THEN TRY RING_CARRIER_TAC THEN
    FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  let MCURVE_OF_ECURVE_NONSINGULAR ← prove
   r"!f a d c:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        c IN ring_carrier f /\ ~(c = ring_0 f) /\
        ~(a = ring_0 f) /\ ~(d = ring_0 f) /\
        edwards_nonsingular(f,a,d)
        ==> montgomery_nonsingular(mcurve_of_ecurve(f,a,d) c)"
   (← do
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [mcurve_of_ecurve] THEN
    MATCH_MP_TAC MONTGOMERY_STRONGLY_NONSINGULAR_IMP_NONSINGULAR THEN
    REPEAT CONJ_TAC THEN TRY RING_CARRIER_TAC THEN
    REWRITE_TAC [← GSYM mcurve_of_ecurve] THEN
    MATCH_MP_TAC MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR THEN
    ASM_REWRITE_TAC []))

  -- @@RETURN BEGIN
  return { mcurve_of_ecurve, montgomery_of_edwards, ecurve_of_mcurve,
           edwards_of_montgomery, ECURVE_OF_MCURVE_OF_ECURVE, MCURVE_OF_ECURVE_OF_MCURVE,
           MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR_EQ, MCURVE_OF_ECURVE_NONSINGULAR_EQ,
           MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR, MCURVE_OF_ECURVE_NONSINGULAR }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Interrelations of the mappings themselves.  (edmont.ml 166-287)           -/
/- ------------------------------------------------------------------------- -/

structure EdmontMaps where
  -- @@FIELDS
  MONTGOMERY_OF_EDWARDS : thm
  EDWARDS_OF_MONTGOMERY_OF_EDWARDS : thm
  EDWARDS_OF_MONTGOMERY : thm
  MONTGOMERY_OF_EDWARDS_OF_MONTGOMERY : thm
  deriving Inhabited

@[nospecialize]
def setupEdmontMaps [HolBase] (D : EdmontDeps) (BEdmontDefs : EdmontDefs) :
    ExceptT String IO EdmontMaps := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, FIELD_TAC, NOT_RING_CHAR_DIVIDES_TAC, RING_CARRIER_TAC, TAUT, .. } := D
  let { DE_MORGAN_THM, DIVIDES_REFL, FIELD_CHAR_NOT2, FORALL_OPTION_THM,
        FORALL_PAIR_THM, MONTGOMERY_STRONGLY_NONSINGULAR, PAIR_EQ, edwards_curve,
        edwards_nonsingular, montgomery_curve, option_DISTINCT, option_INJ, .. } := D.core1
  let { ecurve_of_mcurve, edwards_of_montgomery, mcurve_of_ecurve,
        montgomery_of_edwards, .. } := BEdmontDefs
  -- @@SCOPE END

  let MONTGOMERY_OF_EDWARDS ← prove
   r"!f (a:A) d c p.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\ c IN ring_carrier f /\
        ~(a = d) /\ ~(c = ring_0 f) /\
        edwards_curve(f,a,d) p
        ==> montgomery_curve (mcurve_of_ecurve(f,a,d) c)
                             (montgomery_of_edwards f c p)"
   (← do
    pure (REWRITE_TAC [FIELD_CHAR_NOT2] THEN REWRITE_TAC [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"c:A", ← q r"x:A",
                         ← q r"y:A"] THEN
    REWRITE_TAC [edwards_curve, mcurve_of_ecurve, montgomery_of_edwards] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC [PAIR_EQ] THEN ASM_CASES_TAC (← q r"x:A = ring_0 f") THEN
    ASM_REWRITE_TAC [montgomery_curve] THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC [montgomery_curve] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [montgomery_curve] THEN
      REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC,
      REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC THEN
      NOT_RING_CHAR_DIVIDES_TAC]))

  let EDWARDS_OF_MONTGOMERY_OF_EDWARDS ← prove
   r"!(f:A ring) a d c p.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\ c IN ring_carrier f /\
        ~(a = d) /\ ~(c = ring_0 f) /\
        edwards_curve(f,a,d) p
        ==> edwards_of_montgomery f c (montgomery_of_edwards f c p) = p"
   (← do
    let t1 ← TAUT (← q r"~p ==> p ==> q")
    pure (REWRITE_TAC [FIELD_CHAR_NOT2] THEN REWRITE_TAC [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"c:A", ← q r"x:A",
                         ← q r"y:A"] THEN
    REWRITE_TAC [edwards_curve, montgomery_of_edwards, PAIR_EQ] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_CASES_TAC (← q r"x:A = ring_0 f") THEN
    ASM_REWRITE_TAC [edwards_of_montgomery] THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC [edwards_of_montgomery] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [edwards_of_montgomery] THEN
      MATCH_MP_TAC t1 THEN FIELD_TAC,
      REWRITE_TAC [PAIR_EQ] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [PAIR_EQ] THEN FIELD_TAC THEN
      NOT_RING_CHAR_DIVIDES_TAC]))

  let EDWARDS_OF_MONTGOMERY ← prove
   r"!f (A:A) B c p.
        field f /\ ~(ring_char f = 2) /\
        A IN ring_carrier f /\ B IN ring_carrier f /\ c IN ring_carrier f /\
        ~(B = ring_0 f) /\ ~(c = ring_0 f) /\
        montgomery_strongly_nonsingular(f,A,B) /\
        edwards_nonsingular(ecurve_of_mcurve(f,A,B) c) /\
        montgomery_curve(f,A,B) p
        ==> edwards_curve (ecurve_of_mcurve(f,A,B) c)
                          (edwards_of_montgomery f c p)"
   (← do
    let t1 ← TAUT (← q r"F ==> p")
    pure (MAP_EVERY X_GEN_TAC [← q r"f:A ring", ← q r"A:A", ← q r"B:A", ← q r"c:A"] THEN
    REWRITE_TAC [FIELD_CHAR_NOT2] THEN
    REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN CONJ_TAC THENL
     [REWRITE_TAC [edwards_curve, ecurve_of_mcurve, edwards_of_montgomery] THEN
      REWRITE_TAC [montgomery_curve] THEN REPEAT STRIP_TAC THEN
      TRY RING_CARRIER_TAC THEN FIELD_TAC,
      MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"]] THEN
    REWRITE_TAC [montgomery_curve, edwards_of_montgomery, PAIR_EQ] THEN
    STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [edwards_curve, ecurve_of_mcurve] THENL
     [REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC, ALL_TAC] THEN
    REPEAT (CONJ_TAC THENL [RING_CARRIER_TAC, ALL_TAC]) THEN
    ASM_CASES_TAC (← q r"y:A = ring_0 f") THENL
     [MP_TAC (← ISPECL [← q r"f:A ring", ← q r"A:A", ← q r"B:A"]
       MONTGOMERY_STRONGLY_NONSINGULAR) THEN
      ASM_REWRITE_TAC [] THEN
      ANTS_TAC THENL [ASM_MESON_TAC [DIVIDES_REFL], ALL_TAC] THEN
      DISCH_THEN (MP_TAC o SPECL [← q r"x:A", ← q r"y:A"]) THEN
      ASM_REWRITE_TAC [montgomery_curve] THEN ASM_MESON_TAC [],
      FIRST_X_ASSUM (fun th => tactic_of do
        let _ ← GEN_REWRITE_RULE I [DE_MORGAN_THM] th; pure ALL_TAC)] THEN
    ASM_CASES_TAC (← q r"x:A = ring_neg f (ring_1 f)") THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC t1,
      REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC THEN
      NOT_RING_CHAR_DIVIDES_TAC] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [edwards_nonsingular, ecurve_of_mcurve]) THEN
    FIRST_X_ASSUM (MP_TAC o CONJUNCT2) THEN REWRITE_TAC [DE_MORGAN_THM] THEN
    CONJ_TAC THENL [FIELD_TAC, ALL_TAC] THEN
    EXISTS_TAC (← q r"ring_div f y c:A") THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC THEN
    NOT_RING_CHAR_DIVIDES_TAC))

  let MONTGOMERY_OF_EDWARDS_OF_MONTGOMERY ← prove
   r"!f (A:A) B c p.
        field f /\ ~(ring_char f = 2) /\
        A IN ring_carrier f /\ B IN ring_carrier f /\ c IN ring_carrier f /\
        ~(B = ring_0 f) /\ ~(c = ring_0 f) /\
        montgomery_strongly_nonsingular(f,A,B) /\
        edwards_nonsingular(ecurve_of_mcurve(f,A,B) c) /\
        montgomery_curve(f,A,B) p
        ==> montgomery_of_edwards f c (edwards_of_montgomery f c p) = p"
   (← do
    let t1 ← TAUT (← q r"F ==> p")
    pure (MAP_EVERY X_GEN_TAC [← q r"f:A ring", ← q r"A:A", ← q r"B:A", ← q r"c:A"] THEN
    REWRITE_TAC [FIELD_CHAR_NOT2] THEN
    REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, montgomery_curve] THEN
    REWRITE_TAC [edwards_of_montgomery, montgomery_of_edwards, PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN STRIP_TAC THEN
    REPEAT (COND_CASES_TAC THEN
           ASM_REWRITE_TAC [montgomery_of_edwards, PAIR_EQ,
                            option_DISTINCT, option_INJ])
    THENL [FIELD_TAC, FIELD_TAC, FIELD_TAC, ALL_TAC] THEN
    ASM_CASES_TAC (← q r"y:A = ring_0 f") THENL
     [MP_TAC (← ISPECL [← q r"f:A ring", ← q r"A:A", ← q r"B:A"]
       MONTGOMERY_STRONGLY_NONSINGULAR) THEN
      ASM_REWRITE_TAC [] THEN
      ANTS_TAC THENL [ASM_MESON_TAC [DIVIDES_REFL], ALL_TAC] THEN
      DISCH_THEN (MP_TAC o SPECL [← q r"x:A", ← q r"y:A"]) THEN
      ASM_REWRITE_TAC [montgomery_curve] THEN FIELD_TAC,
      FIRST_X_ASSUM (fun th => tactic_of do
        let _ ← GEN_REWRITE_RULE I [DE_MORGAN_THM] th; pure ALL_TAC)] THEN
    ASM_CASES_TAC (← q r"x:A = ring_neg f (ring_1 f)") THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC t1,
      REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC THEN
      NOT_RING_CHAR_DIVIDES_TAC] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [edwards_nonsingular, ecurve_of_mcurve]) THEN
    FIRST_X_ASSUM (MP_TAC o CONJUNCT2) THEN REWRITE_TAC [DE_MORGAN_THM] THEN
    CONJ_TAC THENL [FIELD_TAC, ALL_TAC] THEN
    EXISTS_TAC (← q r"ring_div f y c:A") THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC THEN
    NOT_RING_CHAR_DIVIDES_TAC))

  -- @@RETURN BEGIN
  return { MONTGOMERY_OF_EDWARDS, EDWARDS_OF_MONTGOMERY_OF_EDWARDS,
           EDWARDS_OF_MONTGOMERY, MONTGOMERY_OF_EDWARDS_OF_MONTGOMERY }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Group isomorphisms: negation, and the isomorphism between the Edwards and -/
/- Montgomery groups.  (edmont.ml 288-595)                                   -/
/- ------------------------------------------------------------------------- -/

structure EdmontIso where
  -- @@FIELDS
  MONTGOMERY_OF_EDWARDS_NEG : thm
  GROUP_ISOMORPHISMS_EDWARDS_MONTGOMERY_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupEdmontIso [HolBase] (D : EdmontDeps) (BEdmontDefs : EdmontDefs) (BEdmontMaps : EdmontMaps) :
    ExceptT String IO EdmontIso := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, FIELD_TAC, GROUP_RULE, INTEGRAL_DOMAIN_RULE, LET_TAC,
        NOT_RING_CHAR_DIVIDES_TAC, RING_CARRIER_TAC, RING_PULL_DIV_TAC, RING_RULE,
        RING_TAC, SET_RULE, TAUT, basic_ss, let_CONV, .. } := D
  let { ABELIAN_EDWARDS_GROUP, ABELIAN_MONTGOMERY_GROUP, CONJ_ASSOC, DE_MORGAN_THM,
        EDWARDS_GROUP, EDWARDS_NONSINGULAR_DENOMINATORS, FIELD_CHAR_NOT2,
        FIELD_IMP_INTEGRAL_DOMAIN, FIELD_INV_EQ_0, FIELD_MUL_EQ_0, FIELD_POW_EQ_0,
        FORALL_IN_IMAGE, FORALL_OPTION_THM, FORALL_PAIR_THM, GROUP_HOMOMORPHISM,
        GROUP_INV, GROUP_ISOMORPHISMS, GROUP_LID_EQ, GROUP_MUL, GROUP_MUL_ASSOC,
        GROUP_MUL_LCANCEL, GROUP_MUL_LID, GROUP_MUL_RID, GROUP_RINV_EQ, IMP_CONJ_ALT,
        IMP_IMP, MONTGOMERY_GROUP, PAIR_EQ, PRIME_2, RING_0, RING_1, RING_ADD_LZERO,
        RING_ADD_RZERO, RING_CHAR_DIVIDES_PRIME, RING_CLAUSES, RING_DIV_1, RING_INV,
        RING_INV_MUL, RING_MUL, RING_MUL_LID, RING_MUL_LNEG, RING_MUL_LZERO,
        RING_MUL_RID, RING_MUL_RNEG, RING_MUL_RZERO, RING_NEG, RING_NEG_EQ,
        RING_NEG_EQ_0, RING_NEG_NEG, RING_OF_NUM_EQ_0, RING_POW, RING_POW_2, RING_SUB,
        RING_SUB_EQ_0, RING_SUB_RZERO, SUBSET, abelian_group, edwards_0, edwards_add,
        edwards_curve, edwards_neg, montgomery_add, montgomery_curve, montgomery_neg,
        option_DISTINCT, option_INJ, ring_div, .. } := D.core1
  let { ECURVE_OF_MCURVE_OF_ECURVE, MCURVE_OF_ECURVE_NONSINGULAR,
        MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR, mcurve_of_ecurve, montgomery_of_edwards, .. } := BEdmontDefs
  let { EDWARDS_OF_MONTGOMERY, EDWARDS_OF_MONTGOMERY_OF_EDWARDS, MONTGOMERY_OF_EDWARDS,
        MONTGOMERY_OF_EDWARDS_OF_MONTGOMERY, .. } := BEdmontMaps
  -- @@SCOPE END
  -- `check (fun eq -> is_eq eq && rand eq = t) o concl`
  let eqRandIs (t : term) (th : thm) : Bool :=
    is_eq (concl th) &&
      (match rand (concl th) with
       | .ok r => r == t
       | .error _ => false)

  let MONTGOMERY_OF_EDWARDS_NEG ← prove
   r"!f (a:A) d c p.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\ c IN ring_carrier f /\
        edwards_curve(f,a,d) p
        ==> montgomery_of_edwards f c (edwards_neg(f,a,d) p) =
            montgomery_neg (mcurve_of_ecurve(f,a,d) c)
                           (montgomery_of_edwards f c p)"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"c:A", ← q r"x:A",
                         ← q r"y:A"] THEN
    REWRITE_TAC [edwards_curve, mcurve_of_ecurve, montgomery_of_edwards] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC [PAIR_EQ] THEN ASM_CASES_TAC (← q r"x:A = ring_0 f") THEN
    ASM_REWRITE_TAC [edwards_neg, montgomery_of_edwards] THEN
    ASM_SIMP_TAC [PAIR_EQ, RING_NEG_EQ_0, RING_0] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [montgomery_neg]) THEN
    REWRITE_TAC [option_INJ, PAIR_EQ, montgomery_neg] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC))

  let GROUP_ISOMORPHISMS_EDWARDS_MONTGOMERY_GROUP ← prove
   r"!f (a:A) d c.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\ c IN ring_carrier f /\
        ~(a = d) /\ ~(a = ring_0 f) /\ ~(d = ring_0 f) /\ ~(c = ring_0 f) /\
        edwards_nonsingular(f,a,d)
        ==> group_isomorphisms (edwards_group(f,a,d),
                                montgomery_group(mcurve_of_ecurve(f,a,d) c))
                               (montgomery_of_edwards f c,
                                edwards_of_montgomery f c)"
   (← do
    -- `let isolemma = prove ... in`: proved first; inside it, right to
    -- left, the second GROUP_RULE and then the first
    let isolemma ← prove
     r"!(G:A group) (H:B group) f g z.
          abelian_group G /\ abelian_group H /\
          z IN group_carrier G /\ ~(z = group_id G) /\
          (!x. x IN group_carrier G
               ==> f(x) IN group_carrier H /\ g(f x) = x) /\
          (!y. y IN group_carrier H
               ==> g(y) IN group_carrier G /\ f(g y) = y) /\
          f(group_id G) = group_id H /\
          (!x. x IN group_carrier G ==> f(group_inv G x) = group_inv H (f x)) /\
          (!x. x IN group_carrier G
               ==> f(group_mul G z x) = group_mul H (f z) (f x)) /\
          (!u v w. u IN group_carrier G /\ ~(u = group_id G) /\ ~(u = z) /\
                   v IN group_carrier G /\ ~(v = group_id G) /\ ~(v = z) /\
                   w IN group_carrier G /\ ~(w = group_id G) /\ ~(w = z) /\
                   group_mul G u v = w /\
                   ~(f v = f u) /\ ~(group_inv H (f v) = f u)
                   ==> group_mul H (f u) (f v) = f w)
          ==> group_isomorphisms (G,H) (f,g)"
     (← do
      let g2 ← GROUP_RULE
        (← q r"group_mul G x y = z <=> x = group_mul G z (group_inv G y)")
      let g1 ← GROUP_RULE
        (← q r"group_id G = group_mul G a b <=> group_inv G b = a")
      pure (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [GROUP_ISOMORPHISMS] THEN
      ASM_SIMP_TAC [GROUP_HOMOMORPHISM, SUBSET, FORALL_IN_IMAGE] THEN
      SUBGOAL_THEN
       (← q r"!x y. x IN group_carrier G /\ y IN group_carrier G /\ ~(x = y)
              ==> (f:A->B) (group_mul G x y) = group_mul H (f x) (f y)")
      ASSUME_TAC THENL
       [MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN STRIP_TAC THEN
        ASM_CASES_TAC (← q r"x:A = group_id G") THENL
         [ASM_SIMP_TAC [GROUP_MUL_LID], ALL_TAC] THEN
        ASM_CASES_TAC (← q r"x:A = z") THENL
         [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN
        ASM_CASES_TAC (← q r"y:A = group_id G") THENL
         [ASM_SIMP_TAC [GROUP_MUL_RID], ALL_TAC] THEN
        ASM_CASES_TAC (← q r"y:A = z") THENL
         [RULE_ASSUM_TAC (REWRITE_RULE [abelian_group]) THEN
          ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN
        ASM_CASES_TAC (← q r"group_mul G x y:A = group_id G") THENL
         [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [g1],
          ALL_TAC] THEN
        ASM_CASES_TAC (← q r"group_mul G x y:A = z") THENL
         [ASM_REWRITE_TAC [] THEN CONV_TAC SYM_CONV THEN POP_ASSUM MP_TAC THEN
          ASM_SIMP_TAC [GROUP_INV, g2],
          ALL_TAC] THEN
        CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC [GROUP_MUL] THEN
        UNDISCH_TAC (← q r"~(group_mul G x y:A = group_id G)") THEN
        ASM_SIMP_TAC [← GSYM GROUP_RINV_EQ] THEN ASM_MESON_TAC [GROUP_INV],
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN STRIP_TAC THEN
      ASM_CASES_TAC (← q r"x:A = y") THEN ASM_SIMP_TAC [] THEN
      UNDISCH_THEN (← q r"x:A = y") (SUBST_ALL_TAC o SYM) THEN
      ASM_CASES_TAC (← q r"x:A = z") THEN ASM_SIMP_TAC [] THEN
      SUBGOAL_THEN
       (← q r"(f:A->B) (group_mul G (group_mul G z x) x) =
        group_mul H (f(group_mul G z x)) (f x)")
      MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [GROUP_LID_EQ, GROUP_MUL],
        ASM_SIMP_TAC [← GSYM GROUP_MUL_ASSOC, GROUP_MUL]] THEN
      ASM_SIMP_TAC [GROUP_MUL_LCANCEL, GROUP_MUL]))
    -- the main tactic, right to left: basic_ss, the INTEGRAL_DOMAIN_RULEs,
    -- then the TAUTs, RING_RULEs and SET_RULEs from the end backwards
    let ss ← ExceptT.mk (basic_ss [])
    let id550 ← INTEGRAL_DOMAIN_RULE
     (← q r"~(a = ring_0 f) /\ ring_mul f a x = ring_mul f a y ==> x = y")
    let id547 ← INTEGRAL_DOMAIN_RULE
     (← q r"~(x = y) /\ ~(ring_neg f x = y) <=>
      ~(ring_pow f x 2 = ring_pow f y 2)")
    let t546 ← TAUT (← q r"~p ==> p ==> q")
    let t485 ← TAUT (← q r"p \/ q ==> ~p /\ ~q /\ r ==> s")
    let t477 ← TAUT (← q r"p \/ q ==> ~p /\ ~q /\ r ==> s")
    let t469 ← TAUT (← q r"p \/ q ==> ~p /\ ~q /\ r ==> s")
    let r444 ← RING_RULE
     (← q r"ring_add f x (ring_neg f y) = ring_sub f x y /\
      ring_sub f x (ring_neg f y) = ring_add f x y")
    let t441 ← TAUT (← q r"F ==> p")
    let r437 ← RING_RULE
     (← q r"ring_neg f y = ring_1 f <=> y = ring_neg f (ring_1 f)")
    let t427 ← TAUT (← q r"F ==> p")
    let s397 ← SET_RULE (← q r"y IN montgomery_curve C <=> montgomery_curve C y")
    let s396 ← SET_RULE (← q r"x IN edwards_curve C <=> edwards_curve C x")
    let t388 ← TAUT
     (← q r"p /\ (q /\ r ==> s) ==> (p ==> q) ==> (p ==> r) ==> s")
    let mcArgs := striplist HolMath.Pair.dest_pair
      (← liftExcept (rand (concl mcurve_of_ecurve)))
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC isolemma THEN
    EXISTS_TAC (← q r"ring_0 f:A,ring_neg f (ring_1 f)") THEN
    ASM_SIMP_TAC [ABELIAN_EDWARDS_GROUP, EDWARDS_GROUP] THEN
    MP_TAC (← ISPECL mcArgs
                  MONTGOMERY_GROUP) THEN
    MP_TAC (← ISPECL mcArgs
                  ABELIAN_MONTGOMERY_GROUP) THEN
    ASM_REWRITE_TAC [← GSYM mcurve_of_ecurve] THEN MATCH_MP_TAC t388 THEN
    CONJ_TAC THENL
     [REPEAT CONJ_TAC THEN TRY RING_CARRIER_TAC THEN
      MATCH_MP_TAC MCURVE_OF_ECURVE_NONSINGULAR THEN ASM_REWRITE_TAC [],
      DISCH_THEN (fun th => REWRITE_TAC [th])] THEN
    UNDISCH_TAC (← q r"~(ring_char(f:A ring) = 2)") THEN
    ASM_SIMP_TAC [← GSYM RING_CHAR_DIVIDES_PRIME, PRIME_2] THEN DISCH_TAC THEN
    REWRITE_TAC [s396] THEN
    REWRITE_TAC [s397] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [edwards_curve] THEN REPEAT CONJ_TAC THEN
      TRY RING_CARRIER_TAC THEN FIELD_TAC,
      REWRITE_TAC [edwards_0, PAIR_EQ] THEN FIELD_TAC,
      ASM_MESON_TAC [EDWARDS_OF_MONTGOMERY_OF_EDWARDS, MONTGOMERY_OF_EDWARDS,
                     RING_CHAR_DIVIDES_PRIME, PRIME_2],
      MP_TAC (← ISPECL [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"c:A"]
          ECURVE_OF_MCURVE_OF_ECURVE) THEN
      ASM_SIMP_TAC [← GSYM RING_CHAR_DIVIDES_PRIME, PRIME_2] THEN DISCH_TAC THEN
      GEN_TAC THEN REWRITE_TAC [mcurve_of_ecurve] THEN REPEAT STRIP_TAC THENL
       [FIRST_ASSUM (MP_TAC o MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ_ALT]
          (← REWRITE_RULE [CONJ_ASSOC] EDWARDS_OF_MONTGOMERY))),
        FIRST_ASSUM (MP_TAC o MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ_ALT]
          (← REWRITE_RULE [CONJ_ASSOC] MONTGOMERY_OF_EDWARDS_OF_MONTGOMERY)))] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"c:A")) THEN
      ASM_REWRITE_TAC [← GSYM mcurve_of_ecurve] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC [MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR,
                    ← GSYM RING_CHAR_DIVIDES_PRIME, PRIME_2] THEN
      REPEAT CONJ_TAC THEN TRY RING_CARRIER_TAC THEN
      FIRST_X_ASSUM (fun th => tactic_of do let _ ← SYM th; pure ALL_TAC) THEN
      FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC,
      REWRITE_TAC [montgomery_of_edwards, edwards_0],
      ASM_SIMP_TAC [MONTGOMERY_OF_EDWARDS_NEG],
      GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"x2:A", ← q r"y2:A"] THEN
      REWRITE_TAC [PAIR_EQ, edwards_curve] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [montgomery_of_edwards, PAIR_EQ] THEN
      ASM_CASES_TAC (← q r"ring_neg f (ring_1 f):A = ring_1 f") THENL
       [MATCH_MP_TAC t427 THEN FIELD_TAC,
        ASM_REWRITE_TAC []] THEN
      COND_CASES_TAC THEN
      REWRITE_TAC [edwards_add, montgomery_add, montgomery_of_edwards,
                   mcurve_of_ecurve] THEN
      ASM_SIMP_TAC [RING_MUL_LZERO, RING_0, RING_1, RING_NEG, RING_MUL_RZERO,
                    RING_ADD_LZERO, RING_ADD_RZERO, RING_MUL_LID, RING_MUL_RID,
                    RING_MUL, RING_DIV_1, RING_SUB_RZERO, PAIR_EQ,
                    FIELD_MUL_EQ_0, RING_NEG_EQ_0, RING_MUL_LNEG,
                    RING_MUL_RNEG, RING_NEG_NEG] THEN
      ASM_SIMP_TAC [RING_NEG_EQ, RING_1, r437] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [montgomery_add] THEN
      COND_CASES_TAC THENL
       [MATCH_MP_TAC t441 THEN
        FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC,
        ALL_TAC] THEN
      ASM_SIMP_TAC [RING_1, r444] THEN
      SUBGOAL_THEN
       (← q r"~(x2:A = ring_0 f) /\
        ~(ring_sub f (ring_1 f) y2 = ring_0 f) /\
        ~(ring_add f (ring_1 f) y2 = ring_0 f) /\
        ~(ring_sub f a d = ring_0 f)")
      STRIP_ASSUME_TAC THENL
       [FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC,
        REPEAT (FIRST_X_ASSUM (fun th => tactic_of do
           let _ ← GEN_REWRITE_RULE I [DE_MORGAN_THM] th; pure ALL_TAC))] THEN
      REPLICATE_TAC 3
       (RING_PULL_DIV_TAC THEN CONV_TAC (RAND_CONV let_CONV)) THEN
      REWRITE_TAC [option_INJ, PAIR_EQ] THEN
      RING_PULL_DIV_TAC THEN FIELD_TAC THEN
      NOT_RING_CHAR_DIVIDES_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"x1:A", ← q r"y1:A", ← q r"x2:A", ← q r"y2:A", ← q r"x3:A",
                         ← q r"y3:A"] THEN
    REWRITE_TAC [edwards_curve, edwards_0, PAIR_EQ] THEN
    DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ASM_CASES_TAC
     (← q r"x1:A = ring_0 f \/ y1 = ring_1 f \/ y1 = ring_neg f (ring_1 f)")
    THENL
     [MATCH_MP_TAC t469 THEN FIELD_TAC,
      FIRST_X_ASSUM (CONJUNCTS_THEN STRIP_ASSUME_TAC o
        REWRITE_RULE [DE_MORGAN_THM]) THEN
      ASM_REWRITE_TAC []] THEN
    DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ASM_CASES_TAC
     (← q r"x2:A = ring_0 f \/ y2 = ring_1 f \/ y2 = ring_neg f (ring_1 f)")
    THENL
     [MATCH_MP_TAC t477 THEN FIELD_TAC,
      FIRST_X_ASSUM (CONJUNCTS_THEN STRIP_ASSUME_TAC o
        REWRITE_RULE [DE_MORGAN_THM]) THEN
      ASM_REWRITE_TAC []] THEN
    DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ASM_CASES_TAC
     (← q r"x3:A = ring_0 f \/ y3 = ring_1 f \/ y3 = ring_neg f (ring_1 f)")
    THENL
     [MATCH_MP_TAC t485 THEN FIELD_TAC,
      FIRST_X_ASSUM (CONJUNCTS_THEN STRIP_ASSUME_TAC o
        REWRITE_RULE [DE_MORGAN_THM]) THEN
      ASM_REWRITE_TAC []] THEN
    ABBREV_TAC (← q r"p3 = montgomery_of_edwards f (c:A) (x3,y3)") THEN
    ABBREV_TAC (← q r"p2 = montgomery_of_edwards f (c:A) (x2,y2)") THEN
    ABBREV_TAC (← q r"p1 = montgomery_of_edwards f (c:A) (x1,y1)") THEN
    MP_TAC (← ISPECL [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"c:A"]
      MONTGOMERY_OF_EDWARDS) THEN
    REWRITE_TAC [FIELD_CHAR_NOT2] THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← HolLight.end_itlist CONJ
          (← [← q r"x1:A,y1:A", ← q r"x2:A,y2:A", ← q r"x3:A,y3:A"].mapM
               (fun t => SPEC t th))))) THEN
    ASM_REWRITE_TAC [edwards_curve] THEN
    REPLICATE_TAC 3 (POP_ASSUM MP_TAC) THEN
    REPLICATE_TAC 2 (ONCE_REWRITE_TAC [IMP_IMP]) THEN
    REWRITE_TAC [← GSYM CONJ_ASSOC] THEN
    MAP_EVERY (fun t => SPEC_TAC (t, t))
      [← q r"p3:(A#A)option", ← q r"p2:(A#A)option", ← q r"p1:(A#A)option"] THEN
    ASM_REWRITE_TAC [montgomery_of_edwards, PAIR_EQ] THEN
    REWRITE_TAC [FORALL_OPTION_THM, option_DISTINCT] THEN
    REWRITE_TAC [FORALL_PAIR_THM, option_INJ, PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [← q r"u1:A", ← q r"v1:A", ← q r"u2:A", ← q r"v2:A", ← q r"u3:A",
                         ← q r"v3:A"] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"(u1:A) IN ring_carrier f /\ (v1:A) IN ring_carrier f /\
      (u2:A) IN ring_carrier f /\ (v2:A) IN ring_carrier f /\
      (u3:A) IN ring_carrier f /\ (v3:A) IN ring_carrier f")
    STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN RING_CARRIER_TAC, ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"ring_mul f (ring_div f c x1) u1:A = v1 /\
      ring_mul f (ring_div f c x2) u2:A = v2 /\
      ring_mul f (ring_div f c x3) u3:A = v3")
    MP_TAC THENL
     [REPEAT CONJ_TAC THEN
      FIRST_X_ASSUM (fun th => tactic_of do
         pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← SYM th])) THEN
      FIRST_X_ASSUM (fun th => tactic_of do
         pure (GEN_REWRITE_TAC RAND_CONV [← SYM th])) THEN
      ASM_SIMP_TAC [ring_div, RING_INV_MUL, RING_INV, RING_POW,
                    RING_MUL, RING_SUB, RING_1] THEN
      RING_TAC THEN REPEAT CONJ_TAC THEN RING_CARRIER_TAC,
      MAP_EVERY (fun t => FIRST_X_ASSUM (fun th => tactic_of do
         let _ ← liftExcept (check (eqRandIs t) th); pure ALL_TAC))
       [← q r"v1:A", ← q r"v2:A", ← q r"v3:A"] THEN STRIP_TAC] THEN
    ASM_REWRITE_TAC [montgomery_curve, mcurve_of_ecurve] THEN
    MAP_EVERY ABBREV_TAC
     [← q r"A:A = ring_div f (ring_mul f (ring_of_num f 2) (ring_add f a d))
                        (ring_sub f a d)",
      ← q r"B:A = ring_div f (ring_div f (ring_of_num f 4) (ring_sub f a d))
                        (ring_pow f c 2)"] THEN
    SUBGOAL_THEN (← q r"(A:A) IN ring_carrier f /\ B IN ring_carrier f")
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN RING_CARRIER_TAC, ALL_TAC] THEN
    STRIP_TAC THEN
    REWRITE_TAC [edwards_add, PAIR_EQ] THEN
    DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    MP_TAC (← ISPECL
     [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"x1:A", ← q r"y1:A", ← q r"x2:A",
      ← q r"y2:A"]
     EDWARDS_NONSINGULAR_DENOMINATORS) THEN
    ASM_REWRITE_TAC [edwards_curve, PAIR_EQ] THEN STRIP_TAC THEN
    REWRITE_TAC [montgomery_neg, option_INJ, PAIR_EQ] THEN
    ASM_CASES_TAC (← q r"u1:A = u2") THEN ASM_REWRITE_TAC [] THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC t546 THEN
      ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, id547] THEN
      MATCH_MP_TAC (← GEN_ALL (← REWRITE_RULE [IMP_IMP] id550)) THEN
      MAP_EVERY EXISTS_TAC [← q r"f:A ring", ← q r"B:A"] THEN
      ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN
      REPEAT CONJ_TAC THEN TRY RING_CARRIER_TAC THEN EXPAND_TAC "B" THEN
      REWRITE_TAC [ring_div] THEN
      ASM (HolLibrary.RingTheory.simpTac ss 8)
       [FIELD_MUL_EQ_0, FIELD_INV_EQ_0, FIELD_POW_EQ_0, RING_CLAUSES] THEN
      ASM_SIMP_TAC [RING_SUB_EQ_0, RING_OF_NUM_EQ_0] THEN
      NOT_RING_CHAR_DIVIDES_TAC,
      ALL_TAC] THEN
    ASM_REWRITE_TAC [montgomery_add] THEN LET_TAC THEN
    SUBGOAL_THEN (← q r"(l:A) IN ring_carrier f") ASSUME_TAC THENL
     [RING_CARRIER_TAC, ALL_TAC] THEN
    CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC [PAIR_EQ, option_INJ] THEN
    ASM_SIMP_TAC [RING_POW_2] THEN
    SUBGOAL_THEN (← q r"~(ring_sub f u2 u1:A = ring_0 f)") ASSUME_TAC THENL
     [ASM_SIMP_TAC [RING_SUB_EQ_0], ALL_TAC] THEN
    EXPAND_TAC "l" THEN RING_PULL_DIV_TAC THEN
    SUBGOAL_THEN (← q r"~(ring_sub f a d:A = ring_0 f)") ASSUME_TAC THENL
     [ASM_SIMP_TAC [RING_SUB_EQ_0], ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["A", "B"] THEN RING_PULL_DIV_TAC THEN
    MAP_EVERY EXPAND_TAC ["v1", "v2", "v3"] THEN RING_PULL_DIV_TAC THEN
    SUBGOAL_THEN
     (← q r"~(ring_sub f (ring_1 f) y1:A = ring_0 f) /\
      ~(ring_sub f (ring_1 f) y2:A = ring_0 f) /\
      ~(ring_sub f (ring_1 f) y3:A = ring_0 f)")
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC [RING_SUB_EQ_0, RING_1], ALL_TAC] THEN
    EXPAND_TAC "u1" THEN RING_PULL_DIV_TAC THEN
    EXPAND_TAC "u2" THEN RING_PULL_DIV_TAC THEN
    EXPAND_TAC "u3" THEN RING_PULL_DIV_TAC THEN
    EXPAND_TAC "x3" THEN RING_PULL_DIV_TAC THEN
    EXPAND_TAC "y3" THEN RING_PULL_DIV_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [← q r"ring_add f (ring_mul f a (ring_pow f x1 2)) (ring_pow f y1 2):A =
        ring_add f (ring_1 f)
        (ring_mul f d (ring_mul f (ring_pow f x1 2) (ring_pow f y1 2)))",
      ← q r"ring_add f (ring_mul f a (ring_pow f x2 2)) (ring_pow f y2 2):A =
        ring_add f (ring_1 f)
        (ring_mul f d (ring_mul f (ring_pow f x2 2) (ring_pow f y2 2)))"] THEN
    REPEAT (FIRST_X_ASSUM (fun th => tactic_of do let _ ← SYM th; pure ALL_TAC)) THEN
    REPEAT (FIRST_X_ASSUM (fun th => tactic_of do
      let _ ← CONV_RULE (RAND_CONV SYM_CONV) th; pure ALL_TAC)) THEN
    RING_TAC))

  -- @@RETURN BEGIN
  return { MONTGOMERY_OF_EDWARDS_NEG, GROUP_ISOMORPHISMS_EDWARDS_MONTGOMERY_GROUP }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Consequences: addition commutes with the map, and the groups are          -/
/- isomorphic in both directions.  (edmont.ml 596-655)                       -/
/- ------------------------------------------------------------------------- -/

structure EdmontIsoCor where
  -- @@FIELDS
  MONTGOMERY_OF_EDWARDS_ADD : thm
  GROUP_ISOMORPHISMS_MONTGOMERY_EDWARDS_GROUP : thm
  ISOMORPHIC_EDWARDS_MONTGOMERY_GROUP : thm
  ISOMORPHIC_MONTGOMERY_EDWARDS_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupEdmontIsoCor [HolBase] (D : EdmontDeps) (BEdmontDefs : EdmontDefs) (BEdmontIso : EdmontIso) :
    ExceptT String IO EdmontIsoCor := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, RING_CARRIER_TAC, .. } := D
  let { CONJ_ASSOC, EDWARDS_GROUP, GROUP_HOMOMORPHISM, GROUP_ISOMORPHISMS,
        GROUP_ISOMORPHISMS_IMP_ISOMORPHISM, GROUP_ISOMORPHISMS_SYM, IMP_CONJ_ALT, IN,
        ISOMORPHIC_GROUP_SYM, MONTGOMERY_GROUP, isomorphic_group, .. } := D.core1
  let { MCURVE_OF_ECURVE_NONSINGULAR, mcurve_of_ecurve, .. } := BEdmontDefs
  let { GROUP_ISOMORPHISMS_EDWARDS_MONTGOMERY_GROUP, .. } := BEdmontIso
  -- @@SCOPE END

  let MONTGOMERY_OF_EDWARDS_ADD ← prove
   r"!f (a:A) d c p q.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\ c IN ring_carrier f /\
        ~(a = d) /\ ~(a = ring_0 f) /\ ~(d = ring_0 f) /\ ~(c = ring_0 f) /\
        edwards_nonsingular(f,a,d) /\
        edwards_curve(f,a,d) p /\
        edwards_curve(f,a,d) q
        ==> montgomery_of_edwards f c (edwards_add(f,a,d) p q) =
            montgomery_add (mcurve_of_ecurve(f,a,d) c)
                           (montgomery_of_edwards f c p)
                           (montgomery_of_edwards f c q)"
   (← do
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"c:A"]
      GROUP_ISOMORPHISMS_EDWARDS_MONTGOMERY_GROUP) THEN
    ASM_REWRITE_TAC [GROUP_ISOMORPHISMS, GROUP_HOMOMORPHISM] THEN
    ASM_SIMP_TAC [EDWARDS_GROUP, IN] THEN DISCH_THEN (K ALL_TAC : thm → tactic) THEN
    MP_TAC (← ISPECL [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"c:A"]
      MCURVE_OF_ECURVE_NONSINGULAR) THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [mcurve_of_ecurve] THEN
    DISCH_THEN (MP_TAC o MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ_ALT]
     (← REWRITE_RULE [CONJ_ASSOC] MONTGOMERY_GROUP))) THEN
    ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN
    ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THEN RING_CARRIER_TAC))

  let GROUP_ISOMORPHISMS_MONTGOMERY_EDWARDS_GROUP ← prove
   r"!f (a:A) d c.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\ c IN ring_carrier f /\
        ~(a = d) /\ ~(a = ring_0 f) /\ ~(d = ring_0 f) /\ ~(c = ring_0 f) /\
        edwards_nonsingular(f,a,d)
        ==> group_isomorphisms (montgomery_group(mcurve_of_ecurve(f,a,d) c),
                                edwards_group(f,a,d))
                               (edwards_of_montgomery f c,
                                montgomery_of_edwards f c)"
   (← do
    pure (ONCE_REWRITE_TAC [GROUP_ISOMORPHISMS_SYM] THEN
    ACCEPT_TAC GROUP_ISOMORPHISMS_EDWARDS_MONTGOMERY_GROUP))

  let ISOMORPHIC_EDWARDS_MONTGOMERY_GROUP ← prove
   r"!f (a:A) d c.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\ c IN ring_carrier f /\
        ~(a = d) /\ ~(a = ring_0 f) /\ ~(d = ring_0 f) /\ ~(c = ring_0 f) /\
        edwards_nonsingular(f,a,d)
        ==> edwards_group(f,a,d) isomorphic_group
            montgomery_group(mcurve_of_ecurve(f,a,d) c)"
   (← do
    pure (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o
      MATCH_MP GROUP_ISOMORPHISMS_EDWARDS_MONTGOMERY_GROUP) THEN
    MESON_TAC [GROUP_ISOMORPHISMS_IMP_ISOMORPHISM, isomorphic_group]))

  let ISOMORPHIC_MONTGOMERY_EDWARDS_GROUP ← prove
   r"!f (a:A) d c.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\ c IN ring_carrier f /\
        ~(a = d) /\ ~(a = ring_0 f) /\ ~(d = ring_0 f) /\ ~(c = ring_0 f) /\
        edwards_nonsingular(f,a,d)
        ==> montgomery_group(mcurve_of_ecurve(f,a,d) c) isomorphic_group
            edwards_group(f,a,d)"
   (← do
    pure (ONCE_REWRITE_TAC [ISOMORPHIC_GROUP_SYM] THEN
    MATCH_ACCEPT_TAC ISOMORPHIC_EDWARDS_MONTGOMERY_GROUP))

  -- @@RETURN BEGIN
  return { MONTGOMERY_OF_EDWARDS_ADD, GROUP_ISOMORPHISMS_MONTGOMERY_EDWARDS_GROUP,
           ISOMORPHIC_EDWARDS_MONTGOMERY_GROUP, ISOMORPHIC_MONTGOMERY_EDWARDS_GROUP }
  -- @@RETURN END

end HolEC.Edmont
