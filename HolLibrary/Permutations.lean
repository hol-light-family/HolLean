/- ========================================================================= -/
/- Permutations, both general and specifically on finite sets.               -/
/- ========================================================================= -/
/- File: HolLibrary/Permutations.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/permutations.ml`, by hand, in file
  order, in the style of HolLibrary/Card.lean and HolLibrary/RSTC.lean (see
  there and HolMath/Base.lean for the conventions).  permutations.ml has no
  `needs`: it runs on the core library.  Each section is a bundle (a
  `structure`) built by a `setup` function; SessionLibrary/Permutations.lean
  builds the bundles in order and exports every name under its HOL Light
  name.  `swapseq` is made with `new_inductive_definition`, as in RSTC.lean;
  PERMSET_CONV's recursion is a top-level `partial def`.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, SET_RULE, TAUT, REAL_RING) they are bound
  first, in OCaml's order.
-/

import HolMath

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

set_option maxRecDepth 8000

namespace HolLibrary.Permutations

-- @@COREFILL BEGIN
/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD1 ADD_CLAUSES ARITH ARITH_EQ CARD_CLAUSES CARD_DELETE CARD_EQ_0
   CARD_IMAGE_INJ CARD_SUBSET CARD_UNION CHOOSE_SUBSET_STRONG COND_ID
   COND_RAND COND_RATOR CONJ_ASSOC DIV_0 EMPTY_GSPEC EQ_SYM EVEN EVEN_ADD
   EVEN_MULT EVEN_SUB EXISTS_PAIR_THM EXISTS_UNIQUE EXISTS_UNIQUE_THM
   EXTENSION FACT FINITE_CROSS_EQ FINITE_DELETE FINITE_EMPTY FINITE_IMAGE
   FINITE_INDUCT_STRONG FINITE_INSERT FINITE_NUMSEG FINITE_NUMSEG_LT
   FINITE_RESTRICT FINITE_RULES FINITE_SING FINITE_SUBSET FORALL_IN_IMAGE
   FORALL_PAIR_THM FORALL_UNWIND_THM2 FUN_EQ_THM HAS_SIZE HAS_SIZE_IMAGE_INJ
   HAS_SIZE_PRODUCT IMAGE_CLAUSES IMP_CONJ IMP_CONJ_ALT IMP_IMP
   INJECTIVE_ON_LEFT_INVERSE IN_CROSS IN_DELETE IN_DIFF IN_ELIM_PAIR_THM
   IN_ELIM_THM IN_IMAGE IN_INSERT IN_NUMSEG IN_SING IN_UNIV ITERATE_BIJECTION
   I_DEF I_O_ID I_THM LAMBDA_PAIR_THM LEFT_AND_EXISTS_THM LEFT_IMP_EXISTS_THM
   LE_ANTISYM LE_REFL : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (LE_TRANS LT LT_REFL MOD_ADD_MOD MOD_CASES MOD_LT MOD_LT_EQ MOD_MOD_REFL
   MONOIDAL_ADD MONOIDAL_REAL_ADD MONO_EXISTS NOT_EVEN NOT_FORALL_THM
   NOT_IN_EMPTY NOT_LT NOT_SUC NUMSEG_LREC ODD PAIR_EQ REAL_POW_NEG
   REAL_POW_ONE REAL_SGN_EQ RIGHT_AND_EXISTS_THM RIGHT_FORALL_IMP_THM
   SELECT_UNIQUE SUBSET SUC_INJ SUC_SUB1 SUM_IMAGE SUM_SUM_PRODUCT
   SURJECTIVE_IFF_INJECTIVE SURJECTIVE_RIGHT_INVERSE SWAP_FORALL_THM nsum
   num_WF o_ASSOC o_DEF o_THM real_pow sum : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms3 where
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms4 where
  deriving Inhabited

-- @@COREFILL END

/-- What permutations.ml uses from Session besides theorems. -/
structure PermutationsDeps where
  -- definitions and parser state
  new_definition : String → ExceptT String IO thm
  parse_as_infix : String × (Int × String) → IO Unit  -- parse.ml's parse_as_infix
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  METIS_TAC : List thm → tactic                 -- meson.ml's METIS_TAC
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  REAL_ARITH_TAC : tactic
  INDUCT_TAC : tactic
  -- conversions
  GEN_BETA_CONV : ioconv            -- ind_defs.ml's GEN_BETA_CONV
  HAS_SIZE_CONV : ioconv            -- sets.ml's HAS_SIZE_CONV
  NUM_REDUCE_CONV : ioconv          -- calc_num.ml's NUM_REDUCE_CONV
  -- (add fields here as needed, with a comment naming the HOL Light value)
  new_inductive_definition : String → ExceptT String IO (thm × thm × thm)
  -- conversions (HOL Light num_CONV, NUM_RED_CONV, REAL_RAT_REDUCE_CONV)
  num_CONV : ioconv
  NUM_RED_CONV : ioconv
  REAL_RAT_REDUCE_CONV : ioconv
  WF_INDUCT_TAC : term → tactic     -- wf.ml's WF_INDUCT_TAC
  REAL_RING : term → ExceptT String IO thm  -- real.ml's REAL_RING
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3
  core4 : CoreThms4

/- ------------------------------------------------------------------------- -/
/- permutes, inverse and transpositions (permutations.ml 1-130).            -/
/- ------------------------------------------------------------------------- -/

structure Permutes where
  -- @@FIELDS
  permutes : thm
  inverse : thm
  SURJECTIVE_INVERSE : thm
  SURJECTIVE_INVERSE_o : thm
  INJECTIVE_INVERSE : thm
  INJECTIVE_INVERSE_o : thm
  INVERSE_UNIQUE_o : thm
  INVERSE_I : thm
  INVERSE_UNIQUE_ALT : thm
  swap : thm
  SWAP_REFL : thm
  SWAP_SYM : thm
  SWAP_IDEMPOTENT : thm
  INVERSE_SWAP : thm
  SWAP_GALOIS : thm
  SWAP_LEFT : thm
  SWAP_RIGHT : thm
  SWAP_OTHER : thm
  SWAP_TRIPLE : thm
  SWAP_TRIPLE_ALT : thm
  INVOLUTION_SIZE_2_IS_SWAP : thm
  INVOLUTION_MOVES_2_IS_SWAP : thm
  deriving Inhabited

@[nospecialize]
def setupPermutes [HolBase] (D : PermutationsDeps) :
    ExceptT String IO Permutes := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, HAS_SIZE_CONV, MESON_TAC, SET_TAC, new_definition,
        parse_as_infix, .. } := D
  let { EXTENSION, FINITE_RESTRICT, FUN_EQ_THM, HAS_SIZE, IN_ELIM_THM, IN_INSERT,
        I_O_ID, I_THM, .. } := D.core1
  let { MONO_EXISTS, NOT_IN_EMPTY, SELECT_UNIQUE, SURJECTIVE_RIGHT_INVERSE, o_THM, .. } := D.core2
  -- @@SCOPE END

  parse_as_infix ("permutes", (12, "right"))

  let permutes ← new_definition
   r"p permutes s <=> (!x. ~(x IN s) ==> p(x) = x) /\ (!y. ?!x. p x = y)"

  /- --------------------------------------------------------------------- -/
  /- Inverse function (on whole universe).                                 -/
  /- --------------------------------------------------------------------- -/

  let inverse ← new_definition
   r"inverse(f) = \y. @x. f x = y"

  let SURJECTIVE_INVERSE ← prove
   r"!f. (!y. ?x. f x = y) <=> !y. f(inverse f y) = y"
   (REWRITE_TAC [SURJECTIVE_RIGHT_INVERSE, inverse] THEN MESON_TAC [])

  let SURJECTIVE_INVERSE_o ← prove
   r"!f. (!y. ?x. f x = y) <=> (f o inverse f = I)"
   (REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM, SURJECTIVE_INVERSE])

  let INJECTIVE_INVERSE ← prove
   r"!f. (!x x'. f x = f x' ==> x = x') <=> !x. inverse f (f x) = x"
   (MESON_TAC [inverse])

  let INJECTIVE_INVERSE_o ← prove
   r"!f. (!x x'. f x = f x' ==> x = x') <=> (inverse f o f = I)"
   (REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM, INJECTIVE_INVERSE])

  let INVERSE_UNIQUE_o ← prove
   r"!f g. f o g = I /\ g o f = I ==> inverse f = g"
   (REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM] THEN
    MESON_TAC [INJECTIVE_INVERSE, SURJECTIVE_INVERSE])

  let INVERSE_I ← prove
   r"inverse I = I"
   (MATCH_MP_TAC INVERSE_UNIQUE_o THEN REWRITE_TAC [I_O_ID])

  let INVERSE_UNIQUE_ALT ← prove
   r"!(f:A->A) g. (!x. f(g x) = x) /\ (!x. g(f x) = x)
                  ==> inverse f = g"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM, inverse] THEN
    X_GEN_TAC (← q r"y:A") THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    X_GEN_TAC (← q r"x:A") THEN EQ_TAC THEN ASM_MESON_TAC [])

  /- --------------------------------------------------------------------- -/
  /- Transpositions.                                                       -/
  /- --------------------------------------------------------------------- -/

  let swap ← new_definition
   r"swap(i,j) k = if k = i then j else if k = j then i else k"

  let SWAP_REFL ← prove
   r"!a. swap(a,a) = I"
   (REWRITE_TAC [FUN_EQ_THM, swap, I_THM] THEN MESON_TAC [])

  let SWAP_SYM ← prove
   r"!a b. swap(a,b) = swap(b,a)"
   (REWRITE_TAC [FUN_EQ_THM, swap, I_THM] THEN MESON_TAC [])

  let SWAP_IDEMPOTENT ← prove
   r"!a b. swap(a,b) o swap(a,b) = I"
   (REWRITE_TAC [FUN_EQ_THM, swap, o_THM, I_THM] THEN MESON_TAC [])

  let INVERSE_SWAP ← prove
   r"!a b. inverse(swap(a,b)) = swap(a,b)"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC INVERSE_UNIQUE_o THEN
    REWRITE_TAC [SWAP_SYM, SWAP_IDEMPOTENT])

  let SWAP_GALOIS ← prove
   r"!a b x y. x = swap(a,b) y <=> y = swap(a,b) x"
   (REWRITE_TAC [swap] THEN MESON_TAC [])

  let SWAP_LEFT ← prove
   r"!a b:A. swap(a,b) a = b"
   (REWRITE_TAC [swap])

  let SWAP_RIGHT ← prove
   r"!a b:A. swap(a,b) b = a"
   (REWRITE_TAC [swap] THEN MESON_TAC [])

  let SWAP_OTHER ← prove
   r"!a b x:A. ~(x = a) /\ ~(x = b) ==> swap(a,b) x = x"
   (REWRITE_TAC [swap] THEN MESON_TAC [])

  let SWAP_TRIPLE ← prove
   r"!a b c:A. ~(a = b) /\ ~(b = c) /\ ~(a = c)
       ==> swap(a,b) o swap(b,c) o swap(a,b) = swap(a,c)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"~(b:A = a) /\ ~(c:A = b) /\ ~(c:A = a)") STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
    REWRITE_TAC [FUN_EQ_THM, o_THM, swap] THEN
    X_GEN_TAC (← q r"x:A") THEN
    ASM_CASES_TAC (← q r"x:A = a") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"x:A = b") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"x:A = c") THEN ASM_REWRITE_TAC [])

  let SWAP_TRIPLE_ALT ← prove
   r"!a x y:A. ~(a = x) /\ ~(a = y) /\ ~(x = y)
       ==> swap(a,x) o swap(a,y) o swap(a,x) = swap(x,y)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"~(x:A = a) /\ ~(y:A = a) /\ ~(y:A = x)") STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
    REWRITE_TAC [FUN_EQ_THM, o_THM, swap] THEN
    X_GEN_TAC (← q r"z:A") THEN
    ASM_CASES_TAC (← q r"z:A = a") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"z:A = x") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"z:A = y") THEN ASM_REWRITE_TAC [])

  let INVOLUTION_SIZE_2_IS_SWAP ← prove
   r"!(s:A->bool) (p:A->A).
          (!x. x IN s ==> p x IN s) /\
          (!x. x IN s ==> p(p x) = x) /\
          {x | x IN s /\ ~(p x = x)} HAS_SIZE 2
          ==> ?a b. a IN s /\ b IN s /\ ~(a = b) /\
                    !x. x IN s ==> p x = swap(a,b) x"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o CONV_RULE HAS_SIZE_CONV) THEN
    REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT, NOT_IN_EMPTY, swap] THEN
    ASM SET_TAC [])

  let INVOLUTION_MOVES_2_IS_SWAP ← prove
   r"!(s:A->bool) (p:A->A).
       FINITE s /\
       (!x. x IN s ==> p x IN s) /\
       (!x. x IN s ==> p(p x) = x) /\
       CARD {x | x IN s /\ ~(p x = x)} = 2
       ==> ?(a:A) (b:A). a IN s /\ b IN s /\ ~(a = b) /\
                         !x. x IN s ==> p x = swap(a,b) x"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC INVOLUTION_SIZE_2_IS_SWAP THEN
    ASM_SIMP_TAC [HAS_SIZE, FINITE_RESTRICT] THEN ASM_MESON_TAC [])

  -- @@RETURN BEGIN
  return { permutes, inverse, SURJECTIVE_INVERSE, SURJECTIVE_INVERSE_o,
           INJECTIVE_INVERSE, INJECTIVE_INVERSE_o, INVERSE_UNIQUE_o, INVERSE_I,
           INVERSE_UNIQUE_ALT, swap, SWAP_REFL, SWAP_SYM, SWAP_IDEMPOTENT, INVERSE_SWAP,
           SWAP_GALOIS, SWAP_LEFT, SWAP_RIGHT, SWAP_OTHER, SWAP_TRIPLE, SWAP_TRIPLE_ALT,
           INVOLUTION_SIZE_2_IS_SWAP, INVOLUTION_MOVES_2_IS_SWAP }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Basic consequences of the definition (permutations.ml 132-280).          -/
/- ------------------------------------------------------------------------- -/

structure BasicCons where
  -- @@FIELDS
  PERMUTES_IN_IMAGE : thm
  PERMUTES_IMAGE : thm
  PERMUTES_INJECTIVE : thm
  PERMUTES_SURJECTIVE : thm
  PERMUTES_INVERSES_o : thm
  PERMUTES_INVERSES : thm
  PERMUTES_SUBSET : thm
  PERMUTES_EMPTY : thm
  PERMUTES_SING : thm
  PERMUTES_UNIV : thm
  PERMUTES_INVERSE_EQ : thm
  PERMUTES_SWAP : thm
  PERMUTES_SUPERSET : thm
  PERMUTES_BIJECTIONS : thm
  PERMUTES_INVERSE_FUNCTION : thm
  PERMUTES_ALT : thm
  PERMUTES_RESTRICT_SET : thm
  PERMUTES_RESTRICT : thm
  PERMUTES_CARTESIAN_PRODUCT : thm
  PERMUTES_TRANSFER_BIJECTIONS : thm
  PERMUTES_TRANSFER : thm
  deriving Inhabited

@[nospecialize]
def setupBasicCons [HolBase] (D : PermutationsDeps) (BPermutes : Permutes) :
    ExceptT String IO BasicCons := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, SET_TAC, .. } := D
  let { COND_RAND, COND_RATOR, EXISTS_PAIR_THM, EXISTS_UNIQUE, EXISTS_UNIQUE_THM,
        EXTENSION, FORALL_IN_IMAGE, FORALL_PAIR_THM, FUN_EQ_THM, IN_CROSS, IN_DIFF,
        IN_IMAGE, IN_SING, IN_UNIV, I_THM, .. } := D.core1
  let { NOT_IN_EMPTY, PAIR_EQ, SUBSET, o_THM, .. } := D.core2
  let { INJECTIVE_INVERSE_o, SURJECTIVE_INVERSE_o, inverse, permutes, swap, .. } := BPermutes
  -- @@SCOPE END

  let PERMUTES_IN_IMAGE ← prove
   r"!p s x. p permutes s ==> (p(x) IN s <=> x IN s)"
   (REWRITE_TAC [permutes] THEN MESON_TAC [])

  let PERMUTES_IMAGE ← prove
   r"!p s. p permutes s ==> IMAGE p s = s"
   (REWRITE_TAC [permutes, EXTENSION, IN_IMAGE] THEN MESON_TAC [])

  let PERMUTES_INJECTIVE ← prove
   r"!p s. p permutes s ==> !x y. p(x) = p(y) <=> x = y"
   (REWRITE_TAC [permutes] THEN MESON_TAC [])

  let PERMUTES_SURJECTIVE ← prove
   r"!p s. p permutes s ==> !y. ?x. p(x) = y"
   (REWRITE_TAC [permutes] THEN MESON_TAC [])

  let PERMUTES_INVERSES_o ← prove
   r"!p s. p permutes s ==> p o inverse(p) = I /\ inverse(p) o p = I"
   (REWRITE_TAC [← GSYM INJECTIVE_INVERSE_o, ← GSYM SURJECTIVE_INVERSE_o] THEN
    REWRITE_TAC [permutes] THEN MESON_TAC [])

  let PERMUTES_INVERSES ← prove
   r"!p s. p permutes s
           ==> (!x. p(inverse p x) = x) /\ (!x. inverse p (p x) = x)"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
    REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM])

  let PERMUTES_SUBSET ← prove
   r"!p s t. p permutes s /\ s SUBSET t ==> p permutes t"
   (REWRITE_TAC [permutes, SUBSET] THEN MESON_TAC [])

  let PERMUTES_EMPTY ← prove
   r"!p. p permutes {} <=> p = I"
   (REWRITE_TAC [FUN_EQ_THM, I_THM, permutes, NOT_IN_EMPTY] THEN MESON_TAC [])

  let PERMUTES_SING ← prove
   r"!p a.  p permutes {a} <=> p = I"
   (REWRITE_TAC [FUN_EQ_THM, I_THM, permutes, IN_SING] THEN MESON_TAC [])

  let PERMUTES_UNIV ← prove
   r"!p. p permutes UNIV <=> !y:A. ?!x. p x = y"
   (REWRITE_TAC [permutes, IN_UNIV] THEN MESON_TAC [])

  let PERMUTES_INVERSE_EQ ← prove
   r"!p s. p permutes s ==> !x y. inverse p y = x <=> p x = y"
   (REWRITE_TAC [permutes, inverse] THEN MESON_TAC [])

  let PERMUTES_SWAP ← prove
   r"!a b s. a IN s /\ b IN s ==> swap(a,b) permutes s"
   (REWRITE_TAC [permutes, swap] THEN MESON_TAC [])

  let PERMUTES_SUPERSET ← prove
   r"!p s t. p permutes s /\ (!x. x IN (s DIFF t) ==> p(x) = x)
             ==> p permutes t"
   (REWRITE_TAC [permutes, IN_DIFF] THEN MESON_TAC [])

  let PERMUTES_BIJECTIONS ← prove
   r"!p q. (!x. x IN s ==> p x IN s) /\ (!x. ~(x IN s) ==> p x = x) /\
           (!x. x IN s ==> q x IN s) /\ (!x. ~(x IN s) ==> q x = x) /\
           (!x. p(q x) = x) /\ (!x. q(p x) = x)
           ==> p permutes s"
   (REWRITE_TAC [permutes] THEN MESON_TAC [])

  let PERMUTES_INVERSE_FUNCTION ← prove
   r"!s p:A->A.
          p permutes s <=>
          ?q. (!x. ~(x IN s) ==> p x = x) /\
              (!x. x IN s ==> p x IN s) /\
              (!x. x IN s ==> p(q x) = x /\ q(p x) = x)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC (← q r"inverse p:A->A") THEN
      ASM_MESON_TAC [permutes, PERMUTES_INVERSES],
      STRIP_TAC THEN ASM_SIMP_TAC [permutes, SUBSET, FORALL_IN_IMAGE] THEN
    X_GEN_TAC (← q r"x:A") THEN REWRITE_TAC [EXISTS_UNIQUE] THEN
    ASM_CASES_TAC (← q r"(x:A) IN s") THENL
     [EXISTS_TAC (← q r"(q:A->A) x"), EXISTS_TAC (← q r"x:A")] THEN
    ASM_MESON_TAC []])

  let PERMUTES_ALT ← prove
   r"!(p:A->A) s.
          p permutes s <=>
          (!x. x IN s ==> p x IN s) /\
          (!x. ~(x IN s) ==> p x = x) /\
          (!y. y IN s ==> ?!x. x IN s /\ p x = y)"
   (← do
    let m1 ← MESON []
     (← q r"!s. (!y. ~(y IN s) ==> P y) /\ (!y. y IN s ==> P y) ==> !y. P y")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [permutes] THEN
    EQ_TAC THEN SIMP_TAC [] THENL [MESON_TAC [], DISCH_TAC] THEN
    MATCH_MP_TAC m1 THEN
    EXISTS_TAC (← q r"IMAGE (p:A->A) s") THEN REWRITE_TAC [FORALL_IN_IMAGE] THEN
    ASM SET_TAC []))

  let PERMUTES_RESTRICT_SET ← prove
   r"!Q p s:A->bool.
          p permutes s /\ (!x. x IN s ==> (Q(p x) <=> Q x))
          ==> (\i. if Q i then p i else i) permutes {x | x IN s /\ Q x}"
   (REWRITE_TAC [PERMUTES_ALT] THEN SET_TAC [])

  let PERMUTES_RESTRICT ← prove
   r"!Q p s:A->bool.
          p permutes s /\ (!x. x IN s ==> (Q(p x) <=> Q x))
          ==> (\i. if Q i then p i else i) permutes s"
   (REWRITE_TAC [PERMUTES_ALT] THEN SET_TAC [])

  let PERMUTES_CARTESIAN_PRODUCT ← prove
   r"!(p:A->A) (q:B->B) s t.
          p permutes s /\ q permutes t
          ==> (\(i,j). if i IN s /\ j IN t then p i,q j else i,j)
              permutes (s CROSS t)"
   (REWRITE_TAC [permutes, EXISTS_UNIQUE_THM] THEN
    REWRITE_TAC [FORALL_PAIR_THM, EXISTS_PAIR_THM, PAIR_EQ, IN_CROSS] THEN
    REWRITE_TAC [COND_RAND] THEN REWRITE_TAC [COND_RATOR] THEN
    REWRITE_TAC [PAIR_EQ] THEN MESON_TAC [])

  let PERMUTES_TRANSFER_BIJECTIONS ← prove
   r"!(f:A->B) f' p s t.
          (!x. f'(f x) = x) /\ (!y. f(f' y) = y) /\
          (!x. x IN s ==> f x IN t) /\
          (!y. y IN t ==> f' y IN s)
          ==> ((f' o p o f) permutes s <=> p permutes t)"
   (REWRITE_TAC [permutes, o_THM] THEN MESON_TAC [])

  let PERMUTES_TRANSFER ← prove
   r"!(f:A->B) p q s.
          p permutes s /\
          (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
          (!x. x IN s ==> q(f x) = f(p x)) /\
          (!y. ~(y IN IMAGE f s) ==> q y = y)
          ==> q permutes (IMAGE f s)"
   (SIMP_TAC [PERMUTES_ALT] THEN SET_TAC [])

  -- @@RETURN BEGIN
  return { PERMUTES_IN_IMAGE, PERMUTES_IMAGE, PERMUTES_INJECTIVE, PERMUTES_SURJECTIVE,
           PERMUTES_INVERSES_o, PERMUTES_INVERSES, PERMUTES_SUBSET, PERMUTES_EMPTY,
           PERMUTES_SING, PERMUTES_UNIV, PERMUTES_INVERSE_EQ, PERMUTES_SWAP,
           PERMUTES_SUPERSET, PERMUTES_BIJECTIONS, PERMUTES_INVERSE_FUNCTION,
           PERMUTES_ALT, PERMUTES_RESTRICT_SET, PERMUTES_RESTRICT,
           PERMUTES_CARTESIAN_PRODUCT, PERMUTES_TRANSFER_BIJECTIONS, PERMUTES_TRANSFER }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Swap conjugation and group properties (permutations.ml 282-350).         -/
/- ------------------------------------------------------------------------- -/

structure Groups where
  -- @@FIELDS
  SWAP_CONJUGATE : thm
  PERMUTES_ID : thm
  PERMUTES_I : thm
  PERMUTES_COMPOSE : thm
  PERMUTES_INVERSE : thm
  PERMUTES_INVERSE_INVERSE : thm
  deriving Inhabited

@[nospecialize]
def setupGroups [HolBase] (D : PermutationsDeps) (BPermutes : Permutes) (BBasicCons : BasicCons) :
    ExceptT String IO Groups := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, METIS_TAC, .. } := D
  let { FUN_EQ_THM, I_THM, .. } := D.core1
  let { o_THM, .. } := D.core2
  let { SWAP_LEFT, SWAP_OTHER, SWAP_RIGHT, permutes, .. } := BPermutes
  let { PERMUTES_INVERSES_o, PERMUTES_INVERSE_EQ, .. } := BBasicCons
  -- @@SCOPE END

  /- Conjugating a swap by a permutation gives a swap of the images: -/
  /- sigma o swap(a,b) o sigma^{-1} = swap(sigma a, sigma b)         -/

  let SWAP_CONJUGATE ← prove
   r"!(p:A->A) s a b. p permutes s
       ==> p o swap(a,b) o inverse p = swap(p a, p b)"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
    SUBGOAL_THEN (← q r"!y:A. (p:A->A)(inverse p y) = y")
      ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"(p:A->A) o inverse p = I") THEN
      REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!y:A. inverse (p:A->A) (p y) = y")
      ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"inverse (p:A->A) o p = I") THEN
      REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM],
      ALL_TAC] THEN
    REWRITE_TAC [FUN_EQ_THM, o_THM] THEN
    X_GEN_TAC (← q r"x:A") THEN
    ASM_CASES_TAC (← q r"(x:A) = (p:A->A) a") THENL
     [ASM_REWRITE_TAC [SWAP_LEFT], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"(x:A) = (p:A->A) b") THENL
     [ASM_REWRITE_TAC [SWAP_RIGHT], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~(inverse (p:A->A) (x:A) = a) /\
                   ~(inverse p x = b)") STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      DISCH_THEN (MP_TAC o AP_TERM (← q r"(p:A->A)")) THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    ASM_SIMP_TAC [SWAP_OTHER] THEN
    ASM_REWRITE_TAC [])

  /- --------------------------------------------------------------------- -/
  /- Group properties.                                                     -/
  /- --------------------------------------------------------------------- -/

  let PERMUTES_ID ← prove
   r"!s:A->bool. (\x. x) permutes s"
   (REWRITE_TAC [permutes] THEN MESON_TAC [])

  let PERMUTES_I ← prove
   r"!s. I permutes s"
   (REWRITE_TAC [permutes, I_THM] THEN MESON_TAC [])

  let PERMUTES_COMPOSE ← prove
   r"!p q s. p permutes s /\ q permutes s ==> (q o p) permutes s"
   (REWRITE_TAC [permutes, o_THM] THEN METIS_TAC [])

  let PERMUTES_INVERSE ← prove
   r"!p s. p permutes s ==> inverse(p) permutes s"
   (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o MATCH_MP PERMUTES_INVERSE_EQ) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [permutes] THEN MESON_TAC [])

  let PERMUTES_INVERSE_INVERSE ← prove
   r"!p. p permutes s ==> inverse(inverse p) = p"
   (SIMP_TAC [FUN_EQ_THM] THEN MESON_TAC [PERMUTES_INVERSE_EQ, PERMUTES_INVERSE])

  -- @@RETURN BEGIN
  return { SWAP_CONJUGATE, PERMUTES_ID, PERMUTES_I, PERMUTES_COMPOSE, PERMUTES_INVERSE,
           PERMUTES_INVERSE_INVERSE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- The number of permutations on a finite set (permutations.ml 352-430).    -/
/- ------------------------------------------------------------------------- -/

structure NumPerms where
  -- @@FIELDS
  PERMUTES_INSERT_LEMMA : thm
  PERMUTES_INSERT : thm
  HAS_SIZE_PERMUTATIONS : thm
  FINITE_PERMUTATIONS : thm
  CARD_PERMUTATIONS : thm
  deriving Inhabited

@[nospecialize]
def setupNumPerms [HolBase] (D : PermutationsDeps) (BPermutes : Permutes) (BBasicCons : BasicCons) (BGroups : Groups) :
    ExceptT String IO NumPerms := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, GEN_BETA_CONV, MESON_TAC, NUM_REDUCE_CONV, SET_RULE, .. } := D
  let { CARD_CLAUSES, EXISTS_PAIR_THM, EXTENSION, FACT, FINITE_EMPTY,
        FINITE_INDUCT_STRONG, FINITE_INSERT, FORALL_PAIR_THM, HAS_SIZE,
        HAS_SIZE_IMAGE_INJ, HAS_SIZE_PRODUCT, IMP_CONJ, IN_DIFF, IN_ELIM_PAIR_THM,
        IN_ELIM_THM, IN_IMAGE, IN_INSERT, I_O_ID, LEFT_IMP_EXISTS_THM, .. } := D.core1
  let { NOT_IN_EMPTY, PAIR_EQ, RIGHT_FORALL_IMP_THM, SUBSET, o_ASSOC, o_THM, .. } := D.core2
  let { SWAP_IDEMPOTENT, permutes, swap, .. } := BPermutes
  let { PERMUTES_EMPTY, PERMUTES_IN_IMAGE, PERMUTES_SUBSET, PERMUTES_SUPERSET,
        PERMUTES_SWAP, .. } := BBasicCons
  let { PERMUTES_COMPOSE, .. } := BGroups
  -- @@SCOPE END

  let PERMUTES_INSERT_LEMMA ← prove
   r"!p a:A s. p permutes (a INSERT s) ==> (swap(a,p(a)) o p) permutes s"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC PERMUTES_SUPERSET THEN
    EXISTS_TAC (← q r"(a:A) INSERT s") THEN CONJ_TAC THENL
     [ASM_MESON_TAC [PERMUTES_SWAP, PERMUTES_IN_IMAGE,
                    IN_INSERT, PERMUTES_COMPOSE],
      REWRITE_TAC [o_THM, swap, IN_INSERT, IN_DIFF] THEN ASM_MESON_TAC []])

  let PERMUTES_INSERT ← prove
   r"{p:A->A | p permutes (a INSERT s)} =
          IMAGE (\(b,p). swap(a,b) o p)
                {(b,p) | b IN a INSERT s /\ p IN {p | p permutes s}}"
   (REWRITE_TAC [EXTENSION, IN_ELIM_PAIR_THM, IN_IMAGE, EXISTS_PAIR_THM] THEN
    X_GEN_TAC (← q r"p:A->A") THEN REWRITE_TAC [IN_ELIM_THM] THEN
    CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN EQ_TAC THENL
     [DISCH_TAC THEN MAP_EVERY EXISTS_TAC
        [← q r"(p:A->A) a", ← q r"swap(a,p a) o (p:A->A)"] THEN
      ASM_SIMP_TAC [SWAP_IDEMPOTENT, o_ASSOC, I_O_ID, PERMUTES_INSERT_LEMMA] THEN
      ASM_MESON_TAC [PERMUTES_IN_IMAGE, IN_INSERT],
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"b:A", ← q r"q:A->A"] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC PERMUTES_COMPOSE THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC [PERMUTES_SUBSET, SUBSET, IN_INSERT],
        MATCH_MP_TAC PERMUTES_SWAP THEN
        ASM_MESON_TAC [PERMUTES_IN_IMAGE, IN_INSERT]]])

  let HAS_SIZE_PERMUTATIONS ← prove
   r"!s:A->bool n. s HAS_SIZE n ==> {p | p permutes s} HAS_SIZE (FACT n)"
   (← do
    let r1 ← SET_RULE (← q r"{x | x = a} = {a}")
    pure (REWRITE_TAC [HAS_SIZE, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [PERMUTES_EMPTY, CARD_CLAUSES, r1] THEN
    SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY] THEN
    REWRITE_TAC [NOT_IN_EMPTY] THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN CONV_TAC NUM_REDUCE_CONV,
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:A", ← q r"s:A->bool"] THEN REWRITE_TAC [← GSYM HAS_SIZE] THEN
    STRIP_TAC THEN X_GEN_TAC (← q r"k:num") THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC [FACT, PERMUTES_INSERT] THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    ASM_SIMP_TAC [HAS_SIZE_PRODUCT, HAS_SIZE, FINITE_INSERT, CARD_CLAUSES] THEN
    REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_PAIR_THM, IN_ELIM_THM, PAIR_EQ] THEN
    CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    MAP_EVERY X_GEN_TAC [← q r"b:A", ← q r"q:A->A", ← q r"c:A", ← q r"r:A->A"] THEN
    STRIP_TAC THEN SUBGOAL_THEN (← q r"c:A = b") SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o C AP_THM (← q r"a:A")) THEN REWRITE_TAC [o_THM, swap] THEN
      SUBGOAL_THEN (← q r"(q:A->A) a = a /\ (r:A->A) a = a") (fun t => SIMP_TAC [t]) THEN
      ASM_MESON_TAC [permutes],
      FIRST_X_ASSUM (MP_TAC o AP_TERM (← q r"(\q:A->A. swap(a:A,b) o q)")) THEN
      ASM_SIMP_TAC [SWAP_IDEMPOTENT, o_ASSOC, I_O_ID]]))

  let FINITE_PERMUTATIONS ← prove
   r"!s. FINITE s ==> FINITE {p | p permutes s}"
   (MESON_TAC [HAS_SIZE_PERMUTATIONS, HAS_SIZE])

  let CARD_PERMUTATIONS ← prove
   r"!s. FINITE s ==> CARD {p | p permutes s} = FACT(CARD s)"
   (MESON_TAC [HAS_SIZE, HAS_SIZE_PERMUTATIONS])

  -- @@RETURN BEGIN
  return { PERMUTES_INSERT_LEMMA, PERMUTES_INSERT, HAS_SIZE_PERMUTATIONS,
           FINITE_PERMUTATIONS, CARD_PERMUTATIONS }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Alternative characterizations of permutation of finite set (432-470).    -/
/- ------------------------------------------------------------------------- -/

structure AltChar where
  -- @@FIELDS
  PERMUTES_FINITE_INJECTIVE : thm
  PERMUTES_FINITE_SURJECTIVE : thm
  deriving Inhabited

@[nospecialize]
def setupAltChar [HolBase] (D : PermutationsDeps) (BPermutes : Permutes) :
    ExceptT String IO AltChar := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, .. } := D
  let { CONJ_ASSOC, FORALL_IN_IMAGE, IMP_CONJ, IMP_IMP, .. } := D.core1
  let { SUBSET, SURJECTIVE_IFF_INJECTIVE, .. } := D.core2
  let { permutes, .. } := BPermutes
  -- @@SCOPE END

  let PERMUTES_FINITE_INJECTIVE ← prove
   r"!s:A->bool p.
          FINITE s
          ==> (p permutes s <=>
               (!x. ~(x IN s) ==> p x = x) /\
               (!x. x IN s ==> p x IN s) /\
               (!x y. x IN s /\ y IN s /\ p x = p y ==> x = y))"
   (← do
    let t1 ← TAUT (← q r"(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)")
    pure (REWRITE_TAC [permutes] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC t1 THEN
    DISCH_TAC THEN EQ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"p:A->A") o MATCH_MP
     (← REWRITE_RULE [IMP_CONJ] SURJECTIVE_IFF_INJECTIVE)) THEN
    ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IMP_IMP, ← GSYM CONJ_ASSOC] THEN
    STRIP_TAC THEN X_GEN_TAC (← q r"y:A") THEN
    ASM_CASES_TAC (← q r"(y:A) IN s") THEN ASM_MESON_TAC []))

  let PERMUTES_FINITE_SURJECTIVE ← prove
   r"!s:A->bool p.
          FINITE s
          ==> (p permutes s <=>
               (!x. ~(x IN s) ==> p x = x) /\ (!x. x IN s ==> p x IN s) /\
               (!y. y IN s ==> ?x. x IN s /\ p x = y))"
   (← do
    let t1 ← TAUT (← q r"(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)")
    pure (REWRITE_TAC [permutes] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC t1 THEN
    DISCH_TAC THEN EQ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"p:A->A") o MATCH_MP
     (← REWRITE_RULE [IMP_CONJ] SURJECTIVE_IFF_INJECTIVE)) THEN
    ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IMP_IMP, ← GSYM CONJ_ASSOC] THEN
    STRIP_TAC THEN X_GEN_TAC (← q r"y:A") THEN
    ASM_CASES_TAC (← q r"(y:A) IN s") THEN ASM_MESON_TAC []))

  -- @@RETURN BEGIN
  return { PERMUTES_FINITE_INJECTIVE, PERMUTES_FINITE_SURJECTIVE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Restriction of permutations to subsets (permutations.ml 472-610).        -/
/- ------------------------------------------------------------------------- -/

structure Restrict where
  -- @@FIELDS
  RESTRICT_PERMUTES_SUBSET : thm
  RESTRICT_I : thm
  RESTRICT_COMPOSE : thm
  RESTRICT_INVERSE : thm
  RESTRICT_SWAP : thm
  deriving Inhabited

@[nospecialize]
def setupRestrict [HolBase] (D : PermutationsDeps) (BPermutes : Permutes) (BBasicCons : BasicCons) (BAltChar : AltChar) :
    ExceptT String IO Restrict := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, SET_TAC, .. } := D
  let { EQ_SYM, FUN_EQ_THM, IN_IMAGE, I_THM, .. } := D.core1
  let { o_THM, .. } := D.core2
  let { swap, .. } := BPermutes
  let { PERMUTES_INJECTIVE, PERMUTES_INVERSES_o, PERMUTES_INVERSE_EQ, .. } := BBasicCons
  let { PERMUTES_FINITE_INJECTIVE, .. } := BAltChar
  -- @@SCOPE END

  let RESTRICT_PERMUTES_SUBSET ← prove
   r"!s t (f:A->A).
      FINITE t /\ t SUBSET s /\ f permutes s /\ IMAGE f t = t
      ==> (\x. if x IN t then f x else x) permutes t"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPEC (← q r"t:A->bool") PERMUTES_FINITE_INJECTIVE) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN
      REWRITE_TAC [] THEN COND_CASES_TAC THEN ASM_MESON_TAC [],
      X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN
      REWRITE_TAC [] THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"(f:A->A) x IN t") MP_TAC THENL
       [ASM SET_TAC [], SIMP_TAC []],
      MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN STRIP_TAC THEN
      REWRITE_TAC [] THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [PERMUTES_INJECTIVE]])

  /- Restriction of identity is identity -/
  let RESTRICT_I ← prove
   r"!t:A->bool. (\x. if x IN t then I x else x) = I"
   (GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM, I_THM] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [])

  /- Restriction of composition = composition of restrictions,
     when both permutations preserve the subset -/
  let RESTRICT_COMPOSE ← prove
   r"!s t (f:A->A) g.
      t SUBSET s /\ f permutes s /\ g permutes s /\
      IMAGE f t = t /\ IMAGE g t = t
      ==> (\x. if x IN t then (f o g) x else x) =
          (\x. if x IN t then f x else x) o (\x. if x IN t then g x else x)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM, o_THM] THEN
    X_GEN_TAC (← q r"x:A") THEN
    ASM_CASES_TAC (← q r"(x:A) IN t") THENL
     [ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"(g:A->A) x IN t") ASSUME_TAC THENL
       [ASM SET_TAC [], ASM_SIMP_TAC []],
      ASM_REWRITE_TAC []])

  /- Restriction of inverse = inverse of restriction -/
  let RESTRICT_INVERSE ← prove
   r"!s t (f:A->A).
      FINITE t /\ t SUBSET s /\ f permutes s /\ IMAGE f t = t
      ==> (\x. if x IN t then inverse f x else x) =
          inverse (\x. if x IN t then f x else x)"
   (REPEAT STRIP_TAC THEN
    ABBREV_TAC (← q r"g = \x:A. if x IN t then f x else x") THEN
    SUBGOAL_THEN (← q r"(g:A->A) permutes t") ASSUME_TAC THENL
     [EXPAND_TAC "g" THEN MATCH_MP_TAC RESTRICT_PERMUTES_SUBSET THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    -- Key fact: inverse f maps t to t
    SUBGOAL_THEN (← q r"!z:A. z IN t ==> inverse f z IN t") ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"(z:A) IN IMAGE (f:A->A) t") MP_TAC THENL
       [ASM SET_TAC [],
        REWRITE_TAC [IN_IMAGE] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"w:A") STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN (← q r"inverse (f:A->A) z = w") SUBST1_TAC THENL
         [MP_TAC (← ASSUME (← q r"(f:A->A) permutes s")) THEN
          DISCH_THEN (MP_TAC o MATCH_MP PERMUTES_INVERSE_EQ) THEN
          ASM_MESON_TAC [],
          ASM_REWRITE_TAC []]],
      ALL_TAC] THEN
    -- Key fact: f(inverse f y) = y
    SUBGOAL_THEN (← q r"!y:A. (f:A->A) (inverse f y) = y") ASSUME_TAC THENL
     [GEN_TAC THEN
      MP_TAC (← MATCH_MP PERMUTES_INVERSES_o (← ASSUME (← q r"(f:A->A) permutes s"))) THEN
      DISCH_THEN (MP_TAC o CONJUNCT1) THEN
      DISCH_THEN (MP_TAC o REWRITE_RULE [FUN_EQ_THM, o_THM, I_THM]) THEN
      DISCH_THEN (fun th => REWRITE_TAC [th]),
      ALL_TAC] THEN
    -- Main: show inverse g y = (if y IN t then inverse f y else y)
    REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"y:A") THEN
    MATCH_MP_TAC EQ_SYM THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP PERMUTES_INVERSE_EQ) THEN
    DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
    -- Goal: g (if y IN t then inverse f y else y) = y
    ASM_CASES_TAC (← q r"(y:A) IN t") THENL
     [ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"inverse (f:A->A) y IN t") ASSUME_TAC THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(g:A->A) (inverse f y) = f (inverse f y)")
        (fun th => ASM_REWRITE_TAC [th]) THEN
      EXPAND_TAC "g" THEN BETA_TAC THEN
      COND_CASES_TAC THENL [REFL_TAC, ASM_MESON_TAC []],
      ASM_REWRITE_TAC [] THEN
      EXPAND_TAC "g" THEN BETA_TAC THEN
      COND_CASES_TAC THENL [ASM_MESON_TAC [], REFL_TAC]])

  /- Helper: restriction of swap(a,b) to a set containing a and b is swap(a,b) -/
  let RESTRICT_SWAP ← prove
   r"!(s:A->bool) a b.
      a IN s /\ b IN s
      ==> (\x. if x IN s then swap(a,b) x else x) = swap(a,b)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"x:A") THEN
    ASM_CASES_TAC (← q r"(x:A) IN s") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [swap] THEN
    REPEAT COND_CASES_TAC THEN ASM_MESON_TAC [])

  -- @@RETURN BEGIN
  return { RESTRICT_PERMUTES_SUBSET, RESTRICT_I, RESTRICT_COMPOSE, RESTRICT_INVERSE,
           RESTRICT_SWAP }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Permutations of index set for iterated operations; combinations of       -/
/- transpositions (permutations.ml 612-660).                                -/
/- ------------------------------------------------------------------------- -/

structure IterSwap where
  -- @@FIELDS
  ITERATE_PERMUTE : thm
  NSUM_PERMUTE : thm
  NSUM_PERMUTE_NUMSEG : thm
  SUM_PERMUTE : thm
  SUM_PERMUTE_NUMSEG : thm
  SWAP_COMMON : thm
  SWAP_COMMON' : thm
  SWAP_INDEPENDENT : thm
  deriving Inhabited

@[nospecialize]
def setupIterSwap [HolBase] (D : PermutationsDeps) (BPermutes : Permutes) :
    ExceptT String IO IterSwap := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, .. } := D
  let { FINITE_NUMSEG, FUN_EQ_THM, ITERATE_BIJECTION, I_THM, .. } := D.core1
  let { MONOIDAL_ADD, MONOIDAL_REAL_ADD, nsum, o_THM, sum, .. } := D.core2
  let { SWAP_SYM, permutes, swap, .. } := BPermutes
  -- @@SCOPE END

  let ITERATE_PERMUTE ← prove
   r"!op. monoidal op
          ==> !f p s. p permutes s ==> iterate op s f = iterate op s (f o p)"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP ITERATE_BIJECTION) THEN
    ASM_MESON_TAC [permutes])

  let NSUM_PERMUTE ← prove
   r"!f p s. p permutes s ==> nsum s f = nsum s (f o p)"
   (REWRITE_TAC [nsum] THEN MATCH_MP_TAC ITERATE_PERMUTE THEN
    REWRITE_TAC [MONOIDAL_ADD])

  let NSUM_PERMUTE_NUMSEG ← prove
   r"!f p m n. p permutes m..n ==> nsum(m..n) f = nsum(m..n) (f o p)"
   (MESON_TAC [NSUM_PERMUTE, FINITE_NUMSEG])

  let SUM_PERMUTE ← prove
   r"!f p s. p permutes s ==> sum s f = sum s (f o p)"
   (REWRITE_TAC [sum] THEN MATCH_MP_TAC ITERATE_PERMUTE THEN
    REWRITE_TAC [MONOIDAL_REAL_ADD])

  let SUM_PERMUTE_NUMSEG ← prove
   r"!f p m n. p permutes m..n ==> sum(m..n) f = sum(m..n) (f o p)"
   (MESON_TAC [SUM_PERMUTE, FINITE_NUMSEG])

  /- --------------------------------------------------------------------- -/
  /- Various combinations of transpositions with 2, 1 and 0 common         -/
  /- elements.                                                             -/
  /- --------------------------------------------------------------------- -/

  let SWAP_COMMON ← prove
   r"!a b c:A. ~(a = c) /\ ~(b = c)
               ==> swap(a,b) o swap(a,c) = swap(b,c) o swap(a,b)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM, swap, o_THM, I_THM] THEN
    DISCH_TAC THEN X_GEN_TAC (← q r"x:A") THEN
    MAP_EVERY ASM_CASES_TAC [← q r"x:A = a", ← q r"x:A = b", ← q r"x:A = c"] THEN
    REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [])

  let SWAP_COMMON' ← prove
   r"!a b c:A. ~(a = b) /\ ~(a = c)
               ==> swap(a,c) o swap(b,c) = swap(b,c) o swap(a,b)"
   (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SWAP_SYM] THEN
    ASM_SIMP_TAC [← GSYM SWAP_COMMON] THEN REWRITE_TAC [SWAP_SYM])

  let SWAP_INDEPENDENT ← prove
   r"!a b c d:A. ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d)
                 ==> swap(a,b) o swap(c,d) = swap(c,d) o swap(a,b)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM, swap, o_THM, I_THM] THEN
    DISCH_TAC THEN X_GEN_TAC (← q r"x:A") THEN
    MAP_EVERY ASM_CASES_TAC [← q r"x:A = a", ← q r"x:A = b", ← q r"x:A = c"] THEN
    REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [])

  -- @@RETURN BEGIN
  return { ITERATE_PERMUTE, NSUM_PERMUTE, NSUM_PERMUTE_NUMSEG, SUM_PERMUTE,
           SUM_PERMUTE_NUMSEG, SWAP_COMMON, SWAP_COMMON', SWAP_INDEPENDENT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Three-cycles: pure permutation combinatorics (permutations.ml 662-682).  -/
/- ------------------------------------------------------------------------- -/

structure ThreeCycle where
  -- @@FIELDS
  three_cycle : thm
  PERMUTES_THREE_CYCLE : thm
  THREE_CYCLE_COMPOSE_REVERSE : thm
  THREE_CYCLE_INVERSE : thm
  THREE_CYCLE_AS_COMMUTATOR : thm
  THREE_CYCLE_COMMUTATOR : thm
  THREE_CYCLE_NOT_I : thm
  deriving Inhabited

@[nospecialize]
def setupThreeCycle [HolBase] (D : PermutationsDeps) (BPermutes : Permutes) :
    ExceptT String IO ThreeCycle := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, new_definition, .. } := D
  let { FUN_EQ_THM, I_THM, .. } := D.core1
  let { o_THM, .. } := D.core2
  let { INVERSE_UNIQUE_ALT, permutes, .. } := BPermutes
  -- @@SCOPE END

  /- A 3-cycle (a b c) sends a -> b -> c -> a, fixes everything else -/
  let three_cycle ← new_definition
   r"three_cycle (a:A) b c =
      \x:A. if x = a then b else if x = b then c else if x = c then a else x"

  let PERMUTES_THREE_CYCLE ← prove
   r"!s a b c:A. a IN s /\ b IN s /\ c IN s /\
                 ~(a = b) /\ ~(b = c) /\ ~(a = c)
                 ==> three_cycle a b c permutes s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [permutes, three_cycle] THEN
    ASM_MESON_TAC [])

  /- Composition of a three-cycle with its reverse gives identity -/
  let THREE_CYCLE_COMPOSE_REVERSE ← prove
   r"!a b c:A. ~(a = b) /\ ~(b = c) /\ ~(a = c)
      ==> three_cycle a b c o three_cycle a c b = I /\
          three_cycle a c b o three_cycle a b c = I"
   (REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM, three_cycle] THEN MESON_TAC [])

  let THREE_CYCLE_INVERSE ← prove
   r"!a b c:A. ~(a = b) /\ ~(b = c) /\ ~(a = c)
      ==> inverse (three_cycle a b c) = three_cycle a c b"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC INVERSE_UNIQUE_ALT THEN
    MP_TAC (← SPECL [← q r"a:A", ← q r"b:A", ← q r"c:A"] THREE_CYCLE_COMPOSE_REVERSE) THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM] THEN MESON_TAC [])

  /- Key commutator identity: (x_a x_b x_c) = sigma^{-1} tau^{-1} sigma tau  -/
  /- where sigma = (x_d x_a x_c) and tau = (x_c x_e x_b):                    -/
  /- every 3-cycle is a commutator of two 3-cycles (when n >= 5).            -/
  /- This is the core combinatorial fact for proving S_n is not solvable.    -/

  let THREE_CYCLE_AS_COMMUTATOR ← prove
   r"!a b c d e:A.
       ~(a = b) /\ ~(a = c) /\ ~(a = d) /\ ~(a = e) /\
       ~(b = c) /\ ~(b = d) /\ ~(b = e) /\
       ~(c = d) /\ ~(c = e) /\
       ~(d = e)
       ==> three_cycle a b c =
           (three_cycle d c a) o
           (three_cycle c b e) o
           (three_cycle d a c) o
           (three_cycle c e b)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [FUN_EQ_THM, o_THM, three_cycle] THEN
    X_GEN_TAC (← q r"x:A") THEN
    ASM_CASES_TAC (← q r"x:A = a") THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"x:A = b") THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"x:A = c") THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"x:A = d") THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"x:A = e") THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    ASM_REWRITE_TAC [])

  /- Same identity but stated using inverse -/
  let THREE_CYCLE_COMMUTATOR ← prove
   r"!a b c d e:A.
       ~(a = b) /\ ~(a = c) /\ ~(a = d) /\ ~(a = e) /\
       ~(b = c) /\ ~(b = d) /\ ~(b = e) /\
       ~(c = d) /\ ~(c = e) /\
       ~(d = e)
       ==> three_cycle a b c =
           (inverse(three_cycle d a c)) o
           (inverse(three_cycle c e b)) o
           (three_cycle d a c) o
           (three_cycle c e b)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"inverse(three_cycle d a (c:A)) = three_cycle d c a")
      SUBST1_TAC THENL
     [MATCH_MP_TAC THREE_CYCLE_INVERSE THEN ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"inverse(three_cycle c e (b:A)) = three_cycle c b e")
      SUBST1_TAC THENL
     [MATCH_MP_TAC THREE_CYCLE_INVERSE THEN ASM_MESON_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC THREE_CYCLE_AS_COMMUTATOR THEN ASM_REWRITE_TAC [])

  /- A 3-cycle is nontrivial (not the identity) -/
  let THREE_CYCLE_NOT_I ← prove
   r"!a b c:A. ~(a = b) /\ ~(b = c) /\ ~(a = c)
               ==> ~(three_cycle a b c = I)"
   (REWRITE_TAC [FUN_EQ_THM, three_cycle, I_THM] THEN MESON_TAC [])

  -- @@RETURN BEGIN
  return { three_cycle, PERMUTES_THREE_CYCLE, THREE_CYCLE_COMPOSE_REVERSE,
           THREE_CYCLE_INVERSE, THREE_CYCLE_AS_COMMUTATOR, THREE_CYCLE_COMMUTATOR,
           THREE_CYCLE_NOT_I }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Permutations as transposition sequences.  (permutations.ml 683-842)       -/
/- ------------------------------------------------------------------------- -/

structure Swapseq where
  -- @@FIELDS
  swapseq_RULES : thm
  swapseq_INDUCT : thm
  swapseq_CASES : thm
  permutation : thm
  SWAPSEQ_I : thm
  PERMUTATION_I : thm
  SWAPSEQ_SWAP : thm
  PERMUTATION_SWAP : thm
  SWAPSEQ_COMPOSE : thm
  PERMUTATION_COMPOSE : thm
  SWAPSEQ_ENDSWAP : thm
  SWAPSEQ_INVERSE_EXISTS : thm
  SWAPSEQ_INVERSE : thm
  PERMUTATION_INVERSE : thm
  SYMMETRY_LEMMA : thm
  SWAP_GENERAL : thm
  FIXING_SWAPSEQ_DECREASE : thm
  SWAPSEQ_IDENTITY_EVEN : thm
  deriving Inhabited

@[nospecialize]
def setupSwapseq [HolBase] (D : PermutationsDeps) (BPermutes : Permutes) (BIterSwap : IterSwap) :
    ExceptT String IO Swapseq := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, .. } := D
  let { ADD_CLAUSES, CONJ_ASSOC, EVEN, FUN_EQ_THM, IMP_CONJ, I_O_ID, I_THM,
        LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, .. } := D.core1
  let { NOT_SUC, RIGHT_FORALL_IMP_THM, SUC_INJ, SUC_SUB1, num_WF, o_ASSOC, o_THM, .. } := D.core2
  let { INVERSE_UNIQUE_o, SWAP_IDEMPOTENT, SWAP_REFL, SWAP_SYM, swap, .. } := BPermutes
  let { SWAP_COMMON, SWAP_COMMON', SWAP_INDEPENDENT, .. } := BIterSwap
  -- @@SCOPE END

  let (swapseq_RULES, swapseq_INDUCT, swapseq_CASES) ← D.new_inductive_definition
   r"(swapseq 0 I) /\
  (!a b p n. swapseq n p /\ ~(a = b) ==> swapseq (SUC n) (swap(a,b) o p))"

  let permutation ← D.new_definition
   r"permutation p <=> ?n. swapseq n p"

  /- --------------------------------------------------------------------- -/
  /- Some closure properties of the set of permutations, with lengths.     -/
  /- --------------------------------------------------------------------- -/

  let SWAPSEQ_I ← CONJUNCT1 swapseq_RULES

  let PERMUTATION_I ← prove
   r"permutation I"
   (REWRITE_TAC [permutation] THEN MESON_TAC [SWAPSEQ_I])

  let SWAPSEQ_SWAP ← prove
   r"!a b. swapseq (if a = b then 0 else 1) (swap(a,b))"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [← ExceptT.mk (D.num_CONV (← q "1"))] THEN
    ASM_MESON_TAC [swapseq_RULES, I_O_ID, SWAPSEQ_I, SWAP_REFL])

  let PERMUTATION_SWAP ← prove
   r"!a b. permutation(swap(a,b))"
   (REWRITE_TAC [permutation] THEN MESON_TAC [SWAPSEQ_SWAP])

  let SWAPSEQ_COMPOSE ← prove
   r"!n p m q. swapseq n p /\ swapseq m q ==> swapseq (n + m) (p o q)"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM, IMP_CONJ] THEN
    MATCH_MP_TAC swapseq_INDUCT THEN
    REWRITE_TAC [ADD_CLAUSES, I_O_ID, ← GSYM o_ASSOC] THEN
    MESON_TAC [swapseq_RULES])

  let PERMUTATION_COMPOSE ← prove
   r"!p q. permutation p /\ permutation q ==> permutation(p o q)"
   (REWRITE_TAC [permutation] THEN MESON_TAC [SWAPSEQ_COMPOSE])

  let SWAPSEQ_ENDSWAP ← prove
   r"!n p a b:A. swapseq n p /\ ~(a = b) ==> swapseq (SUC n) (p o swap(a,b))"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM, IMP_CONJ] THEN
    MATCH_MP_TAC swapseq_INDUCT THEN REWRITE_TAC [I_O_ID, ← GSYM o_ASSOC] THEN
    MESON_TAC [o_ASSOC, swapseq_RULES, I_O_ID])

  let SWAPSEQ_INVERSE_EXISTS ← prove
   r"!n p:A->A. swapseq n p ==> ?q. swapseq n q /\ p o q = I /\ q o p = I"
   (MATCH_MP_TAC swapseq_INDUCT THEN CONJ_TAC THENL
     [MESON_TAC [I_O_ID, swapseq_RULES], ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q "n:num", ← q "q:A->A", ← q "a:A", ← q "b:A"] SWAPSEQ_ENDSWAP) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    EXISTS_TAC (← q r"(q:A->A) o swap (a,b)") THEN
    ASM_REWRITE_TAC [← GSYM o_ASSOC] THEN
    GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o RAND_CONV) [o_ASSOC] THEN
    ASM_REWRITE_TAC [SWAP_IDEMPOTENT, I_O_ID])

  let SWAPSEQ_INVERSE ← prove
   r"!n p. swapseq n p ==> swapseq n (inverse p)"
   (MESON_TAC [SWAPSEQ_INVERSE_EXISTS, INVERSE_UNIQUE_o])

  let PERMUTATION_INVERSE ← prove
   r"!p. permutation p ==> permutation(inverse p)"
   (REWRITE_TAC [permutation] THEN MESON_TAC [SWAPSEQ_INVERSE])

  /- --------------------------------------------------------------------- -/
  /- The identity map only has even transposition sequences.               -/
  /- --------------------------------------------------------------------- -/

  let SYMMETRY_LEMMA ← prove
   r"(!a b c d. P a b c d ==> P a b d c) /\
   (!a b c d. ~(a = b) /\ ~(c = d) /\
              (a = c /\ b = d \/ a = c /\ ~(b = d) \/ ~(a = c) /\ b = d \/
               ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d))
              ==> P a b c d)
   ==> (!a b c d:A. ~(a = b) /\ ~(c = d) ==> P a b c d)"
   (REPEAT STRIP_TAC THEN MAP_EVERY ASM_CASES_TAC
     [← q "a:A = c", ← q "a:A = d", ← q "b:A = c", ← q "b:A = d"] THEN
    ASM_MESON_TAC [])

  let SWAP_GENERAL ← prove
   r"!a b c d:A.
        ~(a = b) /\ ~(c = d)
        ==> swap(a,b) o swap(c,d) = I \/
            ?x y z. ~(x = a) /\ ~(y = a) /\ ~(z = a) /\ ~(x = y) /\
                    swap(a,b) o swap(c,d) = swap(x,y) o swap(a,z)"
   (MATCH_MP_TAC SYMMETRY_LEMMA THEN CONJ_TAC THENL
     [REWRITE_TAC [SWAP_SYM] THEN SIMP_TAC [], ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THENL
     [MESON_TAC [SWAP_IDEMPOTENT],
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [← q "b:A", ← q "d:A", ← q "b:A"] THEN
      ASM_MESON_TAC [SWAP_COMMON],
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [← q "c:A", ← q "d:A", ← q "c:A"] THEN
      ASM_MESON_TAC [SWAP_COMMON'],
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [← q "c:A", ← q "d:A", ← q "b:A"] THEN
      ASM_MESON_TAC [SWAP_INDEPENDENT]])

  let FIXING_SWAPSEQ_DECREASE ← prove
   r"!n p a b:A.
      swapseq n p /\ ~(a = b) /\ (swap(a,b) o p) a = a
      ==> ~(n = 0) /\ swapseq (n - 1) (swap(a,b) o p)"
   (INDUCT_TAC THEN REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [swapseq_CASES] THEN
    REWRITE_TAC [NOT_SUC] THENL
     [DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC [I_THM, o_THM, swap] THEN MESON_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM, LEFT_AND_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q "c:A", ← q "d:A", ← q "q:A->A", ← q "m:num"] THEN
    REWRITE_TAC [SUC_INJ, ← GSYM CONJ_ASSOC] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC [o_ASSOC] THEN STRIP_TAC THEN
    MP_TAC (← SPECL [← q "a:A", ← q "b:A", ← q "c:A", ← q "d:A"] SWAP_GENERAL) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    ASM_REWRITE_TAC [I_O_ID, SUC_SUB1, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q "x:A", ← q "y:A", ← q "z:A"] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN FIRST_X_ASSUM (MP_TAC o SPECL
     [← q "q:A->A", ← q "a:A", ← q "z:A"]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o check (is_eq o concl)) THEN
      REWRITE_TAC [← GSYM o_ASSOC] THEN
      ABBREV_TAC (← q r"r:A->A = swap(a:A,z) o q") THEN
      ASM_REWRITE_TAC [FUN_EQ_THM, o_THM, swap] THEN ASM_MESON_TAC [],
      SPEC_TAC (← q "n:num", ← q "n:num") THEN INDUCT_TAC THEN
      REWRITE_TAC [NOT_SUC, SUC_SUB1, ← GSYM o_ASSOC] THEN
      ASM_MESON_TAC [swapseq_RULES]])

  let SWAPSEQ_IDENTITY_EVEN ← prove
   r"!n. swapseq n (I:A->A) ==> EVEN n"
   (← do
    let a1 ← ARITH_RULE (← q r"m - 1 < SUC m")
    pure (MATCH_MP_TAC num_WF THEN X_GEN_TAC (← q "n:num") THEN DISCH_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [swapseq_CASES] THEN
    DISCH_THEN (DISJ_CASES_THEN2 (SUBST_ALL_TAC o CONJUNCT1) MP_TAC) THEN
    REWRITE_TAC [EVEN, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q "a:A", ← q "b:A", ← q "p:A->A", ← q "m:num"] THEN
    DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THEN
    MP_TAC (← SPECL [← q "m:num", ← q "p:A->A", ← q "a:A", ← q "b:A"] FIXING_SWAPSEQ_DECREASE) THEN
    ASM_REWRITE_TAC [I_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q "m - 1")) THEN
    UNDISCH_THEN (← q r"SUC m = n") (SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC [a1] THEN UNDISCH_TAC (← q r"~(m = 0)") THEN
    SPEC_TAC (← q "m:num", ← q "m:num") THEN INDUCT_TAC THEN
    REWRITE_TAC [SUC_SUB1, EVEN]))

  -- @@RETURN BEGIN
  return { swapseq_RULES, swapseq_INDUCT, swapseq_CASES, permutation, SWAPSEQ_I,
           PERMUTATION_I, SWAPSEQ_SWAP, PERMUTATION_SWAP, SWAPSEQ_COMPOSE,
           PERMUTATION_COMPOSE, SWAPSEQ_ENDSWAP, SWAPSEQ_INVERSE_EXISTS, SWAPSEQ_INVERSE,
           PERMUTATION_INVERSE, SYMMETRY_LEMMA, SWAP_GENERAL, FIXING_SWAPSEQ_DECREASE,
           SWAPSEQ_IDENTITY_EVEN }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Parity of permutations; composition properties; abstract characterization.-/
/- (permutations.ml 844-997)                                                 -/
/- ------------------------------------------------------------------------- -/

structure Evenperm where
  -- @@FIELDS
  evenperm : thm
  SWAPSEQ_EVEN_EVEN : thm
  EVENPERM_UNIQUE : thm
  EVENPERM_I : thm
  EVENPERM_ID : thm
  EVENPERM_SWAP : thm
  EVENPERM_COMPOSE : thm
  EVENPERM_INVERSE : thm
  PERMUTATION_BIJECTIVE : thm
  PERMUTATION_FINITE_SUPPORT : thm
  PERMUTATION_LEMMA : thm
  PERMUTATION : thm
  PERMUTATION_INVERSE_WORKS : thm
  PERMUTATION_INVERSE_COMPOSE : thm
  PERMUTATION_COMPOSE_EQ : thm
  PERMUTATION_COMPOSE_SWAP : thm
  deriving Inhabited

@[nospecialize]
def setupEvenperm [HolBase] (D : PermutationsDeps) (BPermutes : Permutes) (BSwapseq : Swapseq) :
    ExceptT String IO Evenperm := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, .. } := D
  let { EVEN, EVEN_ADD, EXISTS_UNIQUE_THM, FINITE_INDUCT_STRONG, FINITE_INSERT,
        FINITE_RULES, FINITE_SUBSET, FUN_EQ_THM, IMP_CONJ, IMP_CONJ_ALT, IN_ELIM_THM,
        IN_INSERT, I_DEF, I_O_ID, I_THM, LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, .. } := D.core1
  let { NOT_IN_EMPTY, RIGHT_AND_EXISTS_THM, RIGHT_FORALL_IMP_THM, SUBSET,
        SWAP_FORALL_THM, o_ASSOC, o_THM, .. } := D.core2
  let { INJECTIVE_INVERSE_o, INVERSE_UNIQUE_o, SURJECTIVE_INVERSE_o, SWAP_IDEMPOTENT,
        swap, .. } := BPermutes
  let { PERMUTATION_COMPOSE, PERMUTATION_I, PERMUTATION_INVERSE, PERMUTATION_SWAP,
        SWAPSEQ_COMPOSE, SWAPSEQ_IDENTITY_EVEN, SWAPSEQ_INVERSE,
        SWAPSEQ_INVERSE_EXISTS, SWAPSEQ_SWAP, permutation, swapseq_INDUCT,
        swapseq_RULES, .. } := BSwapseq
  -- @@SCOPE END

  /- Therefore we have a welldefined notion of parity. -/

  let evenperm ← D.new_definition r"evenperm(p) = EVEN(@n. swapseq n p)"

  let SWAPSEQ_EVEN_EVEN ← prove
   r"!m n p:A->A. swapseq m p /\ swapseq n p ==> (EVEN m <=> EVEN n)"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP SWAPSEQ_INVERSE_EXISTS) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o AP_TERM (← q r"swapseq (n + m) :(A->A)->bool")) THEN
    ASM_SIMP_TAC [SWAPSEQ_COMPOSE] THEN
    DISCH_THEN (MP_TAC o MATCH_MP SWAPSEQ_IDENTITY_EVEN) THEN
    SIMP_TAC [EVEN_ADD])

  let EVENPERM_UNIQUE ← prove
   r"!n p b. swapseq n p /\ EVEN n = b ==> evenperm p = b"
   (REWRITE_TAC [evenperm] THEN MESON_TAC [SWAPSEQ_EVEN_EVEN])

  /- And it has the expected composition properties. -/

  let EVENPERM_I ← prove
   r"evenperm I = T"
   (MATCH_MP_TAC EVENPERM_UNIQUE THEN MESON_TAC [swapseq_RULES, EVEN])

  let EVENPERM_ID ← prove
   r"evenperm(\x:A. x)"
   (REWRITE_TAC [← GSYM I_DEF, EVENPERM_I])

  let EVENPERM_SWAP ← prove
   r"!a b:A. evenperm(swap(a,b)) = (a = b)"
   (← do
    let c2 ← ExceptT.mk (D.NUM_RED_CONV (← q r"EVEN 1"))
    let c1 ← ExceptT.mk (D.NUM_RED_CONV (← q r"EVEN 0"))
    pure (REPEAT GEN_TAC THEN MATCH_MP_TAC EVENPERM_UNIQUE THEN
    MESON_TAC [SWAPSEQ_SWAP, c1, c2]))

  let EVENPERM_COMPOSE ← prove
   r"!p q. permutation p /\ permutation q
         ==> evenperm (p o q) = (evenperm p = evenperm q)"
   (REWRITE_TAC [permutation, LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    DISCH_THEN (fun th => fun gl => ExceptT.run do
      ExceptT.mk ((ASSUME_TAC th THEN
        ASSUME_TAC (← MATCH_MP SWAPSEQ_COMPOSE th)) gl)) THEN
    ASM_MESON_TAC [EVENPERM_UNIQUE, SWAPSEQ_COMPOSE, EVEN_ADD])

  let EVENPERM_INVERSE ← prove
   r"!p. permutation p ==> evenperm(inverse p) = evenperm p"
   (REWRITE_TAC [permutation] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC EVENPERM_UNIQUE THEN
    ASM_MESON_TAC [SWAPSEQ_INVERSE, EVENPERM_UNIQUE])

  /- --------------------------------------------------------------------- -/
  /- A more abstract characterization of permutations.                     -/
  /- --------------------------------------------------------------------- -/

  let PERMUTATION_BIJECTIVE ← prove
   r"!p. permutation p ==> !y. ?!x. p(x) = y"
   (REWRITE_TAC [permutation] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP SWAPSEQ_INVERSE_EXISTS) THEN
    REWRITE_TAC [FUN_EQ_THM, I_THM, o_THM, LEFT_IMP_EXISTS_THM] THEN
    MESON_TAC [])

  let PERMUTATION_FINITE_SUPPORT ← prove
   r"!p. permutation p ==> FINITE {x:A | ~(p x = x)}"
   (← do
    let s1 ← SET_RULE (← q r"{x | F} = {}")
    pure (REWRITE_TAC [permutation, LEFT_IMP_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN MATCH_MP_TAC swapseq_INDUCT THEN
    REWRITE_TAC [I_THM, FINITE_RULES, s1] THEN
    MAP_EVERY X_GEN_TAC [← q "a:A", ← q "b:A", ← q "p:A->A"] THEN
    STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC (← q r"(a:A) INSERT b INSERT {x | ~(p x = x)}") THEN
    ASM_REWRITE_TAC [FINITE_INSERT, SUBSET, IN_INSERT, IN_ELIM_THM] THEN
    REWRITE_TAC [o_THM, swap] THEN MESON_TAC []))

  let PERMUTATION_LEMMA ← prove
   r"!s p:A->A.
       FINITE s /\
       (!y. ?!x. p(x) = y) /\ (!x. ~(x IN s) ==> p x = x)
       ==> permutation p"
   (← do
    let t2 ← TAUT (← q r"(if p then x else y) <=> p /\ x \/ ~p /\ y")
    let t1 ← TAUT (← q r"(if p then x else y) = a <=> if p then x = a else y = a")
    pure (ONCE_REWRITE_TAC [IMP_CONJ] THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
     [REWRITE_TAC [NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"p:A->A = I") (fun th => REWRITE_TAC [th, PERMUTATION_I]) THEN
      ASM_REWRITE_TAC [FUN_EQ_THM, I_THM],
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q "a:A", ← q "s:A->bool"] THEN STRIP_TAC THEN
    REWRITE_TAC [IN_INSERT] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"permutation((swap(a,p(a)) o swap(a,p(a))) o (p:A->A))")
    MP_TAC THENL [ALL_TAC, REWRITE_TAC [SWAP_IDEMPOTENT, I_O_ID]] THEN
    REWRITE_TAC [← GSYM o_ASSOC] THEN MATCH_MP_TAC PERMUTATION_COMPOSE THEN
    REWRITE_TAC [PERMUTATION_SWAP] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC (← q r"!y. ?!x. (p:A->A) x = y") THEN
      REWRITE_TAC [EXISTS_UNIQUE_THM, swap, o_THM] THEN
      ASM_CASES_TAC (← q r"(p:A->A) a = a") THEN ASM_REWRITE_TAC [] THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      REWRITE_TAC [t1] THEN
      REWRITE_TAC [t2] THEN
      ASM_MESON_TAC [],
      REWRITE_TAC [swap, o_THM] THEN
      ASM_CASES_TAC (← q r"(p:A->A) a = a") THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC []]))

  let PERMUTATION ← prove
   r"!p. permutation p <=> (!y. ?!x. p(x) = y) /\ FINITE {x:A | ~(p(x) = x)}"
   (GEN_TAC THEN EQ_TAC THEN
    SIMP_TAC [PERMUTATION_BIJECTIVE, PERMUTATION_FINITE_SUPPORT] THEN
    STRIP_TAC THEN MATCH_MP_TAC PERMUTATION_LEMMA THEN
    EXISTS_TAC (← q r"{x:A | ~(p x = x)}") THEN
    ASM_SIMP_TAC [IN_ELIM_THM])

  let PERMUTATION_INVERSE_WORKS ← prove
   r"!p. permutation p ==> inverse p o p = I /\ p o inverse p = I"
   (MESON_TAC [PERMUTATION_BIJECTIVE, SURJECTIVE_INVERSE_o,
              INJECTIVE_INVERSE_o])

  let PERMUTATION_INVERSE_COMPOSE ← prove
   r"!p q. permutation p /\ permutation q
         ==> inverse(p o q) = inverse q o inverse p"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC INVERSE_UNIQUE_o THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP PERMUTATION_INVERSE_WORKS)) THEN
    REWRITE_TAC [← GSYM o_ASSOC] THEN REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [o_ASSOC] THEN
    ASM_REWRITE_TAC [I_O_ID])

  let PERMUTATION_COMPOSE_EQ ← prove
   r"(!p q:A->A. permutation(p) ==> (permutation(p o q) <=> permutation q)) /\
   (!p q:A->A. permutation(q) ==> (permutation(p o q) <=> permutation p))"
   (← do
    let r2 ← REWRITE_RULE [IMP_CONJ] PERMUTATION_COMPOSE
    let r1 ← REWRITE_RULE [IMP_CONJ_ALT] PERMUTATION_COMPOSE
    pure (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP PERMUTATION_INVERSE) THEN
    EQ_TAC THEN ASM_SIMP_TAC [PERMUTATION_COMPOSE] THENL
     [DISCH_THEN (MP_TAC o SPEC (← q r"inverse(p:A->A)") o MATCH_MP r1),
      DISCH_THEN (MP_TAC o SPEC (← q r"inverse(q:A->A)") o MATCH_MP r2)] THEN
    ASM_SIMP_TAC [← GSYM o_ASSOC, PERMUTATION_INVERSE_WORKS] THEN
    ASM_SIMP_TAC [o_ASSOC, PERMUTATION_INVERSE_WORKS] THEN
    REWRITE_TAC [I_O_ID]))

  let PERMUTATION_COMPOSE_SWAP ← prove
   r"(!p a b:A. permutation(swap(a,b) o p) <=> permutation p) /\
   (!p a b:A. permutation(p o swap(a,b)) <=> permutation p)"
   (SIMP_TAC [PERMUTATION_COMPOSE_EQ, PERMUTATION_SWAP])

  -- @@RETURN BEGIN
  return { evenperm, SWAPSEQ_EVEN_EVEN, EVENPERM_UNIQUE, EVENPERM_I, EVENPERM_ID,
           EVENPERM_SWAP, EVENPERM_COMPOSE, EVENPERM_INVERSE, PERMUTATION_BIJECTIVE,
           PERMUTATION_FINITE_SUPPORT, PERMUTATION_LEMMA, PERMUTATION,
           PERMUTATION_INVERSE_WORKS, PERMUTATION_INVERSE_COMPOSE,
           PERMUTATION_COMPOSE_EQ, PERMUTATION_COMPOSE_SWAP }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Relation to "permutes"; induction by swaps; sign of a permutation.        -/
/- (permutations.ml 999-1129)                                                -/
/- ------------------------------------------------------------------------- -/

structure Sign where
  -- @@FIELDS
  PERMUTATION_PERMUTES : thm
  PERMUTATION_RESTRICT : thm
  PERMUTES_INDUCT : thm
  PERMUTES_INDUCT_STRONG : thm
  sign : thm
  SIGN_NZ : thm
  SIGN_I : thm
  SIGN_ID : thm
  SIGN_INVERSE : thm
  SIGN_COMPOSE : thm
  SIGN_SWAP : thm
  SIGN_IDEMPOTENT : thm
  REAL_ABS_SIGN : thm
  REAL_SGN_SIGN : thm
  EVENPERM_TRANSFER : thm
  deriving Inhabited

@[nospecialize]
def setupSign [HolBase] (D : PermutationsDeps) (BPermutes : Permutes) (BBasicCons : BasicCons) (BGroups : Groups) (BNumPerms : NumPerms) (BSwapseq : Swapseq) (BEvenperm : Evenperm) :
    ExceptT String IO Sign := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, REAL_ARITH_TAC, SET_TAC, .. } := D
  let { CONJ_ASSOC, FINITE_IMAGE, FINITE_INDUCT_STRONG, FINITE_INSERT, FINITE_SUBSET,
        FORALL_UNWIND_THM2, FUN_EQ_THM, IMP_CONJ, IMP_CONJ_ALT,
        INJECTIVE_ON_LEFT_INVERSE, IN_ELIM_THM, IN_IMAGE, IN_INSERT, I_O_ID, I_THM, .. } := D.core1
  let { MONO_EXISTS, REAL_SGN_EQ, RIGHT_FORALL_IMP_THM, SUBSET, o_ASSOC, o_DEF, o_THM, .. } := D.core2
  let { SWAP_IDEMPOTENT, SWAP_REFL, permutes, swap, .. } := BPermutes
  let { PERMUTES_ALT, PERMUTES_EMPTY, PERMUTES_IN_IMAGE, PERMUTES_RESTRICT,
        PERMUTES_SWAP, PERMUTES_TRANSFER, .. } := BBasicCons
  let { PERMUTES_COMPOSE, PERMUTES_I, .. } := BGroups
  let { PERMUTES_INSERT_LEMMA, .. } := BNumPerms
  let { PERMUTATION_COMPOSE, PERMUTATION_SWAP, .. } := BSwapseq
  let { EVENPERM_COMPOSE, EVENPERM_I, EVENPERM_ID, EVENPERM_INVERSE, EVENPERM_SWAP,
        PERMUTATION, .. } := BEvenperm
  -- @@SCOPE END

  /- Relation to "permutes". -/

  let PERMUTATION_PERMUTES ← prove
   r"!p:A->A. permutation p <=> ?s. FINITE s /\ p permutes s"
   (GEN_TAC THEN REWRITE_TAC [PERMUTATION, permutes] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
     [EXISTS_TAC (← q r"{x:A | ~(p x = x)}") THEN ASM_SIMP_TAC [IN_ELIM_THM],
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"s:A->bool") THEN
      ASM_SIMP_TAC [IN_ELIM_THM, SUBSET] THEN ASM_MESON_TAC []])

  let PERMUTATION_RESTRICT ← prove
   r"!Q (p:A->A).
        permutation p /\ (!x. Q(p x) <=> Q x)
        ==> permutation (\i. if Q i then p i else i)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [IMP_CONJ_ALT] THEN DISCH_TAC THEN
    REWRITE_TAC [PERMUTATION_PERMUTES] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_MESON_TAC [PERMUTES_RESTRICT])

  /- --------------------------------------------------------------------- -/
  /- Hence a sort of induction principle composing by swaps.               -/
  /- --------------------------------------------------------------------- -/

  let PERMUTES_INDUCT ← prove
   r"!P s. FINITE s /\
         P I /\
         (!a b:A p. a IN s /\ b IN s /\ P p /\ permutation p
                    ==> P (swap(a,b) o p))
         ==> (!p. p permutes s ==> P p)"
   (← do
    let t1 ← TAUT (← q r"a /\ b /\ c ==> d <=> b ==> a ==> c ==> d")
    pure (ONCE_REWRITE_TAC [t1] THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_REWRITE_TAC [PERMUTES_EMPTY, IN_INSERT] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"p = swap(x,p x) o swap(x,p x) o (p:A->A)") SUBST1_TAC THENL
     [REWRITE_TAC [o_ASSOC, SWAP_IDEMPOTENT, I_O_ID], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (fun th => FIRST_X_ASSUM MATCH_MP_TAC THEN ASSUME_TAC th) THEN
    ASM_MESON_TAC [PERMUTES_IN_IMAGE, IN_INSERT, PERMUTES_INSERT_LEMMA,
                  PERMUTATION_PERMUTES, FINITE_INSERT, PERMUTATION_COMPOSE,
                  PERMUTATION_SWAP]))

  let PERMUTES_INDUCT_STRONG ← prove
   r"!P s:A->bool.
        FINITE s /\
        P I /\
        (!a b p. a IN s /\ b IN s /\ ~(a = b) /\ P p /\ p permutes s
                 ==> P (swap(a,b) o p))
        ==> !p. p permutes s ==> P p"
   (← do
    let t1 ← TAUT (← q r"p ==> q <=> p ==> p /\ q")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC [t1] THEN
    MATCH_MP_TAC PERMUTES_INDUCT THEN
    ASM_SIMP_TAC [PERMUTES_I, PERMUTES_COMPOSE, PERMUTES_SWAP] THEN
    MAP_EVERY X_GEN_TAC [← q "a:A", ← q "b:A"] THEN
    ASM_CASES_TAC (← q r"a:A = b") THEN ASM_SIMP_TAC [SWAP_REFL, I_O_ID]))

  /- --------------------------------------------------------------------- -/
  /- Sign of a permutation as a real number.                               -/
  /- --------------------------------------------------------------------- -/

  let sign ← D.new_definition
   r"(sign p):real = if evenperm p then &1 else -- &1"

  let SIGN_NZ ← prove
   r"!p. ~(sign p = &0)"
   (REWRITE_TAC [sign] THEN REAL_ARITH_TAC)

  let SIGN_I ← prove
   r"sign I = &1"
   (REWRITE_TAC [sign, EVENPERM_I])

  let SIGN_ID ← prove
   r"sign(\x:A. x) = &1"
   (REWRITE_TAC [sign, EVENPERM_ID])

  let SIGN_INVERSE ← prove
   r"!p. permutation p ==> sign(inverse p) = sign p"
   (SIMP_TAC [sign, EVENPERM_INVERSE] THEN REAL_ARITH_TAC)

  let SIGN_COMPOSE ← prove
   r"!p q. permutation p /\ permutation q ==> sign(p o q) = sign(p) * sign(q)"
   (SIMP_TAC [sign, EVENPERM_COMPOSE] THEN REAL_ARITH_TAC)

  let SIGN_SWAP ← prove
   r"!a b. sign(swap(a,b)) = if a = b then &1 else -- &1"
   (REWRITE_TAC [sign, EVENPERM_SWAP])

  let SIGN_IDEMPOTENT ← prove
   r"!p. sign(p) * sign(p) = &1"
   (GEN_TAC THEN REWRITE_TAC [sign] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN CONV_TAC D.REAL_RAT_REDUCE_CONV)

  let REAL_ABS_SIGN ← prove
   r"!p. abs(sign p) = &1"
   (REWRITE_TAC [sign] THEN REAL_ARITH_TAC)

  let REAL_SGN_SIGN ← prove
   r"!p:A->A. real_sgn(sign p) = sign p"
   (GEN_TAC THEN REWRITE_TAC [sign] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_SGN_EQ] THEN
    CONV_TAC D.REAL_RAT_REDUCE_CONV)

  let EVENPERM_TRANSFER ← prove
   r"!(f:A->B) s p q.
        FINITE s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        p permutes s /\
        (!x. x IN s ==> q(f x) = f(p x)) /\
        (!y. ~(y IN IMAGE f s) ==> q y = y)
        ==> (evenperm q <=> evenperm p)"
   (GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC [CONJ_ASSOC] THEN
    ONCE_REWRITE_TAC [IMP_CONJ] THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [INJECTIVE_ON_LEFT_INVERSE]) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q "g:B->A")) THEN
    SUBGOAL_THEN
     (← q r"!p q. (!x. x IN s ==> q (f x) = f (p x)) /\
          (!y. ~(y IN IMAGE f s) ==> q y = y) <=>
          q = \x. if x IN IMAGE f s then (f:A->B) (p(g x)) else x")
     (fun th => REWRITE_TAC [th])
    THENL
     [REWRITE_TAC [FUN_EQ_THM] THEN ASM SET_TAC [],
      REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_UNWIND_THM2]] THEN
    MATCH_MP_TAC PERMUTES_INDUCT_STRONG THEN
    ASM_REWRITE_TAC [I_THM, o_THM] THEN
    SUBGOAL_THEN
     (← q r"(\x. if x IN IMAGE (f:A->B) s then f (g x) else x) = I")
    SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, I_THM] THEN ASM SET_TAC [],
      REWRITE_TAC [EVENPERM_I]] THEN
    MAP_EVERY X_GEN_TAC [← q "a:A", ← q "b:A", ← q "p:A->A"] THEN STRIP_TAC THEN
    W (MP_TAC o PART_MATCH (lhand o rand) EVENPERM_COMPOSE o rand o snd) THEN
    REWRITE_TAC [PERMUTATION_SWAP] THEN REWRITE_TAC [PERMUTATION_PERMUTES] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN (← q r"evenperm(swap(a,b)) = evenperm(swap((f:A->B) a,f b))")
    SUBST1_TAC THENL
     [REWRITE_TAC [EVENPERM_SWAP] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    W (MP_TAC o PART_MATCH (rand o rand) EVENPERM_COMPOSE o rand o snd) THEN
    REWRITE_TAC [PERMUTATION_SWAP] THEN ANTS_TAC THENL
     [REWRITE_TAC [PERMUTATION_PERMUTES] THEN
      EXISTS_TAC (← q r"IMAGE (f:A->B) s") THEN ASM_SIMP_TAC [FINITE_IMAGE] THEN
      MATCH_MP_TAC PERMUTES_TRANSFER THEN EXISTS_TAC (← q r"p:A->A") THEN
      ASM SET_TAC [],
      DISCH_THEN (SUBST1_TAC o SYM) THEN AP_TERM_TAC] THEN
    REWRITE_TAC [FUN_EQ_THM, o_DEF, swap] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [PERMUTES_ALT]) THEN
    X_GEN_TAC (← q "y:B") THEN REWRITE_TAC [IN_IMAGE] THEN
    ASM_CASES_TAC (← q r"?x. y = (f:A->B) x /\ x IN s") THEN
    ASM_REWRITE_TAC [] THENL [ALL_TAC, ASM_MESON_TAC []] THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN (← q "x:A")
     (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    ASM_SIMP_TAC [] THEN ASM_MESON_TAC [])

  -- @@RETURN BEGIN
  return { PERMUTATION_PERMUTES, PERMUTATION_RESTRICT, PERMUTES_INDUCT,
           PERMUTES_INDUCT_STRONG, sign, SIGN_NZ, SIGN_I, SIGN_ID, SIGN_INVERSE,
           SIGN_COMPOSE, SIGN_SWAP, SIGN_IDEMPOTENT, REAL_ABS_SIGN, REAL_SGN_SIGN,
           EVENPERM_TRANSFER }
  -- @@RETURN END

/- --------------------------------------------------------------------- -/
/- Sign transfer and products; more lemmas.  (permutations.ml 1130-1360)  -/
/- --------------------------------------------------------------------- -/

structure SignTransfer where
  -- @@FIELDS
  SIGN_TRANSFER : thm
  SIGN_CARTESIAN_PRODUCT : thm
  PERMUTES_NUMSET_LE : thm
  PERMUTES_NUMSET_GE : thm
  IMAGE_INVERSE_PERMUTATIONS : thm
  IMAGE_COMPOSE_PERMUTATIONS_L : thm
  IMAGE_COMPOSE_PERMUTATIONS_R : thm
  PERMUTES_IN_NUMSEG : thm
  SUM_PERMUTATIONS_INVERSE : thm
  SUM_PERMUTATIONS_COMPOSE_L : thm
  SUM_PERMUTATIONS_COMPOSE_R : thm
  CARD_EVEN_PERMUTATIONS : thm
  deriving Inhabited

@[nospecialize]
def setupSignTransfer [HolBase] (D : PermutationsDeps) (BPermutes : Permutes) (BBasicCons : BasicCons) (BGroups : Groups) (BNumPerms : NumPerms) (BSwapseq : Swapseq) (BEvenperm : Evenperm) (BSign : Sign) :
    ExceptT String IO SignTransfer := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, HAS_SIZE_CONV, MESON, MESON_TAC, SET_RULE, SET_TAC, .. } := D
  let { CARD_CLAUSES, CARD_IMAGE_INJ, CARD_UNION, CHOOSE_SUBSET_STRONG,
        EXISTS_PAIR_THM, EXTENSION, FINITE_CROSS_EQ, FINITE_IMAGE,
        FINITE_INDUCT_STRONG, FINITE_NUMSEG, FINITE_RESTRICT, FINITE_SING,
        FORALL_PAIR_THM, FUN_EQ_THM, IMP_CONJ, IN_CROSS, IN_ELIM_THM, IN_IMAGE,
        IN_INSERT, IN_NUMSEG, IN_SING, I_O_ID, I_THM, LAMBDA_PAIR_THM, LE_ANTISYM, .. } := D.core1
  let { LT_REFL, NOT_IN_EMPTY, NOT_LT, PAIR_EQ, RIGHT_FORALL_IMP_THM, SUM_IMAGE,
        num_WF, o_ASSOC, o_DEF, o_THM, real_pow, .. } := D.core2
  let { INVERSE_I, SWAP_IDEMPOTENT, permutes, .. } := BPermutes
  let { PERMUTES_ALT, PERMUTES_CARTESIAN_PRODUCT, PERMUTES_INJECTIVE,
        PERMUTES_INVERSES, PERMUTES_INVERSES_o, PERMUTES_IN_IMAGE, PERMUTES_SWAP, .. } := BBasicCons
  let { PERMUTES_COMPOSE, PERMUTES_ID, PERMUTES_INVERSE, PERMUTES_INVERSE_INVERSE, .. } := BGroups
  let { CARD_PERMUTATIONS, FINITE_PERMUTATIONS, .. } := BNumPerms
  let { PERMUTATION_SWAP, .. } := BSwapseq
  let { EVENPERM_COMPOSE, EVENPERM_SWAP, .. } := BEvenperm
  let { EVENPERM_TRANSFER, PERMUTATION_PERMUTES, SIGN_COMPOSE, SIGN_ID, sign, .. } := BSign
  -- @@SCOPE END

  let SIGN_TRANSFER ← prove
   r"!(f:A->B) s p q.
        FINITE s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        p permutes s /\
        (!x. x IN s ==> q(f x) = f(p x)) /\
        (!y. ~(y IN IMAGE f s) ==> q y = y)
        ==> sign q = sign p"
   (REPEAT GEN_TAC THEN REWRITE_TAC [sign] THEN
    DISCH_THEN (SUBST1_TAC o MATCH_MP EVENPERM_TRANSFER) THEN
    REWRITE_TAC [])

  let SIGN_CARTESIAN_PRODUCT ← prove
   r"!(p:A->A) (q:B->B) s t.
        FINITE s /\ FINITE t /\ p permutes s /\ q permutes t
        ==> sign (\(i,j). if i IN s /\ j IN t then p i,q j else i,j) =
            sign p pow CARD t * sign q pow CARD s"
   (← do
    let lemma1 ← prove
     r"!p (s:A->bool) (t:B->bool).
          p permutes s /\ FINITE s /\ FINITE t
          ==> sign (\(i,j). if i IN s /\ j IN t then p i,j else i,j) =
              sign p pow CARD t"
     (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
      REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
       [REWRITE_TAC [CARD_CLAUSES, NOT_IN_EMPTY] THEN
        REWRITE_TAC [← GSYM LAMBDA_PAIR_THM, SIGN_ID, real_pow],
        MAP_EVERY X_GEN_TAC [← q r"b:B", ← q r"t:B->bool"] THEN STRIP_TAC] THEN
      SUBGOAL_THEN
       (← q r"(\(i:A,j:B). if i IN s /\ j IN b INSERT t then p i,j else i,j) =
        (\(i,j). if i IN s /\ j IN {b} then p i,j else i,j) o
        (\(i,j). if i IN s /\ j IN t then p i,j else i,j)")
      SUBST1_TAC THENL
       [REWRITE_TAC [FUN_EQ_THM, FORALL_PAIR_THM, o_THM] THEN
        MAP_EVERY X_GEN_TAC [← q r"i:A", ← q r"j:B"] THEN
        ASM_CASES_TAC (← q r"(i:A) IN s") THEN ASM_REWRITE_TAC [IN_INSERT] THEN
        ASM_CASES_TAC (← q r"j:B = b") THEN ASM_REWRITE_TAC [NOT_IN_EMPTY] THEN
        ASM_CASES_TAC (← q r"(j:B) IN t") THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      W (MP_TAC o PART_MATCH (lhand o rand) SIGN_COMPOSE o lhand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [PERMUTATION_PERMUTES] THEN CONJ_TAC THENL
         [EXISTS_TAC (← q r"(s:A->bool) CROSS {b:B}"),
          EXISTS_TAC (← q r"(s:A->bool) CROSS (t:B->bool)")] THEN
        ASM_REWRITE_TAC [FINITE_CROSS_EQ, FINITE_SING] THEN
        MATCH_MP_TAC PERMUTES_CARTESIAN_PRODUCT THEN
        ASM_REWRITE_TAC [PERMUTES_ID],
        DISCH_THEN SUBST1_TAC] THEN
      ASM_SIMP_TAC [CARD_CLAUSES, real_pow, IN_SING] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC SIGN_TRANSFER THEN
      EXISTS_TAC (← q r"\x:A. x,(b:B)") THEN EXISTS_TAC (← q r"s:A->bool") THEN
      ASM_SIMP_TAC [PAIR_EQ, IN_IMAGE, FORALL_PAIR_THM] THEN
      ASM_MESON_TAC [])
    let lemma2 ← prove
     r"!p (s:A->bool) (t:B->bool).
          FINITE s /\ p permutes t /\ FINITE t
          ==> sign (\(i:A,j:B). if i IN s /\ j IN t then i,p j else i,j) =
              sign p pow CARD s"
     (REPEAT STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"p:B->B", ← q r"t:B->bool", ← q r"s:A->bool"]
        lemma1) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC SIGN_TRANSFER THEN
      EXISTS_TAC (← q r"\(i:B,j:A). j,i") THEN
      EXISTS_TAC (← q r"(t:B->bool) CROSS (s:A->bool)") THEN
      ASM_REWRITE_TAC [FINITE_CROSS_EQ, FORALL_PAIR_THM, IN_CROSS] THEN
      SIMP_TAC [PAIR_EQ, IN_IMAGE, IN_CROSS, EXISTS_PAIR_THM] THEN
      CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
      MATCH_MP_TAC PERMUTES_CARTESIAN_PRODUCT THEN
      ASM_REWRITE_TAC [PERMUTES_ID])
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"(\(i,j). if i IN s /\ j IN t then (p:A->A) i,(q:B->B) j else i,j) =
      (\(i,j). if i IN s /\ j IN t then p i,j else i,j) o
      (\(i,j). if i IN s /\ j IN t then i,q j else i,j)")
    SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, FORALL_PAIR_THM, o_THM] THEN REPEAT GEN_TAC THEN
      REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [PAIR_EQ]) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [PERMUTES_ALT]) THEN ASM SET_TAC [],
      W (MP_TAC o PART_MATCH (lhand o rand) SIGN_COMPOSE o lhand o snd)] THEN
    ANTS_TAC THENL
     [REWRITE_TAC [PERMUTATION_PERMUTES] THEN CONJ_TAC THEN
      EXISTS_TAC (← q r"(s:A->bool) CROSS (t:B->bool)") THEN
      ASM_SIMP_TAC [FINITE_CROSS_EQ, PERMUTES_CARTESIAN_PRODUCT, PERMUTES_ID],
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC [lemma1, lemma2]))

  /- ------------------------------------------------------------------- -/
  /- More lemmas about permutations.                                     -/
  /- ------------------------------------------------------------------- -/

  let PERMUTES_NUMSET_LE ← prove
   r"!p s:num->bool. p permutes s /\ (!i. i IN s ==> p(i) <= i) ==> p = I"
   (REPEAT GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM, I_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC num_WF THEN X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN
    ASM_CASES_TAC (← q r"(n:num) IN s") THENL [ALL_TAC, ASM_MESON_TAC [permutes]] THEN
    ASM_SIMP_TAC [← GSYM LE_ANTISYM] THEN REWRITE_TAC [← GSYM NOT_LT] THEN
    ASM_MESON_TAC [PERMUTES_INJECTIVE, LT_REFL])

  let PERMUTES_NUMSET_GE ← prove
   r"!p s:num->bool. p permutes s /\ (!i. i IN s ==> i <= p(i)) ==> p = I"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"inverse(p:num->num)", ← q r"s:num->bool"] PERMUTES_NUMSET_LE) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [PERMUTES_INVERSE, PERMUTES_INVERSES, PERMUTES_IN_IMAGE],
      ASM_MESON_TAC [PERMUTES_INVERSE_INVERSE, INVERSE_I]])

  let IMAGE_INVERSE_PERMUTATIONS ← prove
   r"!s:A->bool. {inverse p | p permutes s} = {p | p permutes s}"
   (REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
    MESON_TAC [PERMUTES_INVERSE_INVERSE, PERMUTES_INVERSE])

  let IMAGE_COMPOSE_PERMUTATIONS_L ← prove
   r"!s q:A->A. q permutes s ==> {q o p | p permutes s} = {p | p permutes s}"
   (REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"p:A->A") THEN EQ_TAC THENL
     [ASM_MESON_TAC [PERMUTES_COMPOSE],
      DISCH_TAC THEN EXISTS_TAC (← q r"inverse(q:A->A) o (p:A->A)") THEN
      ASM_SIMP_TAC [o_ASSOC, PERMUTES_INVERSE, PERMUTES_COMPOSE] THEN
      ASM_MESON_TAC [PERMUTES_INVERSES_o, I_O_ID]])

  let IMAGE_COMPOSE_PERMUTATIONS_R ← prove
   r"!s q:A->A. q permutes s ==> {p o q | p permutes s} = {p | p permutes s}"
   (REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"p:A->A") THEN EQ_TAC THENL
     [ASM_MESON_TAC [PERMUTES_COMPOSE],
      DISCH_TAC THEN EXISTS_TAC (← q r"(p:A->A) o inverse(q:A->A)") THEN
      ASM_SIMP_TAC [← GSYM o_ASSOC, PERMUTES_INVERSE, PERMUTES_COMPOSE] THEN
      ASM_MESON_TAC [PERMUTES_INVERSES_o, I_O_ID]])

  let PERMUTES_IN_NUMSEG ← prove
   r"!p n i. p permutes 1..n /\ i IN 1..n ==> 1 <= p(i) /\ p(i) <= n"
   (REWRITE_TAC [permutes, IN_NUMSEG] THEN MESON_TAC [])

  let SUM_PERMUTATIONS_INVERSE ← prove
   r"!f m n. sum {p | p permutes m..n} f =
           sum {p | p permutes m..n} (\p. f(inverse p))"
   (← do
    let s1 ← SET_RULE (← q r"{f x | p x} = IMAGE f {x | p x}")
    pure (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (funpow 2 LAND_CONV) [← GSYM IMAGE_INVERSE_PERMUTATIONS] THEN
    GEN_REWRITE_TAC (funpow 2 LAND_CONV) [s1] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← GSYM o_DEF] THEN
    MATCH_MP_TAC SUM_IMAGE THEN
    SIMP_TAC [FINITE_PERMUTATIONS, FINITE_NUMSEG, IN_ELIM_THM] THEN
    MESON_TAC [PERMUTES_INVERSE_INVERSE]))

  let SUM_PERMUTATIONS_COMPOSE_L ← prove
   r"!f m n q.
        q permutes m..n
        ==> sum {p | p permutes m..n} f =
            sum {p | p permutes m..n} (\p. f(q o p))"
   (← do
    let s1 ← SET_RULE (← q r"{f x | p x} = IMAGE f {x | p x}")
    pure (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (funpow 2 LAND_CONV)
     [← GSYM (← MATCH_MP IMAGE_COMPOSE_PERMUTATIONS_L th)])) THEN
    GEN_REWRITE_TAC (funpow 2 LAND_CONV) [s1] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← GSYM o_DEF] THEN
    MATCH_MP_TAC SUM_IMAGE THEN
    SIMP_TAC [FINITE_PERMUTATIONS, FINITE_NUMSEG, IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (fun th => tactic_of do pure (MP_TAC (← AP_TERM (← q r"\p:num->num. inverse(q:num->num) o p") th))) THEN
    REWRITE_TAC [o_ASSOC] THEN
    EVERY_ASSUM (fun th => tactic_of do pure (CONJUNCTS_THEN SUBST1_TAC (← MATCH_MP PERMUTES_INVERSES_o th))) THEN
    REWRITE_TAC [I_O_ID]))

  let SUM_PERMUTATIONS_COMPOSE_R ← prove
   r"!f m n q.
        q permutes m..n
        ==> sum {p | p permutes m..n} f =
            sum {p | p permutes m..n} (\p. f(p o q))"
   (← do
    let s1 ← SET_RULE (← q r"{f x | p x} = IMAGE f {x | p x}")
    pure (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (funpow 2 LAND_CONV)
     [← GSYM (← MATCH_MP IMAGE_COMPOSE_PERMUTATIONS_R th)])) THEN
    GEN_REWRITE_TAC (funpow 2 LAND_CONV) [s1] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← GSYM o_DEF] THEN
    MATCH_MP_TAC SUM_IMAGE THEN
    SIMP_TAC [FINITE_PERMUTATIONS, FINITE_NUMSEG, IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (fun th => tactic_of do pure (MP_TAC (← AP_TERM (← q r"\p:num->num. p o inverse(q:num->num)") th))) THEN
    REWRITE_TAC [← GSYM o_ASSOC] THEN
    EVERY_ASSUM (fun th => tactic_of do pure (CONJUNCTS_THEN SUBST1_TAC (← MATCH_MP PERMUTES_INVERSES_o th))) THEN
    REWRITE_TAC [I_O_ID]))

  let CARD_EVEN_PERMUTATIONS ← prove
   r"!s:A->bool. FINITE s /\ 2 <= CARD s
               ==> 2 * CARD {p | p permutes s /\ evenperm p} = FACT(CARD s)"
   (← do
    let m4 ← MESON []
      (← q r"(!x. f(f x) = x) ==> (!x y. P x /\ P y /\ f x = f y ==> x = y)")
    let a1 ← ARITH_RULE (← q r"b = a ==> 2 * a = a + b")
    let s3 ← SET_RULE
      (← q r"(!x. P x ==> ~P(f x)) ==> {x | P x} INTER IMAGE f {x | P x} = {}")
    let s2 ← SET_RULE
      (← q r"(!x. P x ==> P(f x)) /\ (!x. f(f x) = x) /\
      (!x. P x ==> Q x \/ Q(f x))
      ==> {x | P x} = {x | P x /\ Q x} UNION IMAGE f {x | P x /\ Q x}")
    let s5 ← SET_RULE (← q r"{p | p permutes s /\ Q p} =
                            {p | p IN {p | p permutes s} /\ Q p}")
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"?a b:A. a IN s /\ b IN s /\ ~(a = b)") STRIP_ASSUME_TAC THENL
     [MP_TAC (← SPECL [← q r"2", ← q r"s:A->bool"] CHOOSE_SUBSET_STRONG) THEN
      ASM_REWRITE_TAC [← ExceptT.mk (HAS_SIZE_CONV (← q r"s HAS_SIZE 2"))] THEN SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!p:A->A. p permutes s ==> permutation p") ASSUME_TAC THENL
     [ASM_MESON_TAC [PERMUTATION_PERMUTES], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!Q. FINITE {p:A->A | p permutes s /\ Q p}") ASSUME_TAC THENL
     [REWRITE_TAC [s5] THEN
      ASM_SIMP_TAC [FINITE_RESTRICT, FINITE_PERMUTATIONS],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"FACT(CARD s) = CARD ({p | p permutes s /\ evenperm p} UNION
                         IMAGE (\p. swap(a:A,b) o p)
                               {p | p permutes s /\ evenperm p})")
    SUBST1_TAC THENL
     [FIRST_ASSUM (SUBST1_TAC o SYM o MATCH_MP CARD_PERMUTATIONS) THEN
      AP_TERM_TAC THEN MATCH_MP_TAC s2 THEN
      ASM_SIMP_TAC [PERMUTES_COMPOSE, PERMUTES_SWAP, SWAP_IDEMPOTENT, o_ASSOC,
        I_O_ID, EVENPERM_COMPOSE, PERMUTATION_SWAP, EVENPERM_SWAP] THEN
      CONV_TAC TAUT,
      W (MP_TAC o PART_MATCH (lhs o rand) CARD_UNION o rand o snd) THEN
      ASM_SIMP_TAC [FINITE_IMAGE] THEN ANTS_TAC THENL
       [MATCH_MP_TAC s3 THEN
        ASM_SIMP_TAC [IN_ELIM_THM, EVENPERM_COMPOSE, PERMUTATION_SWAP] THEN
        ASM_REWRITE_TAC [EVENPERM_SWAP],
        DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC a1 THEN
      MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_SIMP_TAC [IN_ELIM_THM] THEN
      MATCH_MP_TAC m4 THEN
      ASM_SIMP_TAC [SWAP_IDEMPOTENT, o_ASSOC, I_O_ID]]))

  -- @@RETURN BEGIN
  return { SIGN_TRANSFER, SIGN_CARTESIAN_PRODUCT, PERMUTES_NUMSET_LE, PERMUTES_NUMSET_GE,
           IMAGE_INVERSE_PERMUTATIONS, IMAGE_COMPOSE_PERMUTATIONS_L,
           IMAGE_COMPOSE_PERMUTATIONS_R, PERMUTES_IN_NUMSEG, SUM_PERMUTATIONS_INVERSE,
           SUM_PERMUTATIONS_COMPOSE_L, SUM_PERMUTATIONS_COMPOSE_R,
           CARD_EVEN_PERMUTATIONS }
  -- @@RETURN END

/- --------------------------------------------------------------------- -/
/- The special case of involutions, and cyclic permutations.             -/
/- (permutations.ml 1356-1507)                                           -/
/- --------------------------------------------------------------------- -/

structure Involution where
  -- @@FIELDS
  PERMUTES_INVOLUTION : thm
  SIGN_INVOLUTION : thm
  PERMUTES_CYCLIC : thm
  PERMUTES_CYCLIC_N : thm
  PERMUTATION_CYCLIC : thm
  PERMUTATION_CYCLIC_N : thm
  EVENPERM_CYCLIC : thm
  EVENPERM_CYCLIC_N : thm
  SIGN_CYCLIC : thm
  SIGN_CYCLIC_N : thm
  deriving Inhabited

@[nospecialize]
def setupInvolution [HolBase] (D : PermutationsDeps) (BPermutes : Permutes) (BBasicCons : BasicCons) (BGroups : Groups) (BAltChar : AltChar) (BSwapseq : Swapseq) (BEvenperm : Evenperm) (BSign : Sign) :
    ExceptT String IO Involution := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC,
        NUM_REDUCE_CONV, REAL_RING, SET_TAC, WF_INDUCT_TAC, .. } := D
  let { ADD1, ADD_CLAUSES, ARITH, ARITH_EQ, CARD_CLAUSES, CARD_DELETE, CARD_EQ_0,
        CARD_SUBSET, COND_ID, DIV_0, EMPTY_GSPEC, EVEN, EVEN_MULT, EVEN_SUB,
        FINITE_DELETE, FINITE_NUMSEG_LT, FINITE_RULES, FINITE_SUBSET, FUN_EQ_THM,
        IMP_CONJ, IN_DELETE, IN_ELIM_THM, IN_SING, I_THM, LEFT_IMP_EXISTS_THM, LE_REFL, .. } := D.core1
  let { LE_TRANS, LT, MOD_ADD_MOD, MOD_CASES, MOD_LT, MOD_LT_EQ, MOD_MOD_REFL,
        NOT_EVEN, NOT_FORALL_THM, NOT_IN_EMPTY, NOT_SUC, ODD, REAL_POW_NEG,
        REAL_POW_ONE, SWAP_FORALL_THM, o_THM, real_pow, .. } := D.core2
  let { swap, .. } := BPermutes
  let { PERMUTES_BIJECTIONS, .. } := BBasicCons
  let { PERMUTES_COMPOSE, PERMUTES_ID, .. } := BGroups
  let { PERMUTES_FINITE_INJECTIVE, .. } := BAltChar
  let { PERMUTATION_SWAP, .. } := BSwapseq
  let { EVENPERM_COMPOSE, EVENPERM_ID, EVENPERM_SWAP, .. } := BEvenperm
  let { PERMUTATION_PERMUTES, SIGN_COMPOSE, SIGN_I, SIGN_SWAP, sign, .. } := BSign
  -- @@SCOPE END

  let PERMUTES_INVOLUTION ← prove
   r"!p s:A->bool. (!x. p(p x) = x) /\ (!x. ~(x IN s) ==> p x = x)
                 ==> p permutes s"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
    EXISTS_TAC (← q r"p:A->A") THEN ASM_MESON_TAC [])

  let SIGN_INVOLUTION ← prove
   r"!p:A->A s. FINITE s /\ (!x. p(p x) = x) /\ (!x. ~(x IN s) ==> p x = x)
              ==> sign p = --(&1) pow (CARD {x | ~(p x = x)} DIV 2)"
   (← do
    let a1 ← ARITH_RULE (← q r"2 <= n ==> n - 1 - 1 + 2 = n")
    let a2 ← ARITH_RULE (← q r"m + 2 = n ==> SUC(m DIV 2) = n DIV 2")
    let r3 ← REAL_RING (← q r"-- &1 * a:real = b ==> s * -- &1 = a ==> s = b")
    let a4 ← ARITH_RULE (← q r"n - 1 - 1 < n <=> ~(n = 0)")
    pure (ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN GEN_TAC THEN
    WF_INDUCT_TAC (← q r"CARD(s:A->bool)") THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"p:A->A = I") THEN
    ASM_SIMP_TAC [I_THM, EMPTY_GSPEC, CARD_CLAUSES, SIGN_I, DIV_0, real_pow,
                 ARITH_EQ] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [FUN_EQ_THM]) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM, I_THM, NOT_FORALL_THM] THEN
    X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"(a:A) IN s /\ p a IN s") STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"s DELETE (a:A) DELETE (p a)")) THEN
    ASM_SIMP_TAC [CARD_DELETE, FINITE_DELETE, IN_DELETE] THEN
    ASM_SIMP_TAC [CARD_EQ_0, a4] THEN
    ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"permutation(p:A->A)") ASSUME_TAC THENL
     [ASM_MESON_TAC [PERMUTATION_PERMUTES, PERMUTES_INVOLUTION], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"p o swap(a:A,p a)")) THEN
    ASM_SIMP_TAC [SIGN_COMPOSE, PERMUTATION_SWAP, SIGN_SWAP] THEN
    REWRITE_TAC [o_THM, swap] THEN ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC r3 THEN
    SUBGOAL_THEN
     (← q r"{x | ~(p (if x = a then p a else if x = p a then a else x) = x)} =
      {x:A | ~(p x = x)} DELETE a DELETE (p a)")
    SUBST1_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"FINITE {x:A | ~(p x = x)}") ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"s:A->bool") THEN
      ASM SET_TAC [],
      ASM_SIMP_TAC [CARD_DELETE, IN_ELIM_THM, FINITE_DELETE, IN_DELETE]] THEN
    REWRITE_TAC [← GSYM (← CONJUNCT2 real_pow)] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC a2 THEN
    MATCH_MP_TAC a1 THEN
    TRANS_TAC LE_TRANS (← q r"CARD {a:A,p a}") THEN CONJ_TAC THENL
     [ASM_SIMP_TAC [CARD_CLAUSES, FINITE_RULES, IN_SING, NOT_IN_EMPTY] THEN
      CONV_TAC NUM_REDUCE_CONV,
      MATCH_MP_TAC CARD_SUBSET THEN ASM SET_TAC []]))

  /- ------------------------------------------------------------------- -/
  /- Cyclic permutations realized via modular addition.                  -/
  /- ------------------------------------------------------------------- -/

  let PERMUTES_CYCLIC ← prove
   r"!n. (\i. if i < n then (i + 1) MOD n else i) permutes {i | i < n}"
   (← do
    let a1 ← ARITH_RULE (← q r"x < n ==> x + 1 < 2 * n")
    pure (GEN_TAC THEN SIMP_TAC [PERMUTES_FINITE_INJECTIVE, FINITE_NUMSEG_LT] THEN
    REWRITE_TAC [IMP_CONJ, IN_ELIM_THM] THEN SIMP_TAC [] THEN
    SIMP_TAC [MOD_CASES, a1] THEN ARITH_TAC))

  let PERMUTES_CYCLIC_N ← prove
   r"!n k. (\i. if i < n then (i + k) MOD n else i) permutes {i | i < n}"
   (GEN_TAC THEN INDUCT_TAC THEN
    SIMP_TAC [ADD_CLAUSES, MOD_LT, COND_ID, PERMUTES_ID] THEN
    SUBGOAL_THEN
     (← q r"(\i. if i < n then SUC(i + k) MOD n else i) =
      (\i. if i < n then (i + 1) MOD n else i) o
      (\i. if i < n then (i + k) MOD n else i)")
    SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, o_THM] THEN X_GEN_TAC (← q r"m:num") THEN
      ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [← CONJUNCT1 LT] THEN
      ASM_CASES_TAC (← q r"m:num < n") THEN ASM_REWRITE_TAC [MOD_LT_EQ] THEN
      REWRITE_TAC [ADD1] THEN MESON_TAC [MOD_ADD_MOD, MOD_MOD_REFL],
      MATCH_MP_TAC PERMUTES_COMPOSE THEN
      ASM_REWRITE_TAC [PERMUTES_CYCLIC]])

  let PERMUTATION_CYCLIC ← prove
   r"!n. permutation (\i. if i < n then (i + 1) MOD n else i)"
   (GEN_TAC THEN REWRITE_TAC [PERMUTATION_PERMUTES] THEN
    EXISTS_TAC (← q r"{i:num | i < n}") THEN
    ASM_REWRITE_TAC [PERMUTES_CYCLIC, FINITE_NUMSEG_LT])

  let PERMUTATION_CYCLIC_N ← prove
   r"!n k. permutation (\i. if i < n then (i + k) MOD n else i)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [PERMUTATION_PERMUTES] THEN
    EXISTS_TAC (← q r"{i:num | i < n}") THEN
    ASM_REWRITE_TAC [PERMUTES_CYCLIC_N, FINITE_NUMSEG_LT])

  let EVENPERM_CYCLIC ← prove
   r"!n. evenperm(\i. if i < n then (i + 1) MOD n else i) <=> n = 0 \/ ODD n"
   (← do
    let a1 ← ARITH_RULE (← q r"m < n ==> m < SUC n")
    let a2 ← ARITH_RULE (← q r"m + 1 < n ==> m < n /\ m < SUC n")
    let a3 ← ARITH_RULE (← q r"m + 1 < SUC n <=> m < n")
    let a4 ← ARITH_RULE (← q r"x < n ==> x + 1 < 2 * n")
    pure (INDUCT_TAC THEN REWRITE_TAC [← CONJUNCT1 LT, EVENPERM_ID, ODD] THEN
    REWRITE_TAC [NOT_SUC] THEN
    SUBGOAL_THEN
     (← q r"(\i. if i < SUC n then (i + 1) MOD SUC n else i) =
      (swap(0,n)) o (\i. if i <  n then (i + 1) MOD n else i)")
    SUBST1_TAC THENL
     [SIMP_TAC [MOD_CASES, a4] THEN
      REWRITE_TAC [FUN_EQ_THM, o_THM, swap] THEN
      POP_ASSUM_LIST (K ALL_TAC) THEN
      REWRITE_TAC [a3] THEN
      X_GEN_TAC (← q r"m:num") THEN
      ASM_CASES_TAC (← q r"m + 1 < n") THEN
      ASM_SIMP_TAC [a2] THENL
       [ASM_ARITH_TAC, ALL_TAC] THEN
      ASM_CASES_TAC (← q r"m:num < n") THEN
      ASM_SIMP_TAC [a1] THEN
      ASM_ARITH_TAC,
      ASM_SIMP_TAC [EVENPERM_COMPOSE, PERMUTATION_SWAP, PERMUTATION_CYCLIC] THEN
      REWRITE_TAC [EVENPERM_SWAP] THEN
      MESON_TAC [ODD]]))

  let EVENPERM_CYCLIC_N ← prove
   r"!n k. evenperm(\i. if i < n then (i + k) MOD n else i) <=>
         n = 0 \/ ODD n \/ EVEN k"
   (GEN_TAC THEN INDUCT_TAC THEN
    SIMP_TAC [ADD_CLAUSES, MOD_LT, COND_ID, EVENPERM_ID, ARITH] THEN
    SUBGOAL_THEN
     (← q r"(\i. if i < n then SUC(i + k) MOD n else i) =
      (\i. if i < n then (i + 1) MOD n else i) o
      (\i. if i < n then (i + k) MOD n else i)")
    SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, o_THM] THEN X_GEN_TAC (← q r"m:num") THEN
      ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [← CONJUNCT1 LT] THEN
      ASM_CASES_TAC (← q r"m:num < n") THEN ASM_REWRITE_TAC [MOD_LT_EQ] THEN
      REWRITE_TAC [ADD1] THEN MESON_TAC [MOD_ADD_MOD, MOD_MOD_REFL],
      ALL_TAC] THEN
    ASM_SIMP_TAC [EVENPERM_COMPOSE, PERMUTATION_CYCLIC_N] THEN
    REWRITE_TAC [EVENPERM_CYCLIC, EVEN, NOT_EVEN] THEN
    ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [] THEN
    MESON_TAC [NOT_EVEN])

  let SIGN_CYCLIC ← prove
   r"!n. sign(\i. if i < n then (i + 1) MOD n else i) = --(&1) pow (n - 1)"
   (← do
    let a1 ← ARITH_RULE (← q r"n <= 1 <=> n = 1 \/ n = 0")
    pure (GEN_TAC THEN REWRITE_TAC [sign, EVENPERM_CYCLIC] THEN
    REWRITE_TAC [REAL_POW_NEG, REAL_POW_ONE, EVEN_SUB, ARITH, NOT_EVEN] THEN
    ASM_CASES_TAC (← q r"n = 1") THEN ASM_REWRITE_TAC [LE_REFL, ARITH] THEN
    ASM_REWRITE_TAC [a1]))

  let SIGN_CYCLIC_N ← prove
   r"!n k. sign(\i. if i < n then (i + k) MOD n else i) =
         --(&1) pow (k * (n - 1))"
   (← do
    let a1 ← ARITH_RULE (← q r"n <= 1 <=> n = 1 \/ n = 0")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [sign, EVENPERM_CYCLIC_N] THEN
    REWRITE_TAC [REAL_POW_NEG, REAL_POW_ONE, EVEN_MULT,
                EVEN_SUB, ARITH, NOT_EVEN] THEN
    ASM_CASES_TAC (← q r"n = 1") THEN ASM_REWRITE_TAC [LE_REFL, ARITH] THEN
    ASM_REWRITE_TAC [a1] THEN
    MESON_TAC []))

  -- @@RETURN BEGIN
  return { PERMUTES_INVOLUTION, SIGN_INVOLUTION, PERMUTES_CYCLIC, PERMUTES_CYCLIC_N,
           PERMUTATION_CYCLIC, PERMUTATION_CYCLIC_N, EVENPERM_CYCLIC, EVENPERM_CYCLIC_N,
           SIGN_CYCLIC, SIGN_CYCLIC_N }
  -- @@RETURN END

/- --------------------------------------------------------------------- -/
/- Conversion for `{p | p permutes s}` where s is a set enumeration.      -/
/- (permutations.ml 1504-1531)                                           -/
/- --------------------------------------------------------------------- -/

structure Permset where
  -- @@FIELDS
  PERMSET_CONV : term → ExceptT String IO thm
  deriving Inhabited

/-- permutations.ml's `PERMSET_CONV` (the inner `let rec`), closed over the
    theorems built in the bundle. -/
partial def loc_PERMSET_CONV [HolBase] (loc_pth_empty PERMUTES_INSERT loc_pth_cross loc_pth_union
    SWAP_REFL I_O_ID IMAGE_CLAUSES : thm) : ioconv := fun tm =>
 (GEN_REWRITE_CONV id [loc_pth_empty] ORELSEC
  (GEN_REWRITE_CONV id [PERMUTES_INSERT] THENC
   ONCE_DEPTH_CONV (loc_PERMSET_CONV loc_pth_empty PERMUTES_INSERT loc_pth_cross loc_pth_union
                     SWAP_REFL I_O_ID IMAGE_CLAUSES) THENC
   REWRITE_CONV [loc_pth_cross] THENC
   REWRITE_CONV [IMAGE_CLAUSES] THENC
   REWRITE_CONV [loc_pth_union] THENC
  REWRITE_CONV [SWAP_REFL, I_O_ID])) tm

@[nospecialize]
def setupPermset [HolBase] (D : PermutationsDeps) (BPermutes : Permutes) (BBasicCons : BasicCons) (BNumPerms : NumPerms) :
    ExceptT String IO Permset := do
  -- @@SCOPE BEGIN
  let { SET_RULE, SET_TAC, .. } := D
  let { IMAGE_CLAUSES, I_O_ID, .. } := D.core1
  let { SWAP_REFL, .. } := BPermutes
  let { PERMUTES_EMPTY, .. } := BBasicCons
  let { PERMUTES_INSERT, .. } := BNumPerms
  -- @@SCOPE END

  let loc_pth_empty ← prove
   r"{p | p permutes {}} = {I}"
   (REWRITE_TAC [PERMUTES_EMPTY] THEN SET_TAC [])
  let loc_pth_cross ← SET_RULE
    (← q r"IMAGE f {x,y | x IN {} /\ y IN t} = {} /\
     IMAGE f {x,y | x IN (a INSERT s) /\ y IN t} =
     (IMAGE (\y. f(a,y)) t) UNION (IMAGE f {x,y | x IN s /\ y IN t})")
  let loc_pth_union ← SET_RULE
    (← q r"{} UNION t = t /\
     (x INSERT s) UNION t = x INSERT (s UNION t)")
  let PERMSET_CONV : term → ExceptT String IO thm ←
    pure (fun tm => ExceptT.mk (loc_PERMSET_CONV loc_pth_empty PERMUTES_INSERT loc_pth_cross loc_pth_union
           SWAP_REFL I_O_ID IMAGE_CLAUSES tm))

  -- @@RETURN BEGIN
  return { PERMSET_CONV }
  -- @@RETURN END

/- --------------------------------------------------------------------- -/
/- Sum over a set of permutations (could generalize to iteration).        -/
/- (permutations.ml 1529-1562)                                           -/
/- --------------------------------------------------------------------- -/

structure SumOver where
  -- @@FIELDS
  SUM_OVER_PERMUTATIONS_INSERT : thm
  SUM_OVER_PERMUTATIONS_NUMSEG : thm
  deriving Inhabited

@[nospecialize]
def setupSumOver [HolBase] (D : PermutationsDeps) (BPermutes : Permutes) (BNumPerms : NumPerms) :
    ExceptT String IO SumOver := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, .. } := D
  let { FINITE_INSERT, FINITE_NUMSEG, FORALL_PAIR_THM, FUN_EQ_THM, IN_ELIM_PAIR_THM,
        IN_ELIM_THM, IN_NUMSEG, I_O_ID, .. } := D.core1
  let { NUMSEG_LREC, PAIR_EQ, SUM_IMAGE, SUM_SUM_PRODUCT, o_ASSOC, o_THM, .. } := D.core2
  let { SWAP_IDEMPOTENT, permutes, swap, .. } := BPermutes
  let { FINITE_PERMUTATIONS, PERMUTES_INSERT, .. } := BNumPerms
  -- @@SCOPE END

  let SUM_OVER_PERMUTATIONS_INSERT ← prove
   r"!f a s. FINITE s /\ ~(a IN s)
           ==> sum {p:A->A | p permutes (a INSERT s)} f =
               sum (a INSERT s)
                   (\b. sum {p | p permutes s} (\q. f(swap(a,b) o q)))"
   (← do
    let lemma ← prove
     r"(\(b,p). f (swap (a,b) o p)) = f o (\(b,p). swap(a,b) o p)"
     (REWRITE_TAC [FUN_EQ_THM, FORALL_PAIR_THM, o_THM])
    let t1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [PERMUTES_INSERT] THEN
    ASM_SIMP_TAC [FINITE_PERMUTATIONS, FINITE_INSERT, SUM_SUM_PRODUCT] THEN
    REWRITE_TAC [lemma] THEN MATCH_MP_TAC SUM_IMAGE THEN
    REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"b:A", ← q r"p:A->A", ← q r"c:A", ← q r"q:A->A"] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [PAIR_EQ] THEN
    MATCH_MP_TAC t1 THEN CONJ_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o C AP_THM (← q r"a:A")) THEN
      REWRITE_TAC [o_THM, swap] THEN ASM_MESON_TAC [permutes],
      DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM (fun th => tactic_of do pure (MP_TAC (← AP_TERM (← q r"(\p:A->A. swap(a:A,c) o p)") th))) THEN
      REWRITE_TAC [o_ASSOC, SWAP_IDEMPOTENT, I_O_ID]]))

  let SUM_OVER_PERMUTATIONS_NUMSEG ← prove
   r"!f m n. m <= n
           ==> sum {p | p permutes (m..n)} f =
               sum(m..n) (\i. sum {p | p permutes (m+1..n)}
                                  (\q. f(swap(m,i) o q)))"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [← GSYM NUMSEG_LREC] THEN
    MATCH_MP_TAC SUM_OVER_PERMUTATIONS_INSERT THEN
    REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN ARITH_TAC)

  -- @@RETURN BEGIN
  return { SUM_OVER_PERMUTATIONS_INSERT, SUM_OVER_PERMUTATIONS_NUMSEG }
  -- @@RETURN END

/- ======== TRANSLATION OF LINES 1130-1562 END ======== -/

end HolLibrary.Permutations
