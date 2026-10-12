/- ---------------------------------------------------------------------- -/
/- Generic iterated operations and special cases of sums over N and R.   -/
/- ---------------------------------------------------------------------- -/
/- File: Iterate.lean
  Generic iterated operations and special cases of sums over N and R.

  Original (c) Copyright, John Harrison 1998-2007
  Original (c) Copyright, Lars Schewe 2007
  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `iterate.ml` (`needs "sets.ml"`).

  THE DESIGN.  One generic operation, `iterate`, folds a binary operation
  `op` over the part of a set where a function has "support" - the points
  where `f` differs from `op`'s neutral element.  Everything else in the
  file is a specialisation: `nsum` and `nproduct` over `:num`, `sum` and
  `product` over `:real`, `isum` and `iproduct` over `:int`.  The generic
  lemmas are proved ONCE against an abstract `monoidal op` hypothesis and
  then instantiated, which is why the "key lemmas" section
  (iterate.ml 361-889) carries most of the file's weight.

  PRIORITIZATION CHANGES MID-FILE.  Four calls bracket the file, and they
  are LOAD-BEARING because they set which type a bare numeral gets at PARSE
  time:
      iterate.ml   10   prioritize_num()     -- after `needs "sets.ml"`
      iterate.ml 1286   prioritize_num()     -- before `nsum`  (1288)
      iterate.ml 1982   prioritize_real()    -- before `sum`   (1984)
      iterate.ml 3112   prioritize_real -> prioritize_num()  RESTORES num
  So iterate.ml 1982-3111 - the real half, `sum` through
  `polynomial_function` - parses numerals as `:real`, and line 3112 puts
  `:num` back for every later file.  A theorem in the real half parsed
  under `:num` priority gets the WRONG TYPE throughout, and `sum` would
  collide with `nsum`; line 3112's restore is half of a pair, and dropping
  it silently mistypes every file that follows.  Every bundle must
  therefore be forced in iterate.ml FILE ORDER with the prioritize guards
  interleaved at their true positions.

  THE ONE PARSER DECLARATION: `parse_as_infix("..",(15,"right"))` at
  iterate.ml 16, giving the segment notation `m..n`, and it must run
  BEFORE `numseg` at 18 and before any term containing `..` is parsed.
  `<<=`, the order used by the general `iterato` section (890-1187), is
  NOT declared here - it comes from `realax.ml:18` at (12,"right") and is
  already registered by this point in the development.

  STYLE.  Written in the HolLight.Base style (HolMath/Base.lean): one `let`
  per OCaml `let`, in file order.  OCaml builds a tactic right to left, so
  where one proof's tactic contains several rules that print (SET_RULE,
  MESON), they are bound first, last one first, to keep HOL Light's message
  order.

  SECTION MAP (iterate.ml line ranges):
      13- 157  the `m..n` segment notation and its theorems
     158- 171  equivalence with the ad-hoc comprehension notation
     172- 192  NUMSEG_CONV, evaluating `m..n` for specific numerals
     193- 252  topological sorting of a finite set
     253- 277  the analogous finiteness theorem for integer segments
     278- 360  neutral, monoidal, support, iterate
     361- 889  KEY LEMMAS about the generic notion (the file's core)
     890-1187  `iterato`: iteration using a specific order `<<=`, hence
               applying to NON-COMMUTATIVE operations, with refined
               notions of domain (`dom`) and neutral element (`neut`)
    1188-1282  nproduct, iproduct, product, isum
    1283-1919  sums of natural numbers (`nsum`)
    1920-1947  cardinality of a finite union, via finite sums
    1948-1978  EXPAND_NSUM_CONV
    1979-2598  sums of real numbers (`sum`) - UNDER prioritize_real
    2599-2715  specialised to intervals of numbers
    2716-2778  partial summation and theorems specific to segments
    2779-2795  congruences for sum, needing the eta expansion
    2796-2826  EXPAND_SUM_CONV
    2827-2854  special algebraic rearrangements
    2855-2962  useful facts about real polynomial functions
    2963-3108  `polynomial_function`, a general notion
    3109-3112  make natural numbers the default again
-/

import HolMath.Sets

import HolMath.Base

namespace HolMath.Iterate

set_option maxRecDepth 8000

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/- ---------------------------------------------------------------------- -/
/- A natural notation for segments of the naturals.                       -/
/- ---------------------------------------------------------------------- -/

/-- `parse_as_infix("..",(15,"right"))` (iterate.ml 16).  Session runs it
    once, before `numseg`. -/
def setupIterateSegmentsInfix : IO Unit :=
  HolCore.Printer.parse_as_infix ("..", (15, "right"))

/-- The segment definition and its theorems, iterate.ml 18-152.  `numseg`
    (18) is the sole `new_definition`; the other twenty-eight are `prove`.
    Under `prioritize_num()` (iterate.ml 10) every bare numeral here is
    `:num`.  Requires `setupIterateSegmentsInfix` to have run first so `..`
    parses as the infix. -/
structure IterateSegments where
  /-- `numseg` (iterate.ml 18): `m..n = {x:num | m <= x /\ x <= n}`.
      `new_definition`. -/
  numseg : thm
  /-- `FINITE_NUMSEG` (iterate.ml 21): `!m n. FINITE(m..n)`. -/
  FINITE_NUMSEG : thm
  /-- `NUMSEG_COMBINE_R` (iterate.ml 27):
      `!m p n. m <= p + 1 /\ p <= n ==> ((m..p) UNION ((p+1)..n) = m..n)`. -/
  NUMSEG_COMBINE_R : thm
  /-- `NUMSEG_COMBINE_L` (iterate.ml 31):
      `!m p n. m <= p /\ p <= n + 1 ==> ((m..(p-1)) UNION (p..n) = m..n)`. -/
  NUMSEG_COMBINE_L : thm
  /-- `NUMSEG_LREC` (iterate.ml 35):
      `!m n. m <= n ==> (m INSERT ((m+1)..n) = m..n)`. -/
  NUMSEG_LREC : thm
  /-- `NUMSEG_RREC` (iterate.ml 39):
      `!m n. m <= n ==> (n INSERT (m..(n-1)) = m..n)`. -/
  NUMSEG_RREC : thm
  /-- `NUMSEG_REC` (iterate.ml 43):
      `!m n. m <= SUC n ==> (m..SUC n = (SUC n) INSERT (m..n))`. -/
  NUMSEG_REC : thm
  /-- `IN_NUMSEG` (iterate.ml 47):
      `!m n p. p IN (m..n) <=> m <= p /\ p <= n`. -/
  IN_NUMSEG : thm
  /-- `IN_NUMSEG_0` (iterate.ml 51): `!m n. m IN (0..n) <=> m <= n`. -/
  IN_NUMSEG_0 : thm
  /-- `NUMSEG_SING` (iterate.ml 55): `!n. n..n = {n}`. -/
  NUMSEG_SING : thm
  /-- `NUMSEG_EMPTY` (iterate.ml 59): `!m n. (m..n = {}) <=> n < m`. -/
  NUMSEG_EMPTY : thm
  /-- `EMPTY_NUMSEG` (iterate.ml 64): `!m n. n < m ==> m..n = {}`. -/
  EMPTY_NUMSEG : thm
  /-- `FINITE_SUBSET_NUMSEG` (iterate.ml 68):
      `!s:num->bool. FINITE s <=> ?n. s SUBSET 0..n`.  `GEN_TAC THEN EQ_TAC
      THENL [b1; b2]` - `EQ_TAC` splits into TWO goals, TWO branches. -/
  FINITE_SUBSET_NUMSEG : thm
  /-- `CARD_NUMSEG_LEMMA` (iterate.ml 78): `!m d. CARD(m..(m+d)) = d + 1`.
      `GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[..]`. -/
  CARD_NUMSEG_LEMMA : thm
  /-- `CARD_NUMSEG` (iterate.ml 85): `!m n. CARD(m..n) = (n + 1) - m`.
      `DISJ_CASES_THEN MP_TAC (ARITH_RULE ..) THENL [b1; b2]` - TWO goals,
      TWO branches. -/
  CARD_NUMSEG : thm
  /-- `HAS_SIZE_NUMSEG` (iterate.ml 94):
      `!m n. (m..n) HAS_SIZE ((n + 1) - m)`. -/
  HAS_SIZE_NUMSEG : thm
  /-- `CARD_NUMSEG_1` (iterate.ml 98): `!n. CARD(1..n) = n`. -/
  CARD_NUMSEG_1 : thm
  /-- `HAS_SIZE_NUMSEG_1` (iterate.ml 102): `!n. (1..n) HAS_SIZE n`. -/
  HAS_SIZE_NUMSEG_1 : thm
  /-- `NUMSEG_CLAUSES` (iterate.ml 106): the recursion pair for `m..0` and
      `m..SUC n`.  `REPEAT STRIP_TAC THEN COND_CASES_TAC THEN GEN_REWRITE_TAC
      I [EXTENSION] THEN ..` (`I` is identity, ZERO conversion levels). -/
  NUMSEG_CLAUSES : thm
  /-- `FINITE_INDEX_NUMSEG` (iterate.ml 114): finiteness via a `1..CARD s`
      index.  `EQ_TAC THENL [DISCH_TAC; MESON_TAC[..]]` - TWO goals, TWO
      branches; the `ISPECL [..] CARD_EQ_BIJECTIONS` is a term-list instance. -/
  FINITE_INDEX_NUMSEG : thm
  /-- `FINITE_INDEX_NUMBERS` (iterate.ml 126): finiteness via an arbitrary
      finite index set.  Bare `MESON_TAC[..]`. -/
  FINITE_INDEX_NUMBERS : thm
  /-- `INTER_NUMSEG` (iterate.ml 133):
      `!m n p q. (m..n) INTER (p..q) = (MAX m p)..(MIN n q)`. -/
  INTER_NUMSEG : thm
  /-- `DISJOINT_NUMSEG` (iterate.ml 137): disjointness of two segments. -/
  DISJOINT_NUMSEG : thm
  /-- `NUMSEG_ADD_SPLIT` (iterate.ml 141):
      `!m n p. m <= n + 1 ==> (m..(n+p) = (m..n) UNION (n+1..n+p))`. -/
  NUMSEG_ADD_SPLIT : thm
  /-- `NUMSEG_OFFSET_IMAGE` (iterate.ml 145):
      `!m n p. (m+p..n+p) = IMAGE (\i. i + p) (m..n)`.  `EQ_TAC THENL
      [DISCH_THEN(..); ALL_TAC]` - TWO goals, TWO branches. -/
  NUMSEG_OFFSET_IMAGE : thm
  /-- `SUBSET_NUMSEG` (iterate.ml 152):
      `!m n p q. (m..n) SUBSET (p..q) <=> n < m \/ p <= m /\ n <= q`.
      `EQ_TAC THENL [MESON_TAC[..]; ARITH_TAC]` - TWO goals, TWO branches. -/
  SUBSET_NUMSEG : thm
  /-- `NUMSEG_LE` (iterate.ml 161): `!n. {x | x <= n} = 0..n`.  The first of
      the comprehension-equivalence pair (iterate.ml 158-171). -/
  NUMSEG_LE : thm
  /-- `NUMSEG_LT` (iterate.ml 165):
      `!n. {x | x < n} = if n = 0 then {} else 0..(n-1)`. -/
  NUMSEG_LT : thm
  deriving Inhabited

@[nospecialize]
def setupIterateSegments [HolBase]
    (new_definition' : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic)
    (SET_TAC : List thm → tactic)
    (ARITH_RULE' : term → IO (Except String thm))
    (ARITH_TAC ASM_ARITH_TAC : tactic)
    (num_INDUCTION : thm)
    (EXTENSION IN_UNION IN_INSERT IN_SING NOT_IN_EMPTY IN_INTER IN_ELIM_THM
     IN_IMAGE SUBSET DISJOINT FINITE_RULES CARD_CLAUSES HAS_SIZE
     FINITE_SUBSET FINITE_NUMSEG_LE FINITE_INDUCT_STRONG FINITE_IMAGE
     CARD_EQ_BIJECTIONS
     LE_0 LE_CASES LE_REFL LE_TRANS NOT_LE SUC_SUB1 ADD_CLAUSES
     LE_EXISTS LEFT_IMP_EXISTS_THM ARITH MONO_EXISTS : thm) :
    ExceptT String IO IterateSegments := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let ARITH_RULE (t : term) : ExceptT String IO thm := ARITH_RULE' t
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC num_INDUCTION
  let ASM_MESON_TAC := ASM MESON_TAC

  let numseg ← new_definition
    r"m..n = {x:num | m <= x /\ x <= n}"

  let FINITE_NUMSEG ← prove
   r"!m n. FINITE(m..n)"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC (← q r"{x:num | x <= n}") THEN REWRITE_TAC [FINITE_NUMSEG_LE] THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM, numseg])

  let NUMSEG_COMBINE_R ← prove
   r"!m p n. m <= p + 1 /\ p <= n ==> ((m..p) UNION ((p+1)..n) = m..n)"
   (REWRITE_TAC [EXTENSION, IN_UNION, numseg, IN_ELIM_THM] THEN ARITH_TAC)

  let NUMSEG_COMBINE_L ← prove
   r"!m p n. m <= p /\ p <= n + 1 ==> ((m..(p-1)) UNION (p..n) = m..n)"
   (REWRITE_TAC [EXTENSION, IN_UNION, numseg, IN_ELIM_THM] THEN ARITH_TAC)

  let NUMSEG_LREC ← prove
   r"!m n. m <= n ==> (m INSERT ((m+1)..n) = m..n)"
   (REWRITE_TAC [EXTENSION, IN_INSERT, numseg, IN_ELIM_THM] THEN ARITH_TAC)

  let NUMSEG_RREC ← prove
   r"!m n. m <= n ==> (n INSERT (m..(n-1)) = m..n)"
   (REWRITE_TAC [EXTENSION, IN_INSERT, numseg, IN_ELIM_THM] THEN ARITH_TAC)

  let NUMSEG_REC ← prove
   r"!m n. m <= SUC n ==> (m..SUC n = (SUC n) INSERT (m..n))"
   (SIMP_TAC [← GSYM NUMSEG_RREC, SUC_SUB1])

  let IN_NUMSEG ← prove
   r"!m n p. p IN (m..n) <=> m <= p /\ p <= n"
   (REWRITE_TAC [numseg, IN_ELIM_THM])

  let IN_NUMSEG_0 ← prove
   r"!m n. m IN (0..n) <=> m <= n"
   (REWRITE_TAC [IN_NUMSEG, LE_0])

  let NUMSEG_SING ← prove
   r"!n. n..n = {n}"
   (REWRITE_TAC [EXTENSION, IN_SING, IN_NUMSEG] THEN ARITH_TAC)

  let NUMSEG_EMPTY ← prove
   r"!m n. (m..n = {}) <=> n < m"
   (REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, IN_NUMSEG] THEN
    MESON_TAC [NOT_LE, LE_TRANS, LE_REFL])

  let EMPTY_NUMSEG ← prove
   r"!m n. n < m ==> m..n = {}"
   (REWRITE_TAC [NUMSEG_EMPTY])

  let FINITE_SUBSET_NUMSEG ← prove
   r"!s:num->bool. FINITE s <=> ?n. s SUBSET 0..n"
   (GEN_TAC THEN EQ_TAC THENL
     [REWRITE_TAC [SUBSET, IN_NUMSEG, LE_0] THEN
      SPEC_TAC ((← q r"s:num->bool"), (← q r"s:num->bool")) THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
      MESON_TAC [LE_CASES, LE_REFL, LE_TRANS],
      MESON_TAC [FINITE_SUBSET, FINITE_NUMSEG]])

  let CARD_NUMSEG_LEMMA ← prove
   r"!m d. CARD(m..(m+d)) = d + 1"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_SIMP_TAC [ADD_CLAUSES, NUMSEG_REC, NUMSEG_SING, FINITE_RULES,
                  ← ARITH_RULE (← q r"m <= SUC(m + d)"), CARD_CLAUSES, FINITE_NUMSEG,
                  NOT_IN_EMPTY, ARITH, IN_NUMSEG, ← ARITH_RULE (← q r"~(SUC n <= n)")])

  let CARD_NUMSEG ← prove
   r"!m n. CARD(m..n) = (n + 1) - m"
   (REPEAT GEN_TAC THEN
    DISJ_CASES_THEN MP_TAC (← ARITH_RULE (← q r"n:num < m \/ m <= n")) THENL
     [ASM_MESON_TAC [NUMSEG_EMPTY, CARD_CLAUSES,
                     ← ARITH_RULE (← q r"n < m ==> ((n + 1) - m = 0)")],
      SIMP_TAC [LE_EXISTS, LEFT_IMP_EXISTS_THM, CARD_NUMSEG_LEMMA] THEN
      REPEAT STRIP_TAC THEN ARITH_TAC])

  let HAS_SIZE_NUMSEG ← prove
   r"!m n. (m..n) HAS_SIZE ((n + 1) - m)"
   (REWRITE_TAC [HAS_SIZE, FINITE_NUMSEG, CARD_NUMSEG])

  let CARD_NUMSEG_1 ← prove
   r"!n. CARD(1..n) = n"
   (REWRITE_TAC [CARD_NUMSEG] THEN ARITH_TAC)

  let HAS_SIZE_NUMSEG_1 ← prove
   r"!n. (1..n) HAS_SIZE n"
   (REWRITE_TAC [CARD_NUMSEG, HAS_SIZE, FINITE_NUMSEG] THEN ARITH_TAC)

  let NUMSEG_CLAUSES ← prove
   r"(!m. m..0 = if m = 0 then {0} else {}) /\
   (!m n. m..SUC n = if m <= SUC n then (SUC n) INSERT (m..n) else m..n)"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC [IN_NUMSEG, NOT_IN_EMPTY, IN_INSERT] THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC)

  let FINITE_INDEX_NUMSEG ← prove
   r"!s:A->bool.
        FINITE s <=>
        ?f. (!i j. i IN 1..CARD s /\ j IN 1..CARD s /\ f i = f j ==> i = j) /\
            s = IMAGE f (1..CARD s)"
   (GEN_TAC THEN
    EQ_TAC THENL [DISCH_TAC, MESON_TAC [FINITE_IMAGE, FINITE_NUMSEG]] THEN
    MP_TAC (← ISPECL [← q r"1..CARD(s:A->bool)", ← q r"s:A->bool"]
          CARD_EQ_BIJECTIONS) THEN
    ASM_REWRITE_TAC [FINITE_NUMSEG, CARD_NUMSEG_1] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC [])

  let FINITE_INDEX_NUMBERS ← prove
   r"!s:A->bool.
        FINITE s <=>
        ?k:num->bool f. (!i j. i IN k /\ j IN k /\ f i = f j ==> i = j) /\
                        FINITE k /\ s = IMAGE f k"
   (MESON_TAC [FINITE_INDEX_NUMSEG, FINITE_NUMSEG, FINITE_IMAGE])

  let INTER_NUMSEG ← prove
   r"!m n p q. (m..n) INTER (p..q) = (MAX m p)..(MIN n q)"
   (REWRITE_TAC [EXTENSION, IN_INTER, IN_NUMSEG] THEN ARITH_TAC)

  let DISJOINT_NUMSEG ← prove
   r"!m n p q. DISJOINT (m..n) (p..q) <=> n < p \/ q < m \/ n < m \/ q < p"
   (REWRITE_TAC [DISJOINT, NUMSEG_EMPTY, INTER_NUMSEG] THEN ARITH_TAC)

  let NUMSEG_ADD_SPLIT ← prove
   r"!m n p. m <= n + 1 ==> (m..(n+p) = (m..n) UNION (n+1..n+p))"
   (REWRITE_TAC [EXTENSION, IN_UNION, IN_NUMSEG] THEN ARITH_TAC)

  let NUMSEG_OFFSET_IMAGE ← prove
   r"!m n p. (m+p..n+p) = IMAGE (\i. i + p) (m..n)"
   (REWRITE_TAC [EXTENSION, IN_IMAGE, IN_NUMSEG] THEN
    REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (fun th => tactic_of do pure (
        EXISTS_TAC (← q r"x - p:num") THEN MP_TAC th)), ALL_TAC] THEN
    ARITH_TAC)

  let SUBSET_NUMSEG ← prove
   r"!m n p q. (m..n) SUBSET (p..q) <=> n < m \/ p <= m /\ n <= q"
   (REPEAT GEN_TAC THEN REWRITE_TAC [SUBSET, IN_NUMSEG] THEN
    EQ_TAC THENL [MESON_TAC [LE_TRANS, NOT_LE, LE_REFL], ARITH_TAC])

  /- ---------------------------------------------------------------------- -/
  /- Equivalence with the more ad-hoc comprehension notation.               -/
  /- ---------------------------------------------------------------------- -/

  let NUMSEG_LE ← prove
   r"!n. {x | x <= n} = 0..n"
   (REWRITE_TAC [EXTENSION, IN_NUMSEG, IN_ELIM_THM] THEN ARITH_TAC)

  let NUMSEG_LT ← prove
   r"!n. {x | x < n} = if n = 0 then {} else 0..(n-1)"
   (GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC [EXTENSION, IN_NUMSEG, IN_ELIM_THM, NOT_IN_EMPTY] THEN
    ASM_ARITH_TAC)

  return {
    numseg, FINITE_NUMSEG, NUMSEG_COMBINE_R, NUMSEG_COMBINE_L, NUMSEG_LREC,
    NUMSEG_RREC, NUMSEG_REC, IN_NUMSEG, IN_NUMSEG_0, NUMSEG_SING, NUMSEG_EMPTY,
    EMPTY_NUMSEG, FINITE_SUBSET_NUMSEG, CARD_NUMSEG_LEMMA, CARD_NUMSEG,
    HAS_SIZE_NUMSEG, CARD_NUMSEG_1, HAS_SIZE_NUMSEG_1, NUMSEG_CLAUSES,
    FINITE_INDEX_NUMSEG, FINITE_INDEX_NUMBERS, INTER_NUMSEG, DISJOINT_NUMSEG,
    NUMSEG_ADD_SPLIT, NUMSEG_OFFSET_IMAGE, SUBSET_NUMSEG, NUMSEG_LE, NUMSEG_LT }

/- ---------------------------------------------------------------------- -/
/- Conversion to evaluate m..n for specific numerals.                     -/
/- ---------------------------------------------------------------------- -/

/-- The three `MESON` lemmas of `NUMSEG_CONV` (iterate.ml 176-178), exposed so
    a later behavioural check of the conversion has its raw material.  These
    ARE theorems; the conversion built from them (below) is NOT. -/
structure NumsegConvPths where
  /-- `pth_0` (iterate.ml 176): `MESON[NUMSEG_EMPTY] \`n < m ==> m..n = {}\``. -/
  pth_0 : thm
  /-- `pth_1` (iterate.ml 177): `MESON[NUMSEG_SING] \`m..m = {m}\``. -/
  pth_1 : thm
  /-- `pth_2` (iterate.ml 178):
      `MESON[NUMSEG_LREC; ADD1] \`m <= n ==> m..n = m INSERT (SUC m..n)\``. -/
  pth_2 : thm
  deriving Inhabited

/-- `pth_0`, `pth_1` and `pth_2` of `NUMSEG_CONV` (iterate.ml 175-177). -/
@[nospecialize]
def setupNumsegConvPths [HolBase]
    (MESON' : List thm → term → IO (Except String thm))
    (S : IterateSegments) (ADD1 : thm) :
    ExceptT String IO NumsegConvPths := do
  let MESON (ths : List thm) (t : term) : ExceptT String IO thm := MESON' ths t
  let { NUMSEG_EMPTY, NUMSEG_SING, NUMSEG_LREC, .. } := S
  let pth_0 ← MESON [NUMSEG_EMPTY] (← q r"n < m ==> m..n = {}")
  let pth_1 ← MESON [NUMSEG_SING] (← q r"m..m = {m}")
  let pth_2 ← MESON [NUMSEG_LREC, ADD1] (← q r"m <= n ==> m..n = m INSERT (SUC m..n)")
  return { pth_0, pth_1, pth_2 }

/-- `let rec NUMSEG_CONV tm = ...` (iterate.ml 179). -/
partial def NUMSEG_CONV [HolBase]
    (NUM_LT_CONV NUM_LE_CONV NUM_SUC_CONV : ioconv)
    (P : NumsegConvPths) (ns_tm m_tm n_tm : term) : ioconv := fun tm => ExceptT.run do
  let { pth_0, pth_1, pth_2 } := P
  let NUMSEG_CONV := NUMSEG_CONV NUM_LT_CONV NUM_LE_CONV NUM_SUC_CONV P ns_tm m_tm n_tm
  let (nstm, nt) ← dest_comb tm
  let (nst, mt) ← dest_comb nstm
  if nst != ns_tm then throw "NUMSEG_CONV" else
  let m ← dest_numeral mt
  let n ← dest_numeral nt
  if n < m then MP_CONV NUM_LT_CONV (← INST [(mt, m_tm), (nt, n_tm)] pth_0)
  else if n == m then INST [(mt, m_tm)] pth_1
  else
    let th ← MP_CONV NUM_LE_CONV (← INST [(mt, m_tm), (nt, n_tm)] pth_2)
    CONV_RULE (funpow 2 RAND_CONV
      (LAND_CONV NUM_SUC_CONV THENC NUMSEG_CONV)) th

/- ---------------------------------------------------------------------- -/
/- Topological sorting of a finite set.                                   -/
/- ---------------------------------------------------------------------- -/

/-- `TOPOLOGICAL_SORT` (iterate.ml 196) and `FINITE_INT_SEG` (iterate.ml 256):
    the two structured proofs closing the segment sections.  Kept separate
    from `IterateSegments` because they need the general order `<<` (already a
    registered infix from wf.ml) and the integer machinery. -/
structure IterateSortSeg where
  /-- `TOPOLOGICAL_SORT` (iterate.ml 196): any antisymmetric transitive order
      `<<` on a finite set admits an index `f : 1..n` respecting it.  A deep
      proof: an inner `SUBGOAL_THEN .. ASSUME_TAC THENL [..;ALL_TAC]` (width 2),
      two `INDUCT_TAC THENL [..;ALL_TAC]` (width 2), a `SUBGOAL_THEN ..
      THENL [..;ALL_TAC]` (width 2), a `CONJ_TAC THENL [bA;bB]` (width 2), and
      inside the branches two more `ASM_CASES_TAC .. THENL` (widths 2). -/
  TOPOLOGICAL_SORT : thm
  /-- `FINITE_INT_SEG` (iterate.ml 256): the four integer segments (closed,
      half-open both ways, open) are finite.  `MATCH_MP_TAC(TAUT ..) THEN
      CONJ_TAC THENL [b1; b2]` - width 2, two branches. -/
  FINITE_INT_SEG : thm
  deriving Inhabited

@[nospecialize]
def setupIterateSortSeg [HolBase]
    (MESON_TAC : List thm → tactic)
    (SET_TAC : List thm → tactic)
    (SET_RULE' : term → IO (Except String thm))
    (ARITH_RULE' : term → IO (Except String thm))
    (ARITH_TAC ASM_ARITH_TAC INT_ARITH_TAC ASM_INT_ARITH_TAC : tactic)
    (INT_ARITH' : term → IO (Except String thm))
    (num_INDUCTION : thm)
    (S : IterateSegments)
    (HAS_SIZE_0 HAS_SIZE_SUC MEMBER_NOT_EMPTY MONO_FORALL COND_RAND
     IMP_CONJ_ALT FINITE_SUBSET FINITE_IMAGE EMPTY_GSPEC FINITE_EMPTY
     IMAGE_CLAUSES NOT_IN_EMPTY IN_IMAGE SUBSET IN_ELIM_THM EXTENSION
     INT_OF_NUM_LE INT_OF_NUM_OF_INT INT_SUB_LE
     ARITH ADD_SUB SUC_SUB1 LT_REFL : thm) :
    ExceptT String IO IterateSortSeg := do
  let SET_RULE (t : term) : ExceptT String IO thm := SET_RULE' t
  let ARITH_RULE (t : term) : ExceptT String IO thm := ARITH_RULE' t
  let INT_ARITH (t : term) : ExceptT String IO thm := INT_ARITH' t
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC num_INDUCTION
  let ASM_MESON_TAC := ASM MESON_TAC
  let { NUMSEG_CLAUSES, IN_NUMSEG, FINITE_NUMSEG, .. } := S

  let TOPOLOGICAL_SORT ← prove
   r"!(<<). (!x y:A. x << y /\ y << x ==> x = y) /\
          (!x y z. x << y /\ y << z ==> x << z)
          ==> !n s. s HAS_SIZE n
                    ==> ?f. s = IMAGE f (1..n) /\
                            (!j k. j IN 1..n /\ k IN 1..n /\ j < k
                                   ==> ~(f k << f j))"
   (GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"!n s. s HAS_SIZE n /\ ~(s = {})
                      ==> ?a:A. a IN s /\ !b. b IN (s DELETE a) ==> ~(b << a)")
    ASSUME_TAC THENL
     [INDUCT_TAC THEN
      REWRITE_TAC [HAS_SIZE_0, HAS_SIZE_SUC, ← TAUT (← q r"~(a /\ ~a)")] THEN
      X_GEN_TAC (← q r"s:A->bool") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"a:A")) THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"a:A")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"s DELETE (a:A)")) THEN
      ASM_SIMP_TAC [← SET_RULE (← q r"a IN s ==> (s DELETE a = {} <=> s = {a})")] THEN
      ASM_CASES_TAC (← q r"s = {a:A}") THEN ASM_REWRITE_TAC [] THENL
       [EXISTS_TAC (← q r"a:A") THEN SET_TAC [], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"b:A") STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC (← q r"((a:A) << (b:A)) :bool") THENL
       [EXISTS_TAC (← q r"a:A"), EXISTS_TAC (← q r"b:A")] THEN ASM SET_TAC [],
      ALL_TAC] THEN
    INDUCT_TAC THENL
     [SIMP_TAC [HAS_SIZE_0, NUMSEG_CLAUSES, ARITH, IMAGE_CLAUSES, NOT_IN_EMPTY],
      ALL_TAC] THEN
    REWRITE_TAC [HAS_SIZE_SUC] THEN X_GEN_TAC (← q r"s:A->bool") THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"SUC n", ← q r"s:A->bool"]) THEN
    ASM_REWRITE_TAC [HAS_SIZE_SUC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") MP_TAC) THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"s DELETE (a:A)")) THEN ASM_SIMP_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"f:num->A") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"\k. if k = 1 then a:A else f(k - 1)") THEN
    SIMP_TAC [← ARITH_RULE (← q r"1 <= k ==> ~(SUC k = 1)"), SUC_SUB1] THEN
    SUBGOAL_THEN (← q r"!i. i IN 1..SUC n <=> i = 1 \/ 1 < i /\ (i - 1) IN 1..n")
     (fun th => REWRITE_TAC [EXTENSION, IN_IMAGE, th])
    THENL [REWRITE_TAC [IN_NUMSEG] THEN ARITH_TAC, ALL_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC (← q r"b:A") THEN ASM_CASES_TAC (← q r"b:A = a") THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      FIRST_ASSUM (fun th => tactic_of do pure (ONCE_REWRITE_TAC [← MATCH_MP
       (← SET_RULE (← q r"~(b = a) ==> (b IN s <=> b IN (s DELETE a))")) th])) THEN
      ONCE_REWRITE_TAC [COND_RAND] THEN
      ASM_REWRITE_TAC [IN_IMAGE, IN_NUMSEG] THEN
      EQ_TAC THENL [ALL_TAC, MESON_TAC []] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"i:num")) THEN EXISTS_TAC (← q r"i + 1") THEN
      ASM_SIMP_TAC [← ARITH_RULE (← q r"1 <= x ==> 1 < x + 1 /\ ~(x + 1 = 1)"), ADD_SUB],
      MAP_EVERY X_GEN_TAC [← q r"j:num", ← q r"k:num"] THEN
      MAP_EVERY ASM_CASES_TAC [← q r"j = 1", ← q r"k = 1"] THEN
      ASM_REWRITE_TAC [LT_REFL] THENL
       [STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC [],
        ARITH_TAC,
        STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC]])

  /- ---------------------------------------------------------------------- -/
  /- Analogous finiteness theorem for segments of integers.                 -/
  /- ---------------------------------------------------------------------- -/

  let FINITE_INT_SEG ← prove
   r"(!l r. FINITE {x:int | l <= x /\ x <= r}) /\
   (!l r. FINITE {x:int | l <= x /\ x < r}) /\
   (!l r. FINITE {x:int | l < x /\ x <= r}) /\
   (!l r. FINITE {x:int | l < x /\ x < r})"
   (MATCH_MP_TAC (← TAUT (← q r"(a ==> b) /\ a ==> a /\ b")) THEN CONJ_TAC THENL
     [DISCH_TAC THEN REPEAT CONJ_TAC THEN POP_ASSUM MP_TAC THEN
      REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] FINITE_SUBSET) THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN INT_ARITH_TAC,
      REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"&0:int <= r - l") THEN
      ASM_SIMP_TAC [← INT_ARITH (← q r"~(&0 <= r - l:int) ==> ~(l <= x /\ x <= r)")] THEN
      ASM_SIMP_TAC [EMPTY_GSPEC, FINITE_EMPTY] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC (← q r"IMAGE (\n. l + &n) (0..num_of_int(r - l))") THEN
      ASM_SIMP_TAC [FINITE_IMAGE, FINITE_NUMSEG] THEN
      REWRITE_TAC [SUBSET, IN_IMAGE, IN_ELIM_THM] THEN
      REWRITE_TAC [← GSYM INT_OF_NUM_LE, IN_NUMSEG] THEN
      X_GEN_TAC (← q r"x:int") THEN STRIP_TAC THEN EXISTS_TAC (← q r"num_of_int(x - l)") THEN
      ASM_SIMP_TAC [INT_OF_NUM_OF_INT, INT_SUB_LE] THEN ASM_INT_ARITH_TAC])

  return { TOPOLOGICAL_SORT, FINITE_INT_SEG }

/- ---------------------------------------------------------------------- -/
/- Generic iteration of operation over set with finite support.           -/
/- ---------------------------------------------------------------------- -/

/-- The FOUR core definitions the whole file rests on, plus the theorems
    directly about them (iterate.ml 281-354).  `iterate op s f` folds the
    binary `op` over the SUPPORT of `f` on `s` - the points where `f` differs
    from `op`'s neutral element - using the set fold `ITSET`; `nsum`,
    `nproduct`, `sum`, `product`, `isum`, `iproduct` are all specialisations,
    and the 528-line key-lemmas section (iterate.ml 361-889) is proved against
    the abstract `monoidal op` hypothesis defined here.  Under `prioritize_num`
    (iterate.ml 10) every bare numeral is `:num`. -/
structure IterateGeneric where
  /-- `neutral` (iterate.ml 281): `neutral op = @x:A. !y. (op x y = y) /\
      (op y x = y)`.  `new_definition`; the body is a SELECT (`@`) term - the
      two-sided identity of `op`. -/
  neutral : thm
  /-- `monoidal` (iterate.ml 284): `monoidal op <=> (!x y. op x y = op y x) /\
      (!x y z. op x (op y z) = op (op x y) z) /\ (!x:A. op (neutral op) x =
      x)` - commutative, associative, with `neutral op` a left identity.
      `new_definition`. -/
  monoidal : thm
  /-- `MONOIDAL_AC` (iterate.ml 289): the AC consequences of `monoidal op`
      (both identities, commutativity, associativity, left-commutativity).
      `REWRITE_TAC[monoidal] THEN MESON_TAC[]`. -/
  MONOIDAL_AC : thm
  /-- `support` (iterate.ml 298): `support op (f:A->B) s = {x | x IN s /\
      ~(f x = neutral op)}`.  `new_definition`. -/
  support : thm
  /-- `iterate` (iterate.ml 301): `iterate op s (f:A->B) = if
      FINITE(support op f s) then ITSET (\x a. op (f x) a) (support op f s)
      (neutral op) else neutral op`.  `new_definition`. -/
  iterate : thm
  /-- `IN_SUPPORT` (iterate.ml 307): `!op (f:A->B) x s. x IN (support op f s)
      <=> x IN s /\ ~(f x = neutral op)`. -/
  IN_SUPPORT : thm
  /-- `SUPPORT_SUPPORT` (iterate.ml 311):
      `!op (f:A->B) s. support op f (support op f s) = support op f s`.
      `REWRITE_TAC[support; IN_ELIM_THM; EXTENSION] THEN REWRITE_TAC[CONJ_ACI]`
      - TWO separate `REWRITE_TAC`s in sequence. -/
  SUPPORT_SUPPORT : thm
  /-- `SUPPORT_EMPTY` (iterate.ml 315): `!op (f:A->B) s. (!x. x IN s ==> f(x) =
      neutral op) <=> support op f s = {}`. -/
  SUPPORT_EMPTY : thm
  /-- `SUPPORT_SUBSET` (iterate.ml 320):
      `!op (f:A->B) s. (support op f s) SUBSET s`. -/
  SUPPORT_SUBSET : thm
  /-- `FINITE_SUPPORT` (iterate.ml 324):
      `!op (f:A->B) s. FINITE s ==> FINITE(support op f s)`. -/
  FINITE_SUPPORT : thm
  /-- `SUPPORT_CLAUSES` (iterate.ml 328): the seven support/set-operation
      clauses (EMPTY, INSERT, DELETE, UNION, INTER, DIFF, IMAGE).  The IMAGE
      clause uses `o` composition inside (`support op (g o f)`).  Proof:
      one big `REWRITE_TAC[..]` THEN `REPEAT STRIP_TAC THEN TRY COND_CASES_TAC
      THEN ASM_MESON_TAC[]`. -/
  SUPPORT_CLAUSES : thm
  /-- `SUPPORT_DELTA` (iterate.ml 346): `!op s (f:A->B) a. support op (\x. if
      x = a then f(x) else neutral op) s = if a IN s then support op f {a}
      else {}`.  `REPEAT COND_CASES_TAC`. -/
  SUPPORT_DELTA : thm
  /-- `FINITE_SUPPORT_DELTA` (iterate.ml 354): `!op (f:A->B) a. FINITE(support
      op (\x. if x = a then f(x) else neutral op) s)`. -/
  FINITE_SUPPORT_DELTA : thm
  deriving Inhabited

@[nospecialize]
def setupIterateGeneric [HolBase]
    (new_definition' : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic)
    (EXTENSION IN_ELIM_THM NOT_IN_EMPTY SUBSET FINITE_SUBSET
     IN_INSERT IN_DELETE IN_IMAGE IN_UNION IN_INTER IN_DIFF IN_SING
     FINITE_RULES CONJ_ACI o_THM COND_RAND : thm) :
    ExceptT String IO IterateGeneric := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let ASM_MESON_TAC := ASM MESON_TAC

  let neutral ← new_definition
    r"neutral op = @x:A. !y. (op x y = y) /\ (op y x = y)"

  let monoidal ← new_definition
    r"monoidal op <=> (!x y. op x y = op y x) /\
                   (!x y z. op x (op y z) = op (op x y) z) /\
                   (!x:A. op (neutral op) x = x)"

  let MONOIDAL_AC ← prove
   r"!op. monoidal op
        ==> (!a:A. op (neutral op) a = a) /\
            (!a. op a (neutral op) = a) /\
            (!a b. op a b = op b a) /\
            (!a b c. op (op a b) c = op a (op b c)) /\
            (!a b c. op a (op b c) = op b (op a c))"
   (REWRITE_TAC [monoidal] THEN MESON_TAC [])

  let support ← new_definition
    r"support op (f:A->B) s = {x | x IN s /\ ~(f x = neutral op)}"

  let iterate ← new_definition
    r"iterate op s (f:A->B) =
        if FINITE(support op f s)
        then ITSET (\x a. op (f x) a) (support op f s) (neutral op)
        else neutral op"

  let IN_SUPPORT ← prove
   r"!op (f:A->B) x s. x IN (support op f s) <=> x IN s /\ ~(f x = neutral op)"
   (REWRITE_TAC [support, IN_ELIM_THM])

  let SUPPORT_SUPPORT ← prove
   r"!op (f:A->B) s. support op f (support op f s) = support op f s"
   (REWRITE_TAC [support, IN_ELIM_THM, EXTENSION] THEN REWRITE_TAC [CONJ_ACI])

  let SUPPORT_EMPTY ← prove
   r"!op (f:A->B) s. (!x. x IN s ==> f(x) = neutral op) <=> support op f s = {}"
   (REWRITE_TAC [IN_SUPPORT, EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY] THEN
    MESON_TAC [])

  let SUPPORT_SUBSET ← prove
   r"!op (f:A->B) s. (support op f s) SUBSET s"
   (SIMP_TAC [SUBSET, IN_SUPPORT])

  let FINITE_SUPPORT ← prove
   r"!op (f:A->B) s. FINITE s ==> FINITE(support op f s)"
   (MESON_TAC [SUPPORT_SUBSET, FINITE_SUBSET])

  let SUPPORT_CLAUSES ← prove
   r"(!(f:A->C). support op f {} = {}) /\
   (!(f:A->C) x s. support op f (x INSERT s) =
        if f(x) = neutral op then support op f s
        else x INSERT (support op f s)) /\
   (!(f:A->C) x s. support op f (s DELETE x) = (support op f s) DELETE x) /\
   (!(f:A->C) s t. support op f (s UNION t) =
                   (support op f s) UNION (support op f t)) /\
   (!(f:A->C) s t. support op f (s INTER t) =
                   (support op f s) INTER (support op f t)) /\
   (!(f:A->C) s t. support op f (s DIFF t) =
                   (support op f s) DIFF (support op f t)) /\
   (!(f:A->B) (g:B->C) s.
                   support op g (IMAGE f s) = IMAGE f (support op (g o f) s))"
   (REWRITE_TAC [support, EXTENSION, IN_ELIM_THM, IN_INSERT, IN_DELETE, o_THM,
      IN_IMAGE, NOT_IN_EMPTY, IN_UNION, IN_INTER, IN_DIFF, COND_RAND] THEN
    REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN ASM_MESON_TAC [])

  let SUPPORT_DELTA ← prove
   r"!op s (f:A->B) a.
        support op (\x. if x = a then f(x) else neutral op) s =
        if a IN s then support op f {a} else {}"
   (REWRITE_TAC [EXTENSION, support, IN_ELIM_THM, IN_SING] THEN
    REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
    ASM_REWRITE_TAC [IN_ELIM_THM, NOT_IN_EMPTY])

  let FINITE_SUPPORT_DELTA ← prove
   r"!op (f:A->B) a.
        FINITE(support op (\x. if x = a then f(x) else neutral op) s)"
   (REWRITE_TAC [SUPPORT_DELTA] THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN SIMP_TAC [FINITE_RULES, FINITE_SUPPORT])

  return {
    neutral, monoidal, MONOIDAL_AC, support, iterate, IN_SUPPORT,
    SUPPORT_SUPPORT, SUPPORT_EMPTY, SUPPORT_SUBSET, FINITE_SUPPORT,
    SUPPORT_CLAUSES, SUPPORT_DELTA, FINITE_SUPPORT_DELTA }

/- ---------------------------------------------------------------------- -/
/- Key lemmas about the generic notion.                                   -/
/- ---------------------------------------------------------------------- -/

/-- The FIRST key-lemmas bundle, iterate.ml 364-539: the eighteen structural
    lemmas from `ITERATE_SUPPORT` to `ITERATE_DELETE` - support-invariance,
    the `iterate` recursion clauses, union/difference/inclusion-exclusion,
    the closure/relation induction principles, `ITERATE_EQ_NEUTRAL`,
    `ITERATE_SING`, the nonempty variants and `ITERATE_DELETE`. -/
structure IterateKey1 where
  /-- `ITERATE_SUPPORT` (iterate.ml 364): `!op (f:A->B) s. iterate op
      (support op f s) f = iterate op s f`.  `SIMP_TAC[iterate;
      SUPPORT_SUPPORT]`. -/
  ITERATE_SUPPORT : thm
  /-- `ITERATE_EXPAND_CASES` (iterate.ml 368): `iterate op s f = if
      FINITE(support op f s) then iterate op (support op f s) f else neutral
      op`.  `SIMP_TAC[iterate; SUPPORT_SUPPORT]`. -/
  ITERATE_EXPAND_CASES : thm
  /-- `ITERATE_CLAUSES_GEN` (iterate.ml 375): the empty/insert recursion under
      a FINITE-SUPPORT hypothesis.  `ONCE_REWRITE_TAC[AND_FORALL_THM]`, an
      `ISPECL [..] FINITE_RECURSION`, `ANTS_TAC THENL [..;ALL_TAC]` (width 2),
      a `GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o LAND_CONV) [COND_RAND]`
      (THREE conversion levels, LAND runs FIRST). -/
  ITERATE_CLAUSES_GEN : thm
  /-- `ITERATE_CLAUSES` (iterate.ml 394): the empty/insert recursion under a
      FINITE hypothesis.  `SIMP_TAC[ITERATE_CLAUSES_GEN; FINITE_SUPPORT]`. -/
  ITERATE_CLAUSES : thm
  /-- `ITERATE_UNION` (iterate.ml 404): iterate over a disjoint union splits.
      Local `lemma` proved by `SET_TAC[]`; `MATCH_MP_TAC
      FINITE_INDUCT_STRONG`. -/
  ITERATE_UNION : thm
  /-- `ITERATE_UNION_GEN` (iterate.ml 421): the support-based union split.
      `ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN SIMP_TAC[SUPPORT_CLAUSES;
      ITERATE_UNION]`. -/
  ITERATE_UNION_GEN : thm
  /-- `ITERATE_DIFF` (iterate.ml 430): `op (iterate op (s DIFF t) f) (iterate
      op t f) = iterate op s f`.  Local `lemma` by `SET_TAC[]`; then bare
      `MESON_TAC[..]`. -/
  ITERATE_DIFF : thm
  /-- `ITERATE_DIFF_GEN` (iterate.ml 441): the support-based difference split.
      `ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN SIMP_TAC[SUPPORT_CLAUSES;
      ITERATE_DIFF]`. -/
  ITERATE_DIFF_GEN : thm
  /-- `ITERATE_INCL_EXCL` (iterate.ml 450): the two-set inclusion-exclusion
      identity.  Three `GEN_REWRITE_TAC` with `SET_RULE` rewrites at
      `LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV` and `LAND_CONV o RAND_CONV o
      ONCE_DEPTH_CONV` (THREE levels each, LAND/RAND run FIRST), a big
      `ASM_SIMP_TAC` with four DISJOINT `SET_RULE`s, then `FIRST_X_ASSUM(fun th
      -> REWRITE_TAC[MATCH_MP MONOIDAL_AC th])`. -/
  ITERATE_INCL_EXCL : thm
  /-- `ITERATE_CLOSED` (iterate.ml 471): a predicate closed under `op` and
      holding at `neutral` holds at the iterate.  `ONCE_REWRITE_TAC
      [ITERATE_EXPAND_CASES]`, `SPEC_TAC(support op f s, s)`, `MATCH_MP_TAC
      FINITE_INDUCT_STRONG`. -/
  ITERATE_CLOSED : thm
  /-- `ITERATE_RELATED` (iterate.ml 483): a congruence for a relation `R`
      preserved by `op`.  `REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC
      FINITE_INDUCT_STRONG`. -/
  ITERATE_RELATED : thm
  /-- `ITERATE_EQ_NEUTRAL` (iterate.ml 496): if `f` is `neutral` on `s` the
      iterate is `neutral`.  `SUBGOAL_THEN (support = {}) ASSUME_TAC THENL
      [b1; b2]` (width 2). -/
  ITERATE_EQ_NEUTRAL : thm
  /-- `ITERATE_SING` (iterate.ml 505): `iterate op {x} f = f x`.
      `SIMP_TAC[ITERATE_CLAUSES; FINITE_RULES; NOT_IN_EMPTY] THEN
      MESON_TAC[monoidal]`. -/
  ITERATE_SING : thm
  /-- `ITERATE_CLOSED_NONEMPTY` (iterate.ml 510): the closure principle for a
      predicate closed only under `op` (no `neutral` obligation), on a NONEMPTY
      finite set.  `MATCH_MP_TAC FINITE_INDUCT_STRONG`, `ASM_CASES_TAC (t =
      {})`. -/
  ITERATE_CLOSED_NONEMPTY : thm
  /-- `ITERATE_RELATED_NONEMPTY` (iterate.ml 523): the relation congruence on a
      NONEMPTY finite set.  `MATCH_MP_TAC FINITE_INDUCT_STRONG`, `ASM_CASES_TAC
      (t = {})`. -/
  ITERATE_RELATED_NONEMPTY : thm
  /-- `ITERATE_DELETE` (iterate.ml 539): `op (f a) (iterate op (s DELETE a) f)
      = iterate op s f`.  Bare `MESON_TAC[..]`. -/
  ITERATE_DELETE : thm
  deriving Inhabited

@[nospecialize]
def setupIterateKey1 [HolBase]
    (MESON_TAC : List thm → tactic)
    (SET_TAC : List thm → tactic)
    (SET_RULE' : term → IO (Except String thm))
    (G : IterateGeneric)
    (FINITE_RECURSION FINITE_INDUCT_STRONG
     FINITE_SUPPORT FINITE_INSERT FINITE_UNION FINITE_DIFF FINITE_INTER
     FINITE_DELETE FINITE_SUBSET SUBSET_DIFF INSERT_DELETE FINITE_RULES
     IN_INSERT IN_UNION IN_DELETE NOT_IN_EMPTY UNION_EMPTY
     EXTENSION FORALL_IN_INSERT NOT_INSERT_EMPTY
     REAL_ADD_RID COND_RAND COND_ID AND_FORALL_THM IMP_CONJ
     RIGHT_FORALL_IMP_THM : thm) :
    ExceptT String IO IterateKey1 := do
  let SET_RULE (t : term) : ExceptT String IO thm := SET_RULE' t
  let ASM_MESON_TAC := ASM MESON_TAC
  let { monoidal, iterate, MONOIDAL_AC, IN_SUPPORT, SUPPORT_SUPPORT,
        SUPPORT_CLAUSES, .. } := G

  let ITERATE_SUPPORT ← prove
   r"!op (f:A->B) s. iterate op (support op f s) f = iterate op s f"
   (SIMP_TAC [iterate, SUPPORT_SUPPORT])

  let ITERATE_EXPAND_CASES ← prove
   r"!op (f:A->B) s.
        iterate op s f =
        if FINITE(support op f s) then iterate op (support op f s) f
        else neutral op"
   (SIMP_TAC [iterate, SUPPORT_SUPPORT])

  let ITERATE_CLAUSES_GEN ← prove
   r"!op. monoidal op
        ==> (!(f:A->B). iterate op {} f = neutral op) /\
            (!f x s. FINITE(support op (f:A->B) s)
                     ==> (iterate op (x INSERT s) f =
                                if x IN s then iterate op s f
                                else op (f x) (iterate op s f)))"
   (GEN_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC [AND_FORALL_THM] THEN GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"\x a. (op:B->B->B) ((f:A->B)(x)) a", ← q r"neutral op :B"]
     FINITE_RECURSION) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [monoidal], ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [iterate, SUPPORT_CLAUSES, FINITE_RULES] THEN
    GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o LAND_CONV) [COND_RAND] THEN
    ASM_REWRITE_TAC [SUPPORT_CLAUSES, FINITE_INSERT, COND_ID] THEN
    ASM_CASES_TAC (← q r"(f:A->B) x = neutral op") THEN
    ASM_SIMP_TAC [IN_SUPPORT] THEN COND_CASES_TAC THEN ASM_MESON_TAC [monoidal])

  let ITERATE_CLAUSES ← prove
   r"!op. monoidal op
        ==> (!(f:A->C). iterate op {} f = neutral op) /\
            (!(f:B->C) x s.
                FINITE(s)
                ==> (iterate op (x INSERT s) f =
                     if x IN s then iterate op s f
                     else op (f x) (iterate op s f)))"
   (SIMP_TAC [ITERATE_CLAUSES_GEN, FINITE_SUPPORT])

  let ITERATE_UNION ← prove
   r"!op. monoidal op
        ==> !(f:A->B) s t.
                FINITE s /\ FINITE t /\ DISJOINT s t
                ==> (iterate op (s UNION t) f =
                     op (iterate op s f) (iterate op t f))"
   (← do
    let lemma ← prove
     r"(s UNION (x INSERT t) = x INSERT (s UNION t)) /\
       (DISJOINT s (x INSERT t) <=> ~(x IN s) /\ DISJOINT s t)"
      (SET_TAC [])
    pure
     (GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN
      REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      ASM_SIMP_TAC [ITERATE_CLAUSES, IN_UNION, UNION_EMPTY, REAL_ADD_RID, lemma,
                    FINITE_UNION] THEN
      ASM_MESON_TAC [monoidal]))

  let ITERATE_UNION_GEN ← prove
   r"!op. monoidal op
        ==> !(f:A->B) s t. FINITE(support op f s) /\ FINITE(support op f t) /\
                           DISJOINT (support op f s) (support op f t)
                           ==> (iterate op (s UNION t) f =
                                op (iterate op s f) (iterate op t f))"
   (ONCE_REWRITE_TAC [← GSYM ITERATE_SUPPORT] THEN
    SIMP_TAC [SUPPORT_CLAUSES, ITERATE_UNION])

  let ITERATE_DIFF ← prove
   r"!op. monoidal op
        ==> !(f:A->B) s t.
                FINITE s /\ t SUBSET s
                ==> (op (iterate op (s DIFF t) f) (iterate op t f) =
                     iterate op s f)"
   (← do
    let lemma ← prove
     r"t SUBSET s ==> (s = (s DIFF t) UNION t) /\ DISJOINT (s DIFF t) t"
      (SET_TAC [])
    pure (MESON_TAC [lemma, ITERATE_UNION, FINITE_UNION, FINITE_SUBSET, SUBSET_DIFF]))

  let ITERATE_DIFF_GEN ← prove
   r"!op. monoidal op
        ==> !f:A->B s t. FINITE (support op f s) /\
                         (support op f t) SUBSET (support op f s)
                         ==> (op (iterate op (s DIFF t) f) (iterate op t f) =
                              iterate op s f)"
   (ONCE_REWRITE_TAC [← GSYM ITERATE_SUPPORT] THEN
    SIMP_TAC [SUPPORT_CLAUSES, ITERATE_DIFF])

  -- OCaml builds this tactic right to left, so its SET_RULEs run (and
  -- print) from the last to the first.
  let ITERATE_INCL_EXCL ← prove
   r"!op. monoidal op
        ==> !s t (f:A->B).
                FINITE s /\ FINITE t
                ==> op (iterate op s f) (iterate op t f) =
                    op (iterate op (s UNION t) f)
                       (iterate op (s INTER t) f)"
   (← do
    let d4 ← SET_RULE (← q r"DISJOINT (s DIFF s') (s INTER s')")
    let d3 ← SET_RULE (← q r"DISJOINT (s DIFF s') (s' INTER s)")
    let d2 ← SET_RULE (← q r"DISJOINT (s DIFF s') (s' DIFF s)")
    let d1 ← SET_RULE (← q r"DISJOINT (s DIFF s' UNION s' DIFF s) (s INTER s')")
    let r3 ← SET_RULE (← q r"t:A->bool = t DIFF s UNION s INTER t")
    let r2 ← SET_RULE (← q r"s:A->bool = s DIFF t UNION s INTER t")
    let r1 ← SET_RULE (← q r"a UNION b = ((a DIFF b) UNION (b DIFF a)) UNION (a INTER b)")
    pure
     (REPEAT STRIP_TAC THEN
      ONCE_REWRITE_TAC [r1] THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [r2] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [r3] THEN
      ASM_SIMP_TAC [ITERATE_UNION, FINITE_UNION, FINITE_DIFF, FINITE_INTER,
        d1, d2, d3, d4] THEN
      FIRST_X_ASSUM (fun th => tactic_of do pure (
        REWRITE_TAC [← MATCH_MP MONOIDAL_AC th]))))

  let ITERATE_CLOSED ← prove
   r"!op. monoidal op
        ==> !P. P(neutral op) /\ (!x y. P x /\ P y ==> P (op x y))
                ==> !f:A->B s. (!x. x IN s /\ ~(f x = neutral op) ==> P(f x))
                               ==> P(iterate op s f)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [ITERATE_EXPAND_CASES] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [← GSYM IN_SUPPORT] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [] THEN POP_ASSUM MP_TAC THEN
    SPEC_TAC ((← q r"support op (f:A->B) s"), (← q r"s:A->bool")) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [ITERATE_CLAUSES, FINITE_INSERT, IN_INSERT])

  let ITERATE_RELATED ← prove
   r"!op. monoidal op
        ==> !R. R (neutral op) (neutral op) /\
                (!x1 y1 x2 y2. R x1 x2 /\ R y1 y2 ==> R (op x1 y1) (op x2 y2))
                ==> !f:A->B g s.
                      FINITE s /\
                      (!x. x IN s ==> R (f x) (g x))
                      ==> R (iterate op s f) (iterate op s g)"
   (GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
    GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [ITERATE_CLAUSES, FINITE_INSERT, IN_INSERT])

  let ITERATE_EQ_NEUTRAL ← prove
   r"!op. monoidal op
        ==> !f:A->B s. (!x. x IN s ==> (f(x) = neutral op))
                       ==> (iterate op s f = neutral op)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"support op (f:A->B) s = {}") ASSUME_TAC THENL
     [ASM_MESON_TAC [EXTENSION, NOT_IN_EMPTY, IN_SUPPORT],
      ASM_MESON_TAC [ITERATE_CLAUSES, FINITE_RULES, ITERATE_SUPPORT]])

  let ITERATE_SING ← prove
   r"!op. monoidal op ==> !f:A->B x. (iterate op {x} f = f x)"
   (SIMP_TAC [ITERATE_CLAUSES, FINITE_RULES, NOT_IN_EMPTY] THEN
    MESON_TAC [monoidal])

  let ITERATE_CLOSED_NONEMPTY ← prove
   r"!op. monoidal op
        ==> !P. (!x y. P x /\ P y ==> P (op x y))
                ==> !f:A->B s. FINITE s /\ ~(s = {}) /\
                               (!x. x IN s ==> P(f x))
                               ==> P(iterate op s f)"
   (GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    REWRITE_TAC [IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY, NOT_INSERT_EMPTY] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:A", ← q r"t:A->bool"] THEN
    ASM_CASES_TAC (← q r"t:A->bool = {}") THEN
    ASM_SIMP_TAC [ITERATE_SING] THEN ASM_SIMP_TAC [ITERATE_CLAUSES])

  let ITERATE_RELATED_NONEMPTY ← prove
   r"!op. monoidal op
        ==> !R. (!x1 y1 x2 y2. R x1 x2 /\ R y1 y2 ==> R (op x1 y1) (op x2 y2))
                ==> !f:A->B g s.
                      FINITE s /\
                      ~(s = {}) /\
                      (!x. x IN s ==> R (f x) (g x))
                      ==> R (iterate op s f) (iterate op s g)"
   (GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY, NOT_INSERT_EMPTY] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:A", ← q r"t:A->bool"] THEN
    ASM_CASES_TAC (← q r"t:A->bool = {}") THEN
    ASM_SIMP_TAC [ITERATE_SING] THEN ASM_SIMP_TAC [ITERATE_CLAUSES])

  let ITERATE_DELETE ← prove
   r"!op. monoidal op
        ==> !f:A->B s a. FINITE s /\ a IN s
                         ==> op (f a) (iterate op (s DELETE a) f) =
                             iterate op s f"
   (MESON_TAC [ITERATE_CLAUSES, FINITE_DELETE, IN_DELETE, INSERT_DELETE])

  return {
    ITERATE_SUPPORT, ITERATE_EXPAND_CASES, ITERATE_CLAUSES_GEN,
    ITERATE_CLAUSES, ITERATE_UNION, ITERATE_UNION_GEN, ITERATE_DIFF,
    ITERATE_DIFF_GEN, ITERATE_INCL_EXCL, ITERATE_CLOSED, ITERATE_RELATED,
    ITERATE_EQ_NEUTRAL, ITERATE_SING, ITERATE_CLOSED_NONEMPTY,
    ITERATE_RELATED_NONEMPTY, ITERATE_DELETE }

/-- The SECOND key-lemmas bundle, iterate.ml 546-703: the eleven mapping and
    congruence lemmas from `ITERATE_DELTA` to `ITERATE_OP` - the delta
    evaluation, image/bijection reindexing, the iterate-of-iterate PRODUCT
    identity, `ITERATE_EQ` and its restrict/general/inverse variants,
    injection, the nonzero union split and `ITERATE_OP`. -/
structure IterateKey2 where
  /-- `ITERATE_DELTA` (iterate.ml 546): `iterate op s (\x. if x = a then f x
      else neutral op) = if a IN s then f a else neutral op`.
      `ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN REWRITE_TAC[SUPPORT_DELTA]
      THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[..] THEN
      REWRITE_TAC[SUPPORT_CLAUSES] THEN COND_CASES_TAC THEN ASM_SIMP_TAC`. -/
  ITERATE_DELTA : thm
  /-- `ITERATE_IMAGE` (iterate.ml 556): reindexing along an injection.  An
      inner `SUBGOAL_THEN .. ASSUME_TAC THENL [b1; b2]` (width 2); the second
      branch closes with a nested `REPEAT STRIP_TAC THENL [b; b]` (width 2)
      inside a `MATCH_MP_TAC(TAUT ..)`. -/
  ITERATE_IMAGE : thm
  /-- `ITERATE_BIJECTION` (iterate.ml 578): invariance under a bijection of the
      index set.  `MATCH_MP_TAC EQ_TRANS`, `CONJ_TAC THENL [b1; b2]` (width 2);
      the second branch does `FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
      (INST_TYPE [aty,bty] ITERATE_IMAGE))` - the `o` composes `MATCH_MP` after
      `MATCH_MP (INST_TYPE ..)`. -/
  ITERATE_BIJECTION : thm
  /-- `ITERATE_ITERATE_PRODUCT` (iterate.ml 591): a double iterate over a
      dependent index set collapses to one over the product.  The file's
      heaviest key lemma (33 lines).  `MATCH_MP_TAC FINITE_INDUCT_STRONG`, TWO
      `FIRST_ASSUM(fun th -> W(MP_TAC o PART_MATCH (lhand o rand) (MATCH_MP TH
      th) o rand o snd))` sites (`ITERATE_UNION`, `ITERATE_IMAGE`), each
      followed by `ANTS_TAC THENL [..; ALL_TAC]` (width 2), and two
      `CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV)`. -/
  ITERATE_ITERATE_PRODUCT : thm
  /-- `ITERATE_EQ` (iterate.ml 624): pointwise-equal functions give equal
      iterates.  `ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES]`, a `SUBGOAL_THEN
      (support g s = support f s) SUBST1_TAC THENL [b1; ALL_TAC]` (width 2), a
      `SUBGOAL_THEN .. MP_TAC THENL [ASM_MESON_TAC[..]; REWRITE_TAC[IMP_CONJ]]`
      (width 2), `SPEC_TAC` then `MATCH_MP_TAC FINITE_INDUCT_STRONG`. -/
  ITERATE_EQ : thm
  /-- `ITERATE_RESTRICT_SET` (iterate.ml 640): iterate over a comprehension
      subset equals iterate with a guarded function.  `ONCE_REWRITE_TAC[GSYM
      ITERATE_SUPPORT]`, a `MESON[]` rewrite lemma, then
      `FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_EQ)`. -/
  ITERATE_RESTRICT_SET : thm
  /-- `ITERATE_EQ_GENERAL` (iterate.ml 652): reindexing by a general bijection
      `h`.  A `SUBGOAL_THEN (t = IMAGE h s) SUBST1_TAC THENL [b1; ALL_TAC]`
      (width 2), `MATCH_MP_TAC EQ_TRANS`, `CONJ_TAC THENL [b1; b2]` (width 2),
      with `CONV_TAC SYM_CONV` and `FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
      ITERATE_IMAGE)`. -/
  ITERATE_EQ_GENERAL : thm
  /-- `ITERATE_EQ_GENERAL_INVERSES` (iterate.ml 668): the two-sided-inverse
      reindexing form.  `FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
      ITERATE_EQ_GENERAL) THEN EXISTS_TAC `h:A->B` THEN ASM_MESON_TAC[]`. -/
  ITERATE_EQ_GENERAL_INVERSES : thm
  /-- `ITERATE_INJECTION` (iterate.ml 678): invariance under an injective
      self-map of a finite set.  `CONV_TAC SYM_CONV`, `FIRST_X_ASSUM
      (MATCH_MP_TAC o MATCH_MP ITERATE_BIJECTION)`, then an `ISPECL [..]
      SURJECTIVE_IFF_INJECTIVE`. -/
  ITERATE_INJECTION : thm
  /-- `ITERATE_UNION_NONZERO` (iterate.ml 690): the union split when `f` is
      neutral on the intersection.  `ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT]`,
      `FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_UNION)`. -/
  ITERATE_UNION_NONZERO : thm
  /-- `ITERATE_OP` (iterate.ml 703): iterate distributes over a pointwise `op`.
      `MATCH_MP_TAC FINITE_INDUCT_STRONG THEN ASM_SIMP_TAC[ITERATE_CLAUSES;
      MONOIDAL_AC]`. -/
  ITERATE_OP : thm
  deriving Inhabited

@[nospecialize]
def setupIterateKey2 [HolBase]
    (MESON' : List thm → term → IO (Except String thm))
    (MESON_TAC : List thm → tactic)
    (SET_RULE' : term → IO (Except String thm))
    (GEN_BETA_CONV : ioconv)
    (G : IterateGeneric) (K1 : IterateKey1)
    (FINITE_INDUCT_STRONG FINITE_IMAGE FINITE_IMAGE_INJ_EQ
     FINITE_PRODUCT_DEPENDENT FINITE_INSERT FINITE_SUPPORT
     SURJECTIVE_IFF_INJECTIVE IMAGE_CLAUSES EQ_TRANS DISJOINT CONJ_ASSOC
     IN_INSERT IN_IMAGE IN_INTER IN_ELIM_THM NOT_IN_EMPTY EXTENSION SUBSET
     o_THM o_DEF ETA_AX PAIR_EQ FORALL_PAIR_THM EXISTS_PAIR_THM
     IMP_CONJ RIGHT_FORALL_IMP_THM : thm) :
    ExceptT String IO IterateKey2 := do
  let MESON (ths : List thm) (t : term) : ExceptT String IO thm := MESON' ths t
  let SET_RULE (t : term) : ExceptT String IO thm := SET_RULE' t
  let ASM_MESON_TAC := ASM MESON_TAC
  let { support, MONOIDAL_AC, IN_SUPPORT, SUPPORT_CLAUSES, SUPPORT_DELTA, .. } := G
  let { ITERATE_SUPPORT, ITERATE_EXPAND_CASES, ITERATE_CLAUSES, ITERATE_UNION,
        ITERATE_SING, .. } := K1

  let ITERATE_DELTA ← prove
   r"!op. monoidal op
        ==> !(f:A->B) a s.
                iterate op s (\x. if x = a then f(x) else neutral op) =
                if a IN s then f(a) else neutral op"
   (GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC [← GSYM ITERATE_SUPPORT] THEN
    REWRITE_TAC [SUPPORT_DELTA] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [ITERATE_CLAUSES] THEN REWRITE_TAC [SUPPORT_CLAUSES] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [ITERATE_CLAUSES, ITERATE_SING])

  let ITERATE_IMAGE ← prove
   r"!op. monoidal op
       ==> !f:A->B g:B->C s.
                (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
                ==> (iterate op (IMAGE f s) g = iterate op s (g o f))"
   (GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN
    SUBGOAL_THEN
     (← q r"!s. FINITE s /\
        (!x y:A. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
        ==> (iterate op (IMAGE f s) (g:B->C) = iterate op s (g o f))")
    ASSUME_TAC THENL
     [REWRITE_TAC [IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      ASM_SIMP_TAC [ITERATE_CLAUSES, IMAGE_CLAUSES, FINITE_IMAGE] THEN
      REWRITE_TAC [o_THM, IN_INSERT] THEN ASM_MESON_TAC [IN_IMAGE],
      GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC [ITERATE_EXPAND_CASES] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC (← TAUT
       (← q r"(a <=> a') /\ (a' ==> (b = b'))
        ==> (if a then b else c) = (if a' then b' else c)")) THEN
      REWRITE_TAC [SUPPORT_CLAUSES] THEN REPEAT STRIP_TAC THENL
       [MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN ASM_MESON_TAC [IN_SUPPORT],
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC [IN_SUPPORT]]])

  let ITERATE_BIJECTION ← prove
   r"!op. monoidal op
        ==>  !f:A->B p s.
                (!x. x IN s ==> p(x) IN s) /\
                (!y. y IN s ==> ?!x. x IN s /\ p(x) = y)
                ==> iterate op s f = iterate op s (f o p)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"iterate op (IMAGE (p:A->A) s) (f:A->B)") THEN CONJ_TAC THENL
     [AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_IMAGE],
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
        (← INST_TYPE [(aty, bty)] ITERATE_IMAGE))] THEN
    ASM_MESON_TAC [])

  -- The tactic's two SET_RULEs run (and print) right to left, as in OCaml.
  let ITERATE_ITERATE_PRODUCT ← prove
   r"!op. monoidal op
        ==> !s:A->bool t:A->B->bool x:A->B->C.
                FINITE s /\ (!i. i IN s ==> FINITE(t i))
                ==> iterate op s (\i. iterate op (t i) (x i)) =
                    iterate op {i,j | i IN s /\ j IN t i} (\(i,j). x i j)"
   (← do
    let r2 ← SET_RULE (← q r"{i,j | i IN a INSERT s /\ j IN t i} =
            IMAGE (\j. a,j) (t a) UNION {i,j | i IN s /\ j IN t i}")
    let r1 ← SET_RULE (← q r"{a,b | F} = {}")
    pure
     (GEN_TAC THEN DISCH_TAC THEN
      REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      ASM_SIMP_TAC [NOT_IN_EMPTY, r1, ITERATE_CLAUSES] THEN
      REWRITE_TAC [r2] THEN
      ASM_SIMP_TAC [FINITE_INSERT, ITERATE_CLAUSES, IN_INSERT] THEN
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM (fun th => tactic_of do pure (
       W (MP_TAC o PART_MATCH (lhand o rand) (← MATCH_MP ITERATE_UNION th) o
       rand o snd))) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC [FINITE_IMAGE, FINITE_PRODUCT_DEPENDENT, IN_INSERT] THEN
        REWRITE_TAC [DISJOINT, EXTENSION, IN_IMAGE, IN_INTER, NOT_IN_EMPTY,
                     IN_ELIM_THM, EXISTS_PAIR_THM, FORALL_PAIR_THM, PAIR_EQ] THEN
        ASM_MESON_TAC [],
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      FIRST_ASSUM (fun th => tactic_of do pure (
       W (MP_TAC o PART_MATCH (lhand o rand) (← MATCH_MP ITERATE_IMAGE th) o
       rand o snd))) THEN
      ANTS_TAC THENL
       [SIMP_TAC [FORALL_PAIR_THM] THEN CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
        ASM_SIMP_TAC [PAIR_EQ],
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [o_DEF] THEN
        CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC [ETA_AX]]))

  let ITERATE_EQ ← prove
   r"!op. monoidal op
        ==> !f:A->B g s.
              (!x. x IN s ==> f x = g x) ==> iterate op s f = iterate op s g"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [ITERATE_EXPAND_CASES] THEN
    SUBGOAL_THEN (← q r"support op g s = support op (f:A->B) s") SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_SUPPORT] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN
     (← q r"FINITE(support op (f:A->B) s) /\
      (!x. x IN (support op f s) ==> f x = g x)")
    MP_TAC THENL [ASM_MESON_TAC [IN_SUPPORT], REWRITE_TAC [IMP_CONJ]] THEN
    SPEC_TAC ((← q r"support op (f:A->B) s"), (← q r"t:A->bool")) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN ASM_SIMP_TAC [ITERATE_CLAUSES] THEN
    MESON_TAC [IN_INSERT])

  let ITERATE_RESTRICT_SET ← prove
   r"!op. monoidal op
        ==> !P s f:A->B. iterate op {x | x IN s /\ P x} f =
                         iterate op s (\x. if P x then f x else neutral op)"
   (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [← GSYM ITERATE_SUPPORT] THEN
    REWRITE_TAC [support, IN_ELIM_THM] THEN
    REWRITE_TAC [← MESON [] (← q r"~((if P x then f x else a) = a) <=> P x /\ ~(f x = a)"),
                 ← GSYM CONJ_ASSOC] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP ITERATE_EQ) THEN
    SIMP_TAC [IN_ELIM_THM])

  let ITERATE_EQ_GENERAL ← prove
   r"!op. monoidal op
        ==> !s:A->bool t:B->bool f:A->C g h.
                (!y. y IN t ==> ?!x. x IN s /\ h(x) = y) /\
                (!x. x IN s ==> h(x) IN t /\ g(h x) = f x)
                ==> iterate op s f = iterate op t g"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"t = IMAGE (h:A->B) s") SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"iterate op s ((g:B->C) o (h:A->B))") THEN CONJ_TAC THENL
     [ASM_MESON_TAC [ITERATE_EQ, o_THM],
      CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP ITERATE_IMAGE) THEN
      ASM_MESON_TAC []])

  let ITERATE_EQ_GENERAL_INVERSES ← prove
   r"!op. monoidal op
        ==> !s:A->bool t:B->bool f:A->C g h k.
                (!y. y IN t ==> k(y) IN s /\ h(k y) = y) /\
                (!x. x IN s ==> h(x) IN t /\ k(h x) = x /\ g(h x) = f x)
                ==> iterate op s f = iterate op t g"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP ITERATE_EQ_GENERAL) THEN
    EXISTS_TAC (← q r"h:A->B") THEN ASM_MESON_TAC [])

  let ITERATE_INJECTION ← prove
   r"!op. monoidal op
          ==> !f:A->B p:A->A s.
                      FINITE s /\
                      (!x. x IN s ==> p x IN s) /\
                      (!x y. x IN s /\ y IN s /\ p x = p y ==> x = y)
                      ==> iterate op s (f o p) = iterate op s f"
   (REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP ITERATE_BIJECTION) THEN
    MP_TAC (← ISPECL [← q r"s:A->bool", ← q r"p:A->A"] SURJECTIVE_IFF_INJECTIVE) THEN
    ASM_REWRITE_TAC [SUBSET, IN_IMAGE] THEN ASM_MESON_TAC [])

  let ITERATE_UNION_NONZERO ← prove
   r"!op. monoidal op
        ==> !f:A->B s t.
                FINITE(s) /\ FINITE(t) /\
                (!x. x IN (s INTER t) ==> f x = neutral(op))
                ==> iterate op (s UNION t) f =
                    op (iterate op s f) (iterate op t f)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM ITERATE_SUPPORT] THEN
    REWRITE_TAC [SUPPORT_CLAUSES] THEN
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP ITERATE_UNION) THEN
    ASM_SIMP_TAC [FINITE_SUPPORT, DISJOINT, IN_INTER, IN_SUPPORT, EXTENSION] THEN
    ASM_MESON_TAC [IN_INTER, NOT_IN_EMPTY])

  let ITERATE_OP ← prove
   r"!op. monoidal op
        ==> !(f:A->B) g s.
                FINITE s
                ==> iterate op s (\x. op (f x) (g x)) =
                    op (iterate op s f) (iterate op s g)"
   (GEN_TAC THEN DISCH_TAC THEN
    GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [ITERATE_CLAUSES, MONOIDAL_AC])

  return {
    ITERATE_DELTA, ITERATE_IMAGE, ITERATE_BIJECTION, ITERATE_ITERATE_PRODUCT,
    ITERATE_EQ, ITERATE_RESTRICT_SET, ITERATE_EQ_GENERAL,
    ITERATE_EQ_GENERAL_INVERSES, ITERATE_INJECTION, ITERATE_UNION_NONZERO,
    ITERATE_OP }

/-- The THIRD key-lemmas bundle, iterate.ml 713-887: the ten superset/swap/
    image/cases lemmas and the four numseg-recursion clauses closing the
    section - `ITERATE_SUPERSET`, `ITERATE_UNIV`, `ITERATE_SWAP`,
    `ITERATE_IMAGE_NONZERO`, `ITERATE_IMAGE_GEN`, `ITERATE_CASES`,
    `ITERATE_OP_GEN`, the three `ITERATE_CLAUSES_NUMSEG*`, `ITERATE_PAIR` and
    `ITERATE_REFLECT`. -/
structure IterateKey3 where
  /-- `ITERATE_SUPERSET` (iterate.ml 713): iterate is unchanged by enlarging
      the set with `neutral` points.  `ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT]
      THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[support; EXTENSION;
      IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET]`. -/
  ITERATE_SUPERSET : thm
  /-- `ITERATE_UNIV` (iterate.ml 723): iterate over any superset of the
      support equals iterate over `UNIV`.  `CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_SUPERSET) THEN ASM
      SET_TAC[]`. -/
  ITERATE_UNIV : thm
  /-- `ITERATE_SWAP` (iterate.ml 732): two nested iterates over finite sets
      commute.  `MATCH_MP_TAC FINITE_INDUCT_STRONG THEN ASM_SIMP_TAC
      [ITERATE_CLAUSES] THEN ASM_SIMP_TAC[ITERATE_EQ_NEUTRAL; GSYM
      ITERATE_OP]`. -/
  ITERATE_SWAP : thm
  /-- `ITERATE_IMAGE_NONZERO` (iterate.ml 744): reindexing along a map that
      collapses only on `neutral` values.  `MATCH_MP_TAC FINITE_INDUCT_STRONG`,
      `MAP_EVERY X_GEN_TAC [a; s]`, a `SUBGOAL_THEN .. SUBST1_TAC THENL
      [ASM_MESON_TAC[]; ALL_TAC]` (width 2), `COND_CASES_TAC`, another
      `SUBGOAL_THEN .. SUBST1_TAC` then `ASM_MESON_TAC[MONOIDAL_AC]`. -/
  ITERATE_IMAGE_NONZERO : thm
  /-- `ITERATE_IMAGE_GEN` (iterate.ml 763): iterate over `s` grouped by the
      fibres of `f`.  `MATCH_MP_TAC EQ_TRANS`, `CONJ_TAC THENL [b1; b2]`
      (width 2); `b1` uses `FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_EQ)`
      and a `SUBGOAL_THEN .. SUBST1_TAC THENL [ASM SET_TAC[]; ..]` (width 2);
      `b2` uses `ITERATE_RESTRICT_SET` and `W(MP_TAC o PART_MATCH (lhand o
      rand) (MATCH_MP ITERATE_SWAP th) o lhand o snd)`. -/
  ITERATE_IMAGE_GEN : thm
  /-- `ITERATE_CASES` (iterate.ml 783): iterate of a conditional splits into
      the two guarded sub-iterates.  `MATCH_MP_TAC EQ_TRANS`, `CONJ_TAC THENL
      [b1; b2]` (width 2); `b1` `FIRST_ASSUM(fun th -> ASM_SIMP_TAC[GSYM
      (MATCH_MP ITERATE_UNION th); FINITE_RESTRICT; SET_RULE ..])`; `b2`
      `BINOP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_EQ)`. -/
  ITERATE_CASES : thm
  /-- `ITERATE_OP_GEN` (iterate.ml 802): the support-based pointwise-`op`
      split.  `MATCH_MP_TAC EQ_TRANS`, `CONJ_TAC THENL [CONV_TAC SYM_CONV;
      ASM_SIMP_TAC[ITERATE_OP; FINITE_UNION] THEN BINOP_TAC]` (width 2), then
      `FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_SUPERSET)`. -/
  ITERATE_OP_GEN : thm
  /-- `ITERATE_CLAUSES_NUMSEG` (iterate.ml 819): the `m..0` / `m..SUC n`
      recursion.  `REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[..] THEN REWRITE_TAC[ARITH_RULE
      `~(SUC n <= n)`; NOT_IN_EMPTY] THEN ASM_MESON_TAC[monoidal]`. -/
  ITERATE_CLAUSES_NUMSEG : thm
  /-- `ITERATE_CLAUSES_NUMSEG_LT` (iterate.ml 831): the `{i | i < k}`
      recursion.  `SIMP_TAC[NUMSEG_CLAUSES_LT; ITERATE_CLAUSES;
      FINITE_NUMSEG_LT] THEN REWRITE_TAC[IN_ELIM_THM; LT_REFL; monoidal] THEN
      MESON_TAC[]`. -/
  ITERATE_CLAUSES_NUMSEG_LT : thm
  /-- `ITERATE_CLAUSES_NUMSEG_LE` (iterate.ml 839): the `{i | i <= k}`
      recursion.  `SIMP_TAC[NUMSEG_CLAUSES_LE; ITERATE_CLAUSES;
      FINITE_NUMSEG_LE; ITERATE_SING] THEN REWRITE_TAC[monoidal; IN_ELIM_THM;
      ARITH_RULE `~(SUC k <= k)`] THEN MESON_TAC[]`. -/
  ITERATE_CLAUSES_NUMSEG_LE : thm
  /-- `ITERATE_PAIR` (iterate.ml 849): pairing consecutive terms of a
      `2*m..2*n+1` iterate.  `INDUCT_TAC THEN CONV_TAC NUM_REDUCE_CONV THENL
      [b1; b2]` (width 2); `b1` uses `num_CONV \`1\``, `b2` several
      `ARITH_RULE` rewrites and `ASM_MESON_TAC[monoidal]`. -/
  ITERATE_PAIR : thm
  /-- `ITERATE_REFLECT` (iterate.ml 867): reflecting the index range `m..n` to
      `0..n-m`.  `REWRITE_TAC[GSYM NUMSEG_EMPTY]`, `COND_CASES_TAC THENL [b1;
      b2]` (width 2) where `b2` starts `RULE_ASSUM_TAC(REWRITE_RULE
      [NUMSEG_EMPTY; NOT_LT])`, a `FIRST_ASSUM(MP_TAC o ISPECL [..] o MATCH_MP
      (INST_TYPE [..] ITERATE_IMAGE))`, an `ANTS_TAC THENL [ARITH_TAC;
      DISCH_THEN(SUBST1_TAC o SYM)]` (width 2), and a final `UNWIND_THM2`/
      `ARITH_RULE` rewrite. -/
  ITERATE_REFLECT : thm
  deriving Inhabited

@[nospecialize]
def setupIterateKey3 [HolBase]
    (MESON_TAC : List thm → tactic)
    (SET_TAC : List thm → tactic)
    (SET_RULE' : term → IO (Except String thm))
    (ARITH_RULE' : term → IO (Except String thm))
    (ARITH_TAC : tactic)
    (ASM_ARITH_TAC : tactic)
    (INDUCT_TAC : tactic)
    (NUM_REDUCE_CONV : ioconv) (num_CONV' : term → IO (Except String thm))
    (G : IterateGeneric) (S : IterateSegments) (K1 : IterateKey1) (K2 : IterateKey2)
    (FINITE_INDUCT_STRONG FINITE_UNION FINITE_RESTRICT FINITE_EMPTY FINITE_IMAGE
     FINITE_NUMSEG_LT FINITE_NUMSEG_LE
     NUMSEG_CLAUSES_LT NUMSEG_CLAUSES_LE IMAGE_CLAUSES EQ_TRANS
     IN_ELIM_THM IN_IMAGE IN_INSERT IN_UNION NOT_IN_EMPTY EXTENSION SUBSET
     UNWIND_THM2 NOT_LT LT_REFL MULT_EQ_0 ARITH o_THM o_DEF
     IMP_CONJ RIGHT_FORALL_IMP_THM : thm) :
    ExceptT String IO IterateKey3 := do
  let SET_RULE (t : term) : ExceptT String IO thm := SET_RULE' t
  let ARITH_RULE (t : term) : ExceptT String IO thm := ARITH_RULE' t
  let num_CONV (t : term) : ExceptT String IO thm := num_CONV' t
  let ASM_MESON_TAC := ASM MESON_TAC
  let { monoidal, support, MONOIDAL_AC, .. } := G
  let { NUMSEG_CLAUSES, FINITE_NUMSEG, IN_NUMSEG, NUMSEG_EMPTY, .. } := S
  let { ITERATE_SUPPORT, ITERATE_CLAUSES, ITERATE_SING, ITERATE_EQ_NEUTRAL,
        ITERATE_UNION, .. } := K1
  let { ITERATE_IMAGE, ITERATE_EQ, ITERATE_RESTRICT_SET, ITERATE_OP, .. } := K2

  let ITERATE_SUPERSET ← prove
   r"!op. monoidal op
        ==> !f:A->B u v.
                u SUBSET v /\
                (!x. x IN v /\ ~(x IN u) ==> f(x) = neutral op)
                ==> iterate op v f = iterate op u f"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM ITERATE_SUPPORT] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [support, EXTENSION, IN_ELIM_THM] THEN ASM_MESON_TAC [SUBSET])

  let ITERATE_UNIV ← prove
   r"!op. monoidal op
        ==> !f:A->B s. support op f UNIV SUBSET s
                  ==> iterate op s f = iterate op UNIV f"
   (REWRITE_TAC [support, SUBSET, IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP ITERATE_SUPERSET) THEN
    ASM SET_TAC [])

  let ITERATE_SWAP ← prove
   r"!op. monoidal op
        ==> !f:A->B->C s t.
                FINITE s /\ FINITE t
                ==> iterate op s (\i. iterate op t (f i)) =
                    iterate op t (\j. iterate op s (\i. f i j))"
   (GEN_TAC THEN DISCH_TAC THEN
    GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [ITERATE_CLAUSES] THEN
    ASM_SIMP_TAC [ITERATE_EQ_NEUTRAL, ← GSYM ITERATE_OP])

  let ITERATE_IMAGE_NONZERO ← prove
   r"!op. monoidal op
        ==> !g:B->C f:A->B s.
                    FINITE s /\
                    (!x y. x IN s /\ y IN s /\ ~(x = y) /\ f x = f y
                           ==> g(f x) = neutral op)
                    ==> iterate op (IMAGE f s) g = iterate op s (g o f)"
   (GEN_TAC THEN DISCH_TAC THEN
    GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [IMAGE_CLAUSES, ITERATE_CLAUSES, FINITE_IMAGE] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:A", ← q r"s:A->bool"] THEN
    REWRITE_TAC [IN_INSERT] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"iterate op s ((g:B->C) o (f:A->B)) = iterate op (IMAGE f s) g")
    SUBST1_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    REWRITE_TAC [IN_IMAGE] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [o_THM] THEN
    SUBGOAL_THEN (← q r"(g:B->C) ((f:A->B) a) = neutral op") SUBST1_TAC THEN
    ASM_MESON_TAC [MONOIDAL_AC])

  let ITERATE_IMAGE_GEN ← prove
   r"!op. monoidal op
        ==> !f:A->B g:A->C s.
                FINITE s
                ==> iterate op s g =
                    iterate op (IMAGE f s)
                       (\y. iterate op {x | x IN s /\ f x = y} g)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     (← q r"iterate op s (\x:A. iterate op {y:B | y IN IMAGE f s /\ (f x = y)}
       (\y. (g:A->C) x))") THEN
    CONJ_TAC THENL
     [FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP ITERATE_EQ) THEN
      ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"{y | y IN IMAGE (f:A->B) s /\ f x = y} = {(f x)}")
      SUBST1_TAC THENL [ASM SET_TAC [], ASM_SIMP_TAC [ITERATE_SING]],
      ASM_SIMP_TAC [ITERATE_RESTRICT_SET] THEN
      FIRST_ASSUM (fun th => tactic_of do pure (W (MP_TAC o PART_MATCH (lhand o rand)
       (← MATCH_MP ITERATE_SWAP th) o lhand o snd))) THEN
      ASM_SIMP_TAC [FINITE_IMAGE]])

  let ITERATE_CASES ← prove
   r"!op. monoidal op
        ==> !s P f g:A->B.
                FINITE s
                ==> iterate op s (\x. if P x then f x else g x) =
                    op (iterate op {x | x IN s /\ P x} f)
                       (iterate op {x | x IN s /\ ~P x} g)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     (← q r"op (iterate op {x | x IN s /\ P x} (\x. if P x then f x else (g:A->B) x))
       (iterate op {x | x IN s /\ ~P x} (\x. if P x then f x else g x))") THEN
    CONJ_TAC THENL
     [FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [← GSYM (← MATCH_MP ITERATE_UNION th),
        FINITE_RESTRICT,
        ← SET_RULE (← q r"DISJOINT {x | x IN s /\ P x} {x | x IN s /\ ~P x}")])) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC [],
      BINOP_TAC THEN FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP ITERATE_EQ) THEN
      SIMP_TAC [IN_ELIM_THM]])

  let ITERATE_OP_GEN ← prove
   r"!op. monoidal op
        ==> !f g:A->B s.
                FINITE(support op f s) /\ FINITE(support op g s)
                ==> iterate op s (\x. op (f x) (g x)) =
                    op (iterate op s f) (iterate op s g)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM ITERATE_SUPPORT] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"iterate op (support op f s UNION support op g s)
                         (\x. op ((f:A->B) x) (g x))") THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV,
      ASM_SIMP_TAC [ITERATE_OP, FINITE_UNION] THEN BINOP_TAC] THEN
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP ITERATE_SUPERSET) THEN
    REWRITE_TAC [support, IN_ELIM_THM, SUBSET, IN_UNION] THEN
    ASM_MESON_TAC [monoidal])

  let ITERATE_CLAUSES_NUMSEG ← prove
   r"!op. monoidal op
        ==> (!m. iterate op (m..0) f = if m = 0 then f(0) else neutral op) /\
            (!m n. iterate op (m..SUC n) f :A =
                   if m <= SUC n then op (iterate op (m..n) f) (f(SUC n))
                   else iterate op (m..n) f)"
   (REWRITE_TAC [NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC [ITERATE_CLAUSES, FINITE_NUMSEG, IN_NUMSEG, FINITE_EMPTY] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"~(SUC n <= n)"), NOT_IN_EMPTY] THEN
    ASM_MESON_TAC [monoidal])

  let ITERATE_CLAUSES_NUMSEG_LT ← prove
   r"!op. monoidal op
        ==> iterate op {i | i < 0} f :A = neutral op /\
            (!k. iterate op {i | i < SUC k} f =
                 op (iterate op {i | i < k} f) (f k))"
   (SIMP_TAC [NUMSEG_CLAUSES_LT, ITERATE_CLAUSES, FINITE_NUMSEG_LT] THEN
    REWRITE_TAC [IN_ELIM_THM, LT_REFL, monoidal] THEN MESON_TAC [])

  let ITERATE_CLAUSES_NUMSEG_LE ← prove
   r"!op. monoidal op
        ==> iterate op {i | i <= 0} f :A = f 0 /\
            (!k. iterate op {i | i <= SUC k} f =
                 op (iterate op {i | i <= k} f) (f(SUC k)))"
   (SIMP_TAC [NUMSEG_CLAUSES_LE, ITERATE_CLAUSES,
              FINITE_NUMSEG_LE, ITERATE_SING] THEN
    REWRITE_TAC [monoidal, IN_ELIM_THM, ← ARITH_RULE (← q r"~(SUC k <= k)")] THEN
    MESON_TAC [])

  let ITERATE_PAIR ← prove
   r"!op. monoidal op
        ==> !f m n. iterate op (2*m..2*n+1) f :A =
                    iterate op (m..n) (\i. op (f(2*i)) (f(2*i+1)))"
   (GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN
    INDUCT_TAC THEN CONV_TAC NUM_REDUCE_CONV THENL
     [ASM_SIMP_TAC [← num_CONV (← q r"1"), ITERATE_CLAUSES_NUMSEG] THEN
      REWRITE_TAC [← ARITH_RULE (← q r"2 * m <= SUC 0 <=> m = 0")] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [MULT_EQ_0, ARITH],
      REWRITE_TAC [← ARITH_RULE (← q r"2 * SUC n + 1 = SUC(SUC(2 * n + 1))")] THEN
      ASM_SIMP_TAC [ITERATE_CLAUSES_NUMSEG] THEN
      REWRITE_TAC [← ARITH_RULE (← q r"2 * m <= SUC(SUC(2 * n + 1)) <=> m <= SUC n"),
                   ← ARITH_RULE (← q r"2 * m <= SUC(2 * n + 1) <=> m <= SUC n")] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [← ARITH_RULE (← q r"2 * SUC n = SUC(2 * n + 1)"),
                   ← ARITH_RULE (← q r"2 * SUC n + 1 = SUC(SUC(2 * n + 1))")] THEN
      ASM_MESON_TAC [monoidal]])

  let ITERATE_REFLECT ← prove
   r"!op:A->A->A.
        monoidal op
        ==> !x m n. iterate op (m..n) x =
                    if n < m then neutral op
                    else iterate op (0..n-m) (\i. x(n - i))"
   (REWRITE_TAC [← GSYM NUMSEG_EMPTY] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THENL
     [ASM_MESON_TAC [ITERATE_CLAUSES],
      RULE_ASSUM_TAC (REWRITE_RULE [NUMSEG_EMPTY, NOT_LT])] THEN
    FIRST_ASSUM (MP_TAC o
     ISPECL [← q r"\i:num. n - i", ← q r"x:num->A", ← q r"0..n-m"] o
     MATCH_MP (← INST_TYPE [(← qty r"X", ← qty r"A")] ITERATE_IMAGE)) THEN
    REWRITE_TAC [o_DEF, IN_NUMSEG] THEN
    ANTS_TAC THENL [ARITH_TAC, DISCH_THEN (SUBST1_TAC o SYM)] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, IN_IMAGE, IN_NUMSEG] THEN
    REWRITE_TAC [UNWIND_THM2, ← ARITH_RULE
      (← q r"x = n - y /\ 0 <= y /\ y <= n - m <=>
       y = n - x /\ x <= n /\ y <= n - m")] THEN
    ASM_ARITH_TAC)

  return {
    ITERATE_SUPERSET, ITERATE_UNIV, ITERATE_SWAP, ITERATE_IMAGE_NONZERO,
    ITERATE_IMAGE_GEN, ITERATE_CASES, ITERATE_OP_GEN, ITERATE_CLAUSES_NUMSEG,
    ITERATE_CLAUSES_NUMSEG_LT, ITERATE_CLAUSES_NUMSEG_LE, ITERATE_PAIR,
    ITERATE_REFLECT }

/- ---------------------------------------------------------------------- -/
/- A more general notion of iteration, using a specific order (<<=)       -/
/- and hence applying to non-commutative operations, as well as giving    -/
/- more refined notions of domain ("dom") and neutral element ("neut").   -/
/- Otherwise it tries to be stylistically similar to "iterate" above.     -/
/- ---------------------------------------------------------------------- -/

/-- The ordered/non-commutative generalisation `iterato` and its eleven
    lemmas (iterate.ml 896-1184).  `iterato dom neut op (<<=) k f` folds `op`
    over the points of `k` where `f` lands in `dom DIFF {neut}`, visiting them
    in the order fixed by `<<=`, so unlike `iterate` it makes sense for a
    NON-COMMUTATIVE `op`; `dom`/`neut` refine the notions of domain and neutral
    element.  This section "tries to be stylistically similar to iterate
    above" (iterate.ml 893), so where a lemma mirrors a `364-889` key lemma the
    name matches with `ITERATE` -> `ITERATO` (SUPPORT, EXPAND_CASES,
    CLAUSES_GEN, CLAUSES, EQ, INDUCT, CLOSED).  Under `prioritize_num`
    (iterate.ml 10) every bare numeral is `:num`.

    The `o`-composition ORDER matters here.  iterate.ml 896
    is `let iterato = (new_specification ["iterato"] o prove) (tm,tac)`.  `f o
    g` applies `g` FIRST, so `prove` runs FIRST (producing the existence
    theorem) and `new_specification ["iterato"] SECOND (introducing the
    constant).  Rendered below as an explicit TWO-STEP: prove the `?itty. ...`
    theorem, then feed it to the threaded `new_specification`.
    `new_specification` is a SIDE-EFFECTING kernel operation, so it is THREADED
    IN as a parameter from Session (exactly as `new_definition`), and must NOT
    live in HolMath.

    *** HAZARD (b): `<<=`. ***  Not declared in iterate.ml; it comes from
    `realax.ml:18 parse_as_infix("<<=",(12,"right"))` and is already registered
    in this development's bootstrap prefix.  Verified at runtime: `x <<= y`
    parses as a 2-argument right-infix application whose head is the RELATION
    VARIABLE `<<=` (`iterato` quantifies over an arbitrary order, so `<<=` is a
    bound variable, NOT a constant). -/
structure IterateOrdered where
  /-- `iterato` (iterate.ml 896): the constant introduced by
      `new_specification ["iterato"]` from the proved existence theorem.  Its
      defining property is the guarded well-founded recursion:
      `iterato dom neut op (<<=) k f = if FINITE{support} /\ ~empty then let
      i = (minimal-or-arbitrary support element) in op (f i) (iterato ... (k
      DELETE i) ...) else neut`. -/
  iterato : thm
  /-- `ITERATO_SUPPORT` (iterate.ml 933): restricting to the support set does
      not change the iteration (mirrors `ITERATE_SUPPORT`).  `ONCE_REWRITE_TAC
      [iterato]`, a `SET_RULE`, `COND_CASES_TAC THEN ... LET_TAC THEN
      CONV_TAC(ONCE_DEPTH_CONV let_CONV)`, `AP_TERM/AP_THM/AP_TERM`, `ASM
      SET_TAC[]`. -/
  ITERATO_SUPPORT : thm
  /-- `ITERATO_EXPAND_CASES` (iterate.ml 945): the finite/infinite case split
      (mirrors `ITERATE_EXPAND_CASES`).  `COND_CASES_TAC THENL [b1; b2]` width
      2; `b2` is `GEN_REWRITE_TAC LAND_CONV [iterato] THEN ASM_REWRITE_TAC[]`. -/
  ITERATO_EXPAND_CASES : thm
  /-- `ITERATO_CLAUSES_GEN` (iterate.ml 955): the empty/insert recursion under
      the general order hypotheses (mirrors `ITERATE_CLAUSES_GEN`).  `CONJ_TAC
      THENL [b1; b2]` (width 2), `ASM_CASES_TAC`, two `SET_RULE`s, a
      `COND_CASES_TAC THENL [c1; c2]` (width 2, `c1` uses `GEN_REWRITE_RULE I
      [IN_DIFF]`), `MATCH_MP_TAC(MESON[] ...)`, `REPEAT CONJ_TAC THENL [d1; d2;
      ALL_TAC]` (width 3), another `COND_CASES_TAC THENL [K ALL_TAC o check
      (is_exists o concl); ...]` (width 2), a `SUBGOAL_THEN .. SUBST1_TAC THENL
      [ALL_TAC; ..]` (width 2), `SELECT_UNIQUE`, `EQ_TAC .. SIMP_TAC[] THENL
      [ALL_TAC; ASM SET_TAC[]]` (width 2), final `ASM_CASES_TAC`. -/
  ITERATO_CLAUSES_GEN : thm
  /-- `ITERATO_CLAUSES` (iterate.ml 1004): the empty/insert recursion for a
      genuine strict order (mirrors `ITERATE_CLAUSES`).  `REPEAT STRIP_TAC THEN
      REWRITE_TAC[ITERATO_CLAUSES_GEN] THEN MATCH_MP_TAC(CONJUNCT2(SPEC_ALL
      ITERATO_CLAUSES_GEN)) THEN ASM_MESON_TAC[]`. -/
  ITERATO_CLAUSES : thm
  /-- `ITERATO_CLAUSES_EXISTS` (iterate.ml 1017): a nonempty support yields an
      element realising one recursion step.  `CONJ_TAC THENL [b1; b2]` (width
      2); the `GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV o RAND_CONV o LAND_CONV)
      [iterato]` chain (LAND runs first), `LET_TAC`, a `GEN_REWRITE_TAC
      (BINDER_CONV o funpow 4 RAND_CONV) [GSYM ITERATO_SUPPORT]` (funpow 4 =
      four RAND levels), `MATCH_MP_TAC o MATCH_MP (MESON[] ...)`, `COND_CASES_TAC
      THENL [DISCH_TAC; ASM SET_TAC[]]` (width 2), `SELECT_RULE`. -/
  ITERATO_CLAUSES_EXISTS : thm
  /-- `ITERATO_EQ` (iterate.ml 1039): pointwise-equal functions give equal
      iterations (mirrors `ITERATE_EQ`).  `ONCE_REWRITE_TAC
      [ITERATO_EXPAND_CASES]`, a `num_WF` induction on `CARD`, `ONCE_REWRITE_TAC
      [iterato]`, `LET_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV)`, `BINOP_TAC
      THENL [ASM_MESON_TAC[]; ALL_TAC]` (width 2), `CARD_PSUBSET`. -/
  ITERATO_EQ : thm
  /-- `ITERATO_INDUCT` (iterate.ml 1078): an induction principle over the
      iteration (mirrors `ITERATE_CLOSED`-style induction).  A `num_WF`
      induction, `ITERATO_CLAUSES_EXISTS`, `MATCH_MP_TAC(TAUT ..)`,
      `CARD_DELETE`, `CARD_EQ_0`. -/
  ITERATO_INDUCT : thm
  /-- `ITERATO_CLOSED` (iterate.ml 1119): a predicate closed under `neut` and
      `op` holds of the iteration (mirrors `ITERATE_CLOSED`).  `REPEAT STRIP_TAC
      THEN MATCH_MP_TAC ITERATO_INDUCT THEN ASM_SIMP_TAC[]`. -/
  ITERATO_CLOSED : thm
  /-- `ITERATO_ITERATE` (iterate.ml 1127): for a `monoidal op`, `iterato` over
      the full universe with `neutral op` collapses to the commutative
      `iterate op`.  A `num_WF` induction using both `ITERATE_CLAUSES` and
      `ITERATO_CLAUSES_EXISTS`, `ITERATO_SUPPORT`/`ITERATE_SUPPORT`. -/
  ITERATO_ITERATE : thm
  /-- `ITERATO_CLAUSES_NUMSEG_LEFT` (iterate.ml 1167): the left-recursion of
      `iterato` over a numeral segment `m..n` with the ORDINARY order `<=` (a
      real constant, not the `<<=` variable).  Uses `ITERATO_CLAUSES_GEN`,
      `NUMSEG_LREC`, `COND_CASES_TAC THENL [..; ..]` (width 2) and `ANTS_TAC
      THENL [..; ..]` (width 2). -/
  ITERATO_CLAUSES_NUMSEG_LEFT : thm
  deriving Inhabited

/-- OCaml builds each tactic right to left, so where one proof's tactic
    contains several rules that print (SET_RULE, MESON), they are bound
    first, last one first. -/
@[nospecialize]
def setupIterateOrdered [HolBase]
    (new_specification' : List String → thm → IO (Except String thm))
    (MESON' : List thm → term → IO (Except String thm))
    (MESON_TAC : List thm → tactic)
    (SET_TAC : List thm → tactic)
    (SET_RULE' : term → IO (Except String thm))
    (ARITH_RULE' : term → IO (Except String thm))
    (ARITH_TAC : tactic)
    (SELECT_RULE : thm → Except String thm)
    (let_CONV : ioconv)
    (LET_TAC : tactic)
    (G : IterateGeneric) (K1 : IterateKey1) (S : IterateSegments)
    (WF_REC WF_MEASURE MEASURE EXISTS_SWAP_FUN_THM SWAP_FORALL_THM SKOLEM_THM
     num_WF CARD_PSUBSET PSUBSET_ALT SELECT_UNIQUE MEMBER_NOT_EMPTY CONJ_ASSOC
     UNWIND_THM2 EMPTY_GSPEC NOT_IN_EMPTY IN_DIFF IN_SING IN_DELETE IN_ELIM_THM
     IN_INSERT IN_UNIV FINITE_SUBSET FINITE_INSERT FINITE_DELETE FINITE_RESTRICT
     CARD_DELETE CARD_EQ_0 COND_SWAP NOT_EXISTS_THM IMP_IMP RIGHT_IMP_FORALL_THM
     NOT_LE CONJ_SYM UNWIND_THM1 : thm) :
    ExceptT String IO IterateOrdered := do
  let new_specification (l : List String) (th : thm) : ExceptT String IO thm :=
    new_specification' l th
  let MESON (ths : List thm) (t : term) : ExceptT String IO thm := MESON' ths t
  let SET_RULE (t : term) : ExceptT String IO thm := SET_RULE' t
  let ARITH_RULE (t : term) : ExceptT String IO thm := ARITH_RULE' t
  let ASM_MESON_TAC := ASM MESON_TAC
  let { support, .. } := G
  let { ITERATE_EXPAND_CASES, ITERATE_SUPPORT, ITERATE_CLAUSES, .. } := K1
  let { NUMSEG_LREC, NUMSEG_EMPTY, FINITE_NUMSEG, IN_NUMSEG, .. } := S
  let { FUN_EQ_THM, NOT_IMP, COND_RAND, .. } := HolBase.C

  let iterato ← new_specification ["iterato"] (← prove
   r"?itty.
      !dom neut op (<<=) k (f:K->A).
         itty dom neut op (<<=) k f =
         if FINITE {i | i IN k /\ f i IN dom DIFF {neut}} /\
            ~({i | i IN k /\ f i IN dom DIFF {neut}} = {})
         then let i = if ?i. i IN k /\ f i IN dom DIFF {neut} /\
                             !j. j <<= i /\ j IN k /\ f j IN dom DIFF {neut}
                                 ==> j = i
                       then @i. i IN k /\ f i IN dom DIFF {neut} /\
                                !j. j <<= i /\ j IN k /\
                                    f j IN dom DIFF {neut}
                                    ==> j = i
                       else @i. i IN k /\ f i IN dom DIFF {neut} in
              op (f i) (itty dom neut op (<<=)
                          {j | j IN k DELETE i /\ f j IN dom DIFF {neut}} f)
         else neut"
   (← do
    let r2 ← SET_RULE (← q r"p /\ q /\ ~(p /\ ~r /\ q) <=> r /\ p /\ q")
    let r1 ← SET_RULE (← q r"{i | i IN k DIFF {a} /\ P i} = {i | i IN k /\ P i} DELETE a")
    pure
     (REPLICATE_TAC 4 (ONCE_REWRITE_TAC [← GSYM SKOLEM_THM]) THEN REPEAT GEN_TAC THEN
      GEN_REWRITE_TAC I [EXISTS_SWAP_FUN_THM] THEN REWRITE_TAC [] THEN
      GEN_REWRITE_TAC BINDER_CONV [SWAP_FORALL_THM] THEN
      ONCE_REWRITE_TAC [← GSYM SKOLEM_THM] THEN GEN_TAC THEN
      MATCH_MP_TAC (← MATCH_MP WF_REC (← ISPEC
       (← q r"\k. CARD {i | i IN k /\ (f:K->A) i IN dom DIFF {neut}}") WF_MEASURE)) THEN
      REWRITE_TAC [MEASURE] THEN REPEAT STRIP_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      LET_TAC THEN CONV_TAC (ONCE_DEPTH_CONV let_CONV) THEN
      AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC [r1] THEN
      MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [PSUBSET_ALT] THEN CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
      REWRITE_TAC [IN_ELIM_THM, IN_DELETE, ← GSYM CONJ_ASSOC] THEN
      REWRITE_TAC [r2] THEN
      REWRITE_TAC [UNWIND_THM2] THEN
      FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [← GSYM MEMBER_NOT_EMPTY] o CONJUNCT2) THEN
      REWRITE_TAC [IN_ELIM_THM, IN_DELETE] THEN ASM_MESON_TAC [])))

  let ITERATO_SUPPORT ← prove
   r"!dom neut op (<<=) k (f:K->A).
        iterato dom neut op (<<=) {i | i IN k /\ f i IN dom DIFF {neut}} f =
        iterato dom neut op (<<=) k f"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [iterato] THEN
    REWRITE_TAC [CONJ_ASSOC, ← SET_RULE (← q r"y IN {x | x IN s /\ P x} /\ P y <=>
                        y IN {x | x IN s /\ P x}")] THEN
    REWRITE_TAC [IN_ELIM_THM, ← GSYM CONJ_ASSOC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN LET_TAC THEN
    CONV_TAC (ONCE_DEPTH_CONV let_CONV) THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC [])

  let ITERATO_EXPAND_CASES ← prove
   r"!dom neut op (<<=) k (f:K->A).
        iterato dom neut op (<<=) k f =
        if FINITE {i | i IN k /\ f i IN dom DIFF {neut}}
        then iterato dom neut op (<<=) {i | i IN k /\ f i IN dom DIFF {neut}} f
        else neut"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THENL
     [REWRITE_TAC [ITERATO_SUPPORT],
      GEN_REWRITE_TAC LAND_CONV [iterato] THEN ASM_REWRITE_TAC []])

  let ITERATO_CLAUSES_GEN ← prove
   r"!dom neut op (<<=) (f:K->A).
        (iterato dom neut op (<<=) {} f = neut) /\
        (!i k. FINITE {j | j IN k /\ f j IN dom DIFF {neut}} /\
               (!j. j IN k ==> i = j \/ i <<= j \/ j <<= i) /\
               (!j. j <<= i /\ j IN k /\ f j IN dom DIFF {neut} ==> j = i)
               ==> iterato dom neut op (<<=) (i INSERT k) f =
                   if f i IN dom ==> f i = neut \/ i IN k
                   then iterato dom neut op (<<=) k f
                   else op (f i) (iterato dom neut op (<<=) k f))"
   (← do
    let r4 ← SET_RULE (← q r"~(i IN k) ==> (i INSERT k) DELETE i = k")
    let m3 ← MESON [] (← q r"q /\ p /\ x = z ==> (if p /\ q then x else y) = z")
    let r2 ← SET_RULE (← q r"x IN dom ==> x = a <=> ~(x IN dom DIFF {a})")
    let r1 ← SET_RULE (← q r"i IN k ==> i INSERT k = k")
    pure
     (REPEAT GEN_TAC THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [iterato] THEN
        ASM_REWRITE_TAC [NOT_IN_EMPTY, EMPTY_GSPEC],
        REPEAT GEN_TAC THEN STRIP_TAC] THEN
      ASM_CASES_TAC (← q r"(i:K) IN k") THEN
      ASM_SIMP_TAC [COND_SWAP, r1] THEN
      REWRITE_TAC [r2] THEN
      REWRITE_TAC [COND_SWAP] THEN COND_CASES_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [iterato] THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [IN_DIFF]) THEN
        REWRITE_TAC [IN_SING] THEN STRIP_TAC,
        ONCE_REWRITE_TAC [← GSYM ITERATO_SUPPORT] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC []] THEN
      MATCH_MP_TAC m3 THEN
      REPEAT CONJ_TAC THENL
       [ASM SET_TAC [],
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC (← q r"i INSERT {j | j IN k /\ (f:K->A) j IN dom DIFF {neut}}") THEN
        ASM_REWRITE_TAC [FINITE_INSERT] THEN ASM SET_TAC [],
        ALL_TAC] THEN
      COND_CASES_TAC THENL
       [FIRST_X_ASSUM ((K ALL_TAC : thm → tactic) o check (is_exists o concl)),
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"i:K") o REWRITE_RULE [NOT_EXISTS_THM]) THEN
        ASM SET_TAC []] THEN
      SUBGOAL_THEN
       (← q r"(@i'. i' IN i INSERT k /\
            (f:K->A) i' IN dom DIFF {neut} /\
            (!j. j <<= i' /\ j IN i INSERT k /\ f j IN dom DIFF {neut}
                 ==> j = i')) = i")
      SUBST1_TAC THENL
       [ALL_TAC,
        CONV_TAC (ONCE_DEPTH_CONV let_CONV) THEN
        ASM_SIMP_TAC [r4] THEN
        REWRITE_TAC [ITERATO_SUPPORT]] THEN
      MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC (← q r"j:K") THEN
      REWRITE_TAC [] THEN EQ_TAC THEN SIMP_TAC [] THENL [ALL_TAC, ASM SET_TAC []] THEN
      ASM_CASES_TAC (← q r"j:K = i") THEN ASM_REWRITE_TAC [IN_INSERT] THEN ASM SET_TAC []))

  let ITERATO_CLAUSES ← prove
   r"!dom neut op (<<=) (f:K->A).
        (iterato dom neut op (<<=) {} f = neut) /\
        (!i k. FINITE {i | i IN k /\ f i IN dom DIFF {neut}} /\
               (!j. j IN k ==> i <<= j /\ ~(j <<= i))
               ==> iterato dom neut op (<<=) (i INSERT k) f =
                   if f i IN dom ==> f i = neut \/ i IN k
                   then iterato dom neut op (<<=) k f
                   else op (f i) (iterato dom neut op (<<=) k f))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [ITERATO_CLAUSES_GEN] THEN
    MATCH_MP_TAC (← CONJUNCT2 (← SPEC_ALL ITERATO_CLAUSES_GEN)) THEN
    ASM_MESON_TAC [])

  let ITERATO_CLAUSES_EXISTS ← prove
   r"!dom neut op (<<=) (f:K->A).
        (iterato dom neut op (<<=) {} f = neut) /\
        (!k. FINITE {i | i IN k /\ f i IN dom DIFF {neut}} /\
             ~({i | i IN k /\ f i IN dom DIFF {neut}} = {})
             ==> ?i. i IN k /\ f i IN dom DIFF {neut} /\
                     iterato dom neut op (<<=) k f =
                     op (f i) (iterato dom neut op (<<=) (k DELETE i) f))"
   (REPEAT GEN_TAC THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [iterato] THEN
      ASM_REWRITE_TAC [NOT_IN_EMPTY, EMPTY_GSPEC],
      REPEAT GEN_TAC THEN STRIP_TAC] THEN
    GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV o RAND_CONV o LAND_CONV)
     [iterato] THEN
    ASM_REWRITE_TAC [] THEN LET_TAC THEN
    GEN_REWRITE_TAC (BINDER_CONV o funpow 4 RAND_CONV)
     [← GSYM ITERATO_SUPPORT] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← MESON []
     (← q r"t = i ==> (t = i ==> P i) ==> ?j. P j"))) THEN
    REWRITE_TAC [] THEN COND_CASES_TAC THENL [DISCH_TAC, ASM SET_TAC []] THEN
    FIRST_X_ASSUM (MP_TAC o SELECT_RULE) THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [])

  let ITERATO_EQ ← prove
   r"!dom neut op (<<=) k f (g:K->A).
        (!i. i IN k ==> f i = g i)
        ==> iterato dom neut op (<<=) k f = iterato dom neut op (<<=) k g"
   (← do
    let r2 ← SET_RULE (← q r"{j | j IN s DELETE i /\ P j} = {j | j IN s /\ P j} DELETE i")
    let m1 ← MESON []
      (← q r"(!n k. FINITE k /\ CARD k = n ==> P k) ==> (!k. FINITE k ==> P k)")
    pure
     (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [ITERATO_EXPAND_CASES] THEN
      ASM_SIMP_TAC [← TAUT (← q r"p /\ q <=> ~(p ==> ~q)")] THEN
      REWRITE_TAC [NOT_IMP] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN
       (← q r"!i. i IN {i | i IN k /\ (g:K->A) i IN dom DIFF {neut}} ==> f i = g i")
      MP_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      UNDISCH_TAC (← q r"FINITE {i | i IN k /\ (g:K->A) i IN dom DIFF {neut}}") THEN
      SPEC_TAC ((← q r"{i | i IN k /\ (g:K->A) i IN dom DIFF {neut}}"), (← q r"k:K->bool")) THEN
      POP_ASSUM_LIST (K ALL_TAC) THEN MATCH_MP_TAC m1 THEN
      REWRITE_TAC [IMP_IMP] THEN MATCH_MP_TAC num_WF THEN
      X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN X_GEN_TAC (← q r"k:K->bool") THEN
      STRIP_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE
       [IMP_IMP, RIGHT_IMP_FORALL_THM, ← GSYM CONJ_ASSOC]) THEN
      ASM_CASES_TAC (← q r"k:K->bool = {}") THEN
      ASM_REWRITE_TAC [ITERATO_CLAUSES_EXISTS] THEN ONCE_REWRITE_TAC [iterato] THEN
        SUBGOAL_THEN (← q r"!s i. i IN k /\ (f:K->A) i IN s <=> i IN k /\ g i IN s")
      ASSUME_TAC THENL [ASM_MESON_TAC [], ASM_REWRITE_TAC [CONJ_ASSOC]] THEN
      ASM_REWRITE_TAC [← GSYM CONJ_ASSOC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN LET_TAC THEN
      CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN (← q r"(i:K) IN k") ASSUME_TAC THENL
       [EXPAND_TAC "i" THEN
        RULE_ASSUM_TAC (REWRITE_RULE [← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM]) THEN
        FIRST_X_ASSUM (MP_TAC o CONJUNCT2) THEN MESON_TAC [],
        ALL_TAC] THEN
      BINOP_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      ASM_REWRITE_TAC [r2] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC [FINITE_DELETE, FINITE_RESTRICT, IN_DELETE, IN_ELIM_THM] THEN
      REWRITE_TAC [← ONCE_REWRITE_RULE [CONJ_SYM] UNWIND_THM1] THEN
      FIRST_X_ASSUM (fun th => tactic_of do pure (
        GEN_REWRITE_TAC RAND_CONV [← SYM th])) THEN
      MATCH_MP_TAC CARD_PSUBSET THEN ASM SET_TAC []))

  let ITERATO_INDUCT ← prove
   r"!dom neut op (<<=) k (f:K->A) P.
        P neut /\
        (!i x. i IN k /\ f i IN dom /\ ~(f i = neut) /\ P x ==> P (op (f i) x))
        ==> P(iterato dom neut op (<<=) k f)"
   (← do
    let m2 ← MESON []
      (← q r"(!n k. FINITE k /\ CARD k = n ==> P k) ==> (!k. FINITE k ==> P k)")
    let r1 ← SET_RULE (← q r"i IN k /\ f i IN s /\ ~(f i = z) /\ Q <=>
      i IN {j | j IN k /\ f j IN s DIFF {z}} /\ Q")
    pure
     (REPEAT GEN_TAC THEN REWRITE_TAC [r1] THEN
      ONCE_REWRITE_TAC [ITERATO_EXPAND_CASES] THEN
      ONCE_REWRITE_TAC [COND_RAND] THEN SIMP_TAC [] THEN
      REWRITE_TAC [← TAUT
       (← q r"(a /\ p ==> if q then r else T) <=> a ==> q ==> p ==> r")] THEN
      STRIP_TAC THEN
      SPEC_TAC ((← q r"{i | i IN k /\ (f:K->A) i IN dom DIFF {neut}}"), (← q r"k:K->bool")) THEN
      MATCH_MP_TAC m2 THEN
      REWRITE_TAC [IMP_IMP] THEN MATCH_MP_TAC num_WF THEN
      X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN
      X_GEN_TAC (← q r"k:K->bool") THEN STRIP_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE
       [IMP_IMP, RIGHT_IMP_FORALL_THM, ← GSYM CONJ_ASSOC]) THEN
      ASM_CASES_TAC (← q r"k:K->bool = {}") THEN
      ASM_REWRITE_TAC [ITERATO_CLAUSES_EXISTS] THEN
      MP_TAC (← ISPECL
       [← q r"dom:A->bool", ← q r"neut:A", ← q r"op:A->A->A", ← q r"(<<=):K->K->bool",
        ← q r"f:K->A"]
       ITERATO_CLAUSES_EXISTS) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"k:K->bool") o CONJUNCT2) THEN
      ASM_SIMP_TAC [FINITE_RESTRICT] THEN MATCH_MP_TAC (← TAUT
       (← q r"(p ==> r) /\ (q ==> r) ==> (~p ==> q) ==> r")) THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC [← GSYM ITERATO_SUPPORT] THEN SIMP_TAC [] THEN
        ASM_REWRITE_TAC [ITERATO_CLAUSES_EXISTS],
        DISCH_THEN (X_CHOOSE_THEN (← q r"i:K") MP_TAC)] THEN
      REWRITE_TAC [IN_DIFF, IN_SING] THEN STRIP_TAC THEN
      FIRST_X_ASSUM SUBST1_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC (← q r"n - 1") THEN
      ASM_SIMP_TAC [CARD_DELETE, FINITE_DELETE, IN_DELETE] THEN
      REWRITE_TAC [← ARITH_RULE (← q r"n - 1 < n <=> ~(n = 0)")] THEN
      ASM_MESON_TAC [CARD_EQ_0]))

  let ITERATO_CLOSED ← prove
   r"!dom neut op (<<=) k (f:K->A) P.
        P neut /\
        (!x y. P x /\ P y ==> P(op x y)) /\
        (!i. i IN k /\ f i IN dom /\ ~(f i = neut) ==> P(f i))
        ==> P(iterato dom neut op (<<=) k f)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC ITERATO_INDUCT THEN ASM_SIMP_TAC [])

  let ITERATO_ITERATE ← prove
   r"!(op:A->A->A) ((<<=):K->K->bool).
        monoidal op ==> iterato (:A) (neutral op) op (<<=) = iterate op"
   (← do
    let r3 ← SET_RULE (← q r"i IN k ==> i INSERT (k DELETE i) = k")
    let m2 ← MESON []
      (← q r"(!n k. FINITE k /\ CARD k = n ==> P k) ==> (!k. FINITE k ==> P k)")
    let m1 ← MESON []
      (← q r"(p ==> x = y) ==> (if p then x else z) = (if p then y else z)")
    pure
     (REPEAT STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"k:K->bool", ← q r"f:K->A"] THEN
      ONCE_REWRITE_TAC [ITERATE_EXPAND_CASES, ITERATO_EXPAND_CASES] THEN
      REWRITE_TAC [support, IN_UNIV, IN_DIFF, IN_SING] THEN MATCH_MP_TAC m1 THEN
      SPEC_TAC ((← q r"{i | i IN k /\ ~((f:K->A) i = neutral op)}"), (← q r"k:K->bool")) THEN
      MATCH_MP_TAC m2 THEN
      REWRITE_TAC [IMP_IMP] THEN MATCH_MP_TAC num_WF THEN
      X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN
      X_GEN_TAC (← q r"k:K->bool") THEN STRIP_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE
       [IMP_IMP, RIGHT_IMP_FORALL_THM, ← GSYM CONJ_ASSOC]) THEN
      ASM_CASES_TAC (← q r"k:K->bool = {}") THEN
      ASM_SIMP_TAC [ITERATE_CLAUSES, ITERATO_CLAUSES_EXISTS] THEN
      MP_TAC (← ISPECL
       [← q r"(:A)", ← q r"neutral op:A", ← q r"op:A->A->A", ← q r"(<<=):K->K->bool",
        ← q r"f:K->A"]
       ITERATO_CLAUSES_EXISTS) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"k:K->bool") o CONJUNCT2) THEN
      ASM_SIMP_TAC [FINITE_RESTRICT] THEN MATCH_MP_TAC (← TAUT
       (← q r"(p ==> r) /\ (q ==> r) ==> (~p ==> q) ==> r")) THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC [← GSYM ITERATO_SUPPORT, ← GSYM ITERATE_SUPPORT] THEN
        REWRITE_TAC [support, IN_UNIV, IN_DIFF, IN_SING] THEN
        ASM_SIMP_TAC [ITERATE_CLAUSES, ITERATO_CLAUSES_EXISTS],
        DISCH_THEN (X_CHOOSE_THEN (← q r"i:K") MP_TAC)] THEN
      REWRITE_TAC [IN_DIFF, IN_SING] THEN STRIP_TAC THEN
      FIRST_X_ASSUM SUBST1_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"n - 1", ← q r"k DELETE (i:K)"]) THEN
      REWRITE_TAC [← ARITH_RULE (← q r"n - 1 < n <=> ~(n = 0)")] THEN
      ASM_SIMP_TAC [FINITE_DELETE, CARD_DELETE] THEN
      ANTS_TAC THENL [ASM_MESON_TAC [CARD_EQ_0], DISCH_THEN SUBST1_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o ISPECL [← q r"f:K->A", ← q r"i:K", ← q r"k DELETE (i:K)"] o
        CONJUNCT2 o MATCH_MP ITERATE_CLAUSES) THEN
      ASM_REWRITE_TAC [FINITE_DELETE, IN_DELETE] THEN
      ASM_SIMP_TAC [r3]))

  let ITERATO_CLAUSES_NUMSEG_LEFT ← prove
   r"!dom neut op (f:num->A) m n.
       iterato dom neut op (<=) (m..n) f =
         if m <= n then
           if f m IN dom ==> f m = neut
           then iterato dom neut op (<=) (m+1..n) f
           else op (f m) (iterato dom neut op (<=) (m+1..n) f)
         else neut"
   (REPEAT GEN_TAC THEN MP_TAC (← ISPECL
       [← q r"dom:A->bool", ← q r"neut:A", ← q r"op:A->A->A",
        ← q r"(<=):num->num->bool", ← q r"f:num->A"] ITERATO_CLAUSES_GEN) THEN
    COND_CASES_TAC THENL
     [DISCH_THEN (fun th => tactic_of do pure (ASM_SIMP_TAC [← GSYM NUMSEG_LREC] THEN MP_TAC th)),
      DISCH_THEN (MP_TAC o CONJUNCT1) THEN
      ASM_MESON_TAC [NUMSEG_EMPTY, NOT_LE]] THEN
    DISCH_THEN (MP_TAC o SPECL [← q r"m:num", ← q r"m+1..n"] o CONJUNCT2) THEN
    ANTS_TAC THENL
     [SIMP_TAC [FINITE_RESTRICT, FINITE_NUMSEG, IN_NUMSEG] THEN ARITH_TAC,
      REWRITE_TAC [IN_NUMSEG, ← ARITH_RULE (← q r"~(m + 1 <= m)")]])

  return {
    iterato, ITERATO_SUPPORT, ITERATO_EXPAND_CASES, ITERATO_CLAUSES_GEN,
    ITERATO_CLAUSES, ITERATO_CLAUSES_EXISTS, ITERATO_EQ, ITERATO_INDUCT,
    ITERATO_CLOSED, ITERATO_ITERATE, ITERATO_CLAUSES_NUMSEG_LEFT }

/- ---------------------------------------------------------------------- -/
/- Four iterated operations where we just more or less express the basic  -/
/- definition and clausal form of the recursion, but don't develop any    -/
/- more lemmas; for products load "Library/products.ml" and for sums of   -/
/- intgers load "Library/isum.ml".                                        -/
/- ---------------------------------------------------------------------- -/

/-- The four specialisations of `iterate` (iterate.ml 1188-1282), where the
    OCaml "just more or less expresses the basic definition and clausal form
    of the recursion".  Each of `nproduct`/`iproduct`/`product`/`isum` is a
    `new_definition` folding a binary operation with `iterate`; each carries a
    `NEUTRAL_*` (its neutral element via `SELECT_UNIQUE`), a `MONOIDAL_*` (the
    monoid law via an arithmetic decision procedure) and a `*_CLAUSES` (the
    empty/insert recursion via `ITERATE_CLAUSES`).

    *** THE TYPE DISCIPLINE IS THE POINT. ***  This range is under
    `prioritize_num()` (iterate.ml 10), so a BARE numeral parses as `:num`.
    The four operations live at THREE DIFFERENT TYPES, and each takes its type
    NOT from any bare numeral but from the EXPLICIT type annotation on the
    folded operator, EXACTLY as the OCaml does:
      nproduct  over `:num`   -- `iterate (( * ):num->num->num)`
      iproduct  over `:int`   -- `iterate (( * ):int->int->int)`
      product   over `:real`  -- `iterate (( * ):real->real->real)`
      isum      over `:int`   -- `iterate ((+):int->int->int)`
    The `&1`/`&0` in the `:int` and `:real` neutral lemmas are `int_of_num`/
    `real_of_num` applications (`&`), so THEY too carry the type explicitly and
    do not depend on numeral priority.  `sum` over `:real` is NOT in this range
    - it arrives at iterate.ml 1984, after `prioritize_real()`.

    Threads `IK1.ITERATE_CLAUSES` (the generic recursion these instantiate),
    plus the neutral-uniqueness lemma `SELECT_UNIQUE`, `SWAP_FORALL_THM`, the
    arithmetic identities for each type (`MULT_CLAUSES`/`MULT_EQ_1` for num,
    `INT_MUL_L/RID`, `INT_ADD_L/RID`, `REAL_MUL_L/RID`) and the three decision
    tactics `ARITH_TAC`/`INT_ARITH_TAC`/`REAL_ARITH_TAC`. -/
structure IterateSpecial where
  /-- `nproduct` (iterate.ml 1194): `nproduct = iterate (( * ):num->num->num)`,
      the finite product over `:num`.  `new_definition`. -/
  nproduct : thm
  /-- `NEUTRAL_MUL` (iterate.ml 1197): `neutral(( * ):num->num->num) = 1`. -/
  NEUTRAL_MUL : thm
  /-- `MONOIDAL_MUL` (iterate.ml 1202): `monoidal(( * ):num->num->num)`. -/
  MONOIDAL_MUL : thm
  /-- `NPRODUCT_CLAUSES` (iterate.ml 1206): the empty/insert recursion for
      `nproduct` (neutral `1`, step `f(x) * ...`). -/
  NPRODUCT_CLAUSES : thm
  /-- `iproduct` (iterate.ml 1216): `iproduct = iterate (( * ):int->int->int)`,
      the finite product over `:int`.  `new_definition`. -/
  iproduct : thm
  /-- `NEUTRAL_INT_MUL` (iterate.ml 1219): `neutral(( * ):int->int->int) = &1`. -/
  NEUTRAL_INT_MUL : thm
  /-- `MONOIDAL_INT_MUL` (iterate.ml 1224): `monoidal(( * ):int->int->int)`. -/
  MONOIDAL_INT_MUL : thm
  /-- `IPRODUCT_CLAUSES` (iterate.ml 1228): the empty/insert recursion for
      `iproduct` (neutral `&1`, step `f(x) * ...`). -/
  IPRODUCT_CLAUSES : thm
  /-- `product` (iterate.ml 1238): `product = iterate (( * ):real->real->real)`,
      the finite product over `:real`.  `new_definition`. -/
  product : thm
  /-- `NEUTRAL_REAL_MUL` (iterate.ml 1241): `neutral(( * ):real->real->real) = &1`. -/
  NEUTRAL_REAL_MUL : thm
  /-- `MONOIDAL_REAL_MUL` (iterate.ml 1246): `monoidal(( * ):real->real->real)`. -/
  MONOIDAL_REAL_MUL : thm
  /-- `PRODUCT_CLAUSES` (iterate.ml 1250): the empty/insert recursion for
      `product` (neutral `&1`, step `f(x) * ...`). -/
  PRODUCT_CLAUSES : thm
  /-- `isum` (iterate.ml 1260): `isum = iterate ((+):int->int->int)`, the
      finite sum over `:int`.  `new_definition`. -/
  isum : thm
  /-- `NEUTRAL_INT_ADD` (iterate.ml 1263): `neutral((+):int->int->int) = &0`. -/
  NEUTRAL_INT_ADD : thm
  /-- `MONOIDAL_INT_ADD` (iterate.ml 1268): `monoidal((+):int->int->int)`. -/
  MONOIDAL_INT_ADD : thm
  /-- `ISUM_CLAUSES` (iterate.ml 1272): the empty/insert recursion for `isum`
      (neutral `&0`, step `f(x) + ...`). -/
  ISUM_CLAUSES : thm
  deriving Inhabited

@[nospecialize]
def setupIterateSpecial [HolBase]
    (new_definition' : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic)
    (ARITH_TAC INT_ARITH_TAC REAL_ARITH_TAC : tactic)
    (SELECT_UNIQUE SWAP_FORALL_THM MULT_CLAUSES MULT_EQ_1
     INT_MUL_LID INT_MUL_RID REAL_MUL_LID REAL_MUL_RID
     INT_ADD_LID INT_ADD_RID : thm)
    (IGen : IterateGeneric) (IK1 : IterateKey1) :
    ExceptT String IO IterateSpecial := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let { neutral, monoidal, .. } := IGen
  let { ITERATE_CLAUSES, .. } := IK1

  let nproduct ← new_definition
    r"nproduct:(A->bool)->(A->num)->num = iterate(( * ):num->num->num)"

  let NEUTRAL_MUL ← prove
   r"neutral(( * ):num->num->num) = 1"
   (REWRITE_TAC [neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    MESON_TAC [MULT_CLAUSES, MULT_EQ_1])

  let MONOIDAL_MUL ← prove
   r"monoidal(( * ):num->num->num)"
   (REWRITE_TAC [monoidal, NEUTRAL_MUL] THEN ARITH_TAC)

  let NPRODUCT_CLAUSES ← prove
   r"(!f:A->num. nproduct {} f = 1) /\
   (!x (f:B->num) s.
        FINITE(s)
        ==> (nproduct (x INSERT s) f =
             if x IN s then nproduct s f else f(x) * nproduct s f))"
   (REWRITE_TAC [nproduct, ← GSYM NEUTRAL_MUL] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC [MONOIDAL_MUL])

  let iproduct ← new_definition
    r"iproduct:(A->bool)->(A->int)->int = iterate (( * ):int->int->int)"

  let NEUTRAL_INT_MUL ← prove
   r"neutral(( * ):int->int->int) = &1"
   (REWRITE_TAC [neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    MESON_TAC [INT_MUL_LID, INT_MUL_RID])

  let MONOIDAL_INT_MUL ← prove
   r"monoidal(( * ):int->int->int)"
   (REWRITE_TAC [monoidal, NEUTRAL_INT_MUL] THEN INT_ARITH_TAC)

  let IPRODUCT_CLAUSES ← prove
   r"(!f:A->int. iproduct {} f = &1) /\
   (!x (f:B->int) s.
        FINITE(s)
        ==> (iproduct (x INSERT s) f =
             if x IN s then iproduct s f else f(x) * iproduct s f))"
   (REWRITE_TAC [iproduct, ← GSYM NEUTRAL_INT_MUL] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC [MONOIDAL_INT_MUL])

  let product ← new_definition
    r"product:(A->bool)->(A->real)->real = iterate (( * ):real->real->real)"

  let NEUTRAL_REAL_MUL ← prove
   r"neutral(( * ):real->real->real) = &1"
   (REWRITE_TAC [neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    MESON_TAC [REAL_MUL_LID, REAL_MUL_RID])

  let MONOIDAL_REAL_MUL ← prove
   r"monoidal(( * ):real->real->real)"
   (REWRITE_TAC [monoidal, NEUTRAL_REAL_MUL] THEN REAL_ARITH_TAC)

  let PRODUCT_CLAUSES ← prove
   r"(!f:A->real. product {} f = &1) /\
   (!x (f:B->real) s.
        FINITE(s)
        ==> (product (x INSERT s) f =
             if x IN s then product s f else f(x) * product s f))"
   (REWRITE_TAC [product, ← GSYM NEUTRAL_REAL_MUL] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC [MONOIDAL_REAL_MUL])

  let isum ← new_definition
   r"isum:(A->bool)->(A->int)->int = iterate((+):int->int->int)"

  let NEUTRAL_INT_ADD ← prove
   r"neutral((+):int->int->int) = &0"
   (REWRITE_TAC [neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    MESON_TAC [INT_ADD_LID, INT_ADD_RID])

  let MONOIDAL_INT_ADD ← prove
   r"monoidal((+):int->int->int)"
   (REWRITE_TAC [monoidal, NEUTRAL_INT_ADD] THEN INT_ARITH_TAC)

  let ISUM_CLAUSES ← prove
   r"(!f:A->int. isum {} f = &0) /\
   (!x (f:B->int) s.
        FINITE(s)
        ==> (isum (x INSERT s) f =
             if x IN s then isum s f else f(x) + isum s f))"
   (REWRITE_TAC [isum, ← GSYM NEUTRAL_INT_ADD] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC [MONOIDAL_INT_ADD])

  return {
    nproduct, NEUTRAL_MUL, MONOIDAL_MUL, NPRODUCT_CLAUSES, iproduct,
    NEUTRAL_INT_MUL, MONOIDAL_INT_MUL, IPRODUCT_CLAUSES, product,
    NEUTRAL_REAL_MUL, MONOIDAL_REAL_MUL, PRODUCT_CLAUSES, isum,
    NEUTRAL_INT_ADD, MONOIDAL_INT_ADD, ISUM_CLAUSES }

/- ---------------------------------------------------------------------- -/
/- Sums of natural numbers.                                               -/
/- (`prioritize_num()` at iterate.ml 1286 is run by Session.)             -/
/- ---------------------------------------------------------------------- -/

/-- The FIRST nsum bundle, iterate.ml 1288-1461: the `nsum` definition, the
    additive neutral/monoidal identities, and the twenty-five theorems from
    `NSUM_DEGENERATE` to `NSUM_SWAP` - the recursion clauses, union/difference/
    inclusion-exclusion, support-invariance, additivity, the ordering lemmas
    (`NSUM_LE`/`NSUM_LT`/...), `NSUM_CONST`, the positivity lemmas, and
    delta/singleton/swap. -/
structure IterateNsum1 where
  /-- `nsum` (iterate.ml 1288): `nsum = iterate ((+):num->num->num)`, the finite
      sum over `:num`.  `new_definition`; neutral `0`. -/
  nsum : thm
  /-- `NEUTRAL_ADD` (iterate.ml 1291): `neutral((+):num->num->num) = 0`. -/
  NEUTRAL_ADD : thm
  /-- `MONOIDAL_ADD` (iterate.ml 1296): `monoidal((+):num->num->num)`. -/
  MONOIDAL_ADD : thm
  /-- `NSUM_DEGENERATE` (iterate.ml 1300): infinite support gives `nsum = 0`. -/
  NSUM_DEGENERATE : thm
  /-- `NSUM_CLAUSES` (iterate.ml 1305): the empty/insert recursion clauses. -/
  NSUM_CLAUSES : thm
  /-- `NSUM_UNION` (iterate.ml 1315): sum over a disjoint union. -/
  NSUM_UNION : thm
  /-- `NSUM_DIFF` (iterate.ml 1321): sum over a set difference. -/
  NSUM_DIFF : thm
  /-- `NSUM_INCL_EXCL` (iterate.ml 1329): the inclusion-exclusion identity. -/
  NSUM_INCL_EXCL : thm
  /-- `NSUM_SUPPORT` (iterate.ml 1336): `nsum (support (+) f s) f = nsum s f`. -/
  NSUM_SUPPORT : thm
  /-- `NSUM_ADD` (iterate.ml 1340): additivity of the summand. -/
  NSUM_ADD : thm
  /-- `NSUM_ADD_GEN` (iterate.ml 1345): additivity under finite support. -/
  NSUM_ADD_GEN : thm
  /-- `NSUM_EQ_0` (iterate.ml 1352): a summand identically `0` gives `nsum = 0`. -/
  NSUM_EQ_0 : thm
  /-- `NSUM_0` (iterate.ml 1357): `nsum s (\n. 0) = 0`. -/
  NSUM_0 : thm
  /-- `NSUM_LMUL` (iterate.ml 1361): `nsum s (\x. c * f x) = c * nsum s f`. -/
  NSUM_LMUL : thm
  /-- `NSUM_RMUL` (iterate.ml 1374): `nsum s (\x. f x * c) = nsum s f * c`. -/
  NSUM_RMUL : thm
  /-- `NSUM_LE` (iterate.ml 1378): monotonicity in the summand. -/
  NSUM_LE : thm
  /-- `NSUM_LT` (iterate.ml 1386): strict monotonicity with a strict witness. -/
  NSUM_LT : thm
  /-- `NSUM_LT_ALL` (iterate.ml 1399): strict monotonicity, everywhere strict. -/
  NSUM_LT_ALL : thm
  /-- `NSUM_EQ` (iterate.ml 1405): extensional equality of the summand. -/
  NSUM_EQ : thm
  /-- `NSUM_CONST` (iterate.ml 1410): `nsum s (\n. c) = CARD s * c`. -/
  NSUM_CONST : thm
  /-- `NSUM_POS_BOUND` (iterate.ml 1416): a bound on the sum bounds each term. -/
  NSUM_POS_BOUND : thm
  /-- `NSUM_EQ_0_IFF` (iterate.ml 1424): `nsum s f = 0 <=> all terms 0`. -/
  NSUM_EQ_0_IFF : thm
  /-- `NSUM_POS_LT` (iterate.ml 1429): a positive term gives a positive sum. -/
  NSUM_POS_LT : thm
  /-- `NSUM_POS_LT_ALL` (iterate.ml 1435): all-positive terms give positive sum. -/
  NSUM_POS_LT_ALL : thm
  /-- `NSUM_DELETE` (iterate.ml 1441): `f a + nsum (s DELETE a) f = nsum s f`. -/
  NSUM_DELETE : thm
  /-- `NSUM_SING` (iterate.ml 1445): `nsum {x} f = f x`. -/
  NSUM_SING : thm
  /-- `NSUM_DELTA` (iterate.ml 1449): sum of a delta function. -/
  NSUM_DELTA : thm
  /-- `NSUM_SWAP` (iterate.ml 1454): exchange of two finite summations. -/
  NSUM_SWAP : thm
  deriving Inhabited

@[nospecialize]
def setupIterateNsum1 [HolBase]
    (new_definition' : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic)
    (SET_TAC : List thm → tactic)
    (ARITH_TAC : tactic)
    (ARITH_RULE' : term → IO (Except String thm))
    (IGen : IterateGeneric) (IK1 : IterateKey1) (IK2 : IterateKey2)
    (IK3 : IterateKey3)
    (SELECT_UNIQUE ADD_CLAUSES MULT_CLAUSES MULT_SYM MULT_EQ_0 LEFT_ADD_DISTRIB
     CARD_CLAUSES FINITE_RULES FINITE_INDUCT_STRONG NOT_IN_EMPTY IN_INSERT
     IN_DELETE FINITE_DELETE LE_REFL LE_ADD2 LTE_ADD2 LE_0
     SWAP_FORALL_THM ETA_AX MEMBER_NOT_EMPTY LT_IMP_LE REAL_LT_IMP_LE
     IMP_CONJ RIGHT_FORALL_IMP_THM : thm) :
    ExceptT String IO IterateNsum1 := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let ARITH_RULE (t : term) : ExceptT String IO thm := ARITH_RULE' t
  let ASM_MESON_TAC := ASM MESON_TAC
  let { neutral, monoidal, iterate, support, SUPPORT_SUPPORT, .. } := IGen
  let { ITERATE_CLAUSES, ITERATE_UNION, ITERATE_DIFF, ITERATE_INCL_EXCL,
        ITERATE_EQ_NEUTRAL, ITERATE_EXPAND_CASES, ITERATE_DELETE, .. } := IK1
  let { ITERATE_OP, ITERATE_EQ, ITERATE_DELTA, .. } := IK2
  let { ITERATE_OP_GEN, .. } := IK3

  let nsum ← new_definition
    r"nsum:(A->bool)->(A->num)->num = iterate (+)"

  let NEUTRAL_ADD ← prove
   r"neutral((+):num->num->num) = 0"
   (REWRITE_TAC [neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    MESON_TAC [ADD_CLAUSES])

  let MONOIDAL_ADD ← prove
   r"monoidal((+):num->num->num)"
   (REWRITE_TAC [monoidal, NEUTRAL_ADD] THEN ARITH_TAC)

  let NSUM_DEGENERATE ← prove
   r"!f s:A->bool. ~(FINITE {x | x IN s /\ ~(f x = 0)}) ==> nsum s f = 0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [nsum] THEN
    SIMP_TAC [iterate, support, NEUTRAL_ADD])

  let NSUM_CLAUSES ← prove
   r"(!f:A->num. nsum {} f = 0) /\
   (!x (f:B->num) s.
        FINITE(s)
        ==> (nsum (x INSERT s) f =
             if x IN s then nsum s f else f(x) + nsum s f))"
   (REWRITE_TAC [nsum, ← GSYM NEUTRAL_ADD] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC [MONOIDAL_ADD])

  let NSUM_UNION ← prove
   r"!f s t:A->bool.
        FINITE s /\ FINITE t /\ DISJOINT s t
        ==> nsum (s UNION t) f = nsum s f + nsum t f"
   (SIMP_TAC [nsum, ITERATE_UNION, MONOIDAL_ADD])

  let NSUM_DIFF ← prove
   r"!f s t:A->bool.
        FINITE s /\ t SUBSET s
        ==> nsum (s DIFF t) f = nsum s f - nsum t f"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← ARITH_RULE (← q r"(x + z = y:num) ==> (x = y - z)")) THEN
    ASM_SIMP_TAC [nsum, ITERATE_DIFF, MONOIDAL_ADD])

  let NSUM_INCL_EXCL ← prove
   r"!s t (f:A->num).
     FINITE s /\ FINITE t
     ==> nsum s f + nsum t f = nsum (s UNION t) f + nsum (s INTER t) f"
   (REWRITE_TAC [nsum, ← GSYM NEUTRAL_ADD] THEN
    MATCH_MP_TAC ITERATE_INCL_EXCL THEN REWRITE_TAC [MONOIDAL_ADD])

  let NSUM_SUPPORT ← prove
   r"!f s:A->bool. nsum (support (+) f s) f = nsum s f"
   (SIMP_TAC [nsum, iterate, SUPPORT_SUPPORT])

  let NSUM_ADD ← prove
   r"!f g s:A->bool.
        FINITE s ==> (nsum s (\x. f(x) + g(x)) = nsum s f + nsum s g)"
   (SIMP_TAC [nsum, ITERATE_OP, MONOIDAL_ADD])

  let NSUM_ADD_GEN ← prove
   r"!f g s:A->bool.
        FINITE {x | x IN s /\ ~(f x = 0)} /\ FINITE {x | x IN s /\ ~(g x = 0)}
        ==> nsum s (\x. f x + g x) = nsum s f + nsum s g"
   (REWRITE_TAC [← GSYM NEUTRAL_ADD, ← GSYM support, nsum] THEN
    MATCH_MP_TAC ITERATE_OP_GEN THEN ACCEPT_TAC MONOIDAL_ADD)

  let NSUM_EQ_0 ← prove
   r"!f s:A->bool. (!x. x IN s ==> f(x) = 0) ==> nsum s f = 0"
   (REWRITE_TAC [nsum, ← GSYM NEUTRAL_ADD] THEN
    SIMP_TAC [ITERATE_EQ_NEUTRAL, MONOIDAL_ADD])

  let NSUM_0 ← prove
   r"!s:A->bool. nsum s (\n. 0) = 0"
   (SIMP_TAC [NSUM_EQ_0])

  let NSUM_LMUL ← prove
   r"!f c s:A->bool. nsum s (\x. c * f(x)) = c * nsum s f"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"c = 0") THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, NSUM_0] THEN REWRITE_TAC [nsum] THEN
    ONCE_REWRITE_TAC [ITERATE_EXPAND_CASES] THEN
    SUBGOAL_THEN (← q r"support (+) (\x:A. c * f(x)) s = support (+) f s") SUBST1_TAC
    THENL [ASM_SIMP_TAC [support, MULT_EQ_0, NEUTRAL_ADD], ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC [NEUTRAL_ADD, MULT_CLAUSES] THEN
    UNDISCH_TAC (← q r"FINITE (support (+) f (s:A->bool))") THEN
    SPEC_TAC ((← q r"support (+) f (s:A->bool)"), (← q r"t:A->bool")) THEN
    REWRITE_TAC [← GSYM nsum] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [NSUM_CLAUSES, MULT_CLAUSES, LEFT_ADD_DISTRIB])

  let NSUM_RMUL ← prove
   r"!f c s:A->bool. nsum s (\x. f(x) * c) = nsum s f * c"
   (ONCE_REWRITE_TAC [MULT_SYM] THEN REWRITE_TAC [NSUM_LMUL])

  let NSUM_LE ← prove
   r"!f g s:A->bool.
        FINITE(s) /\ (!x. x IN s ==> f(x) <= g(x))
        ==> nsum s f <= nsum s g"
   (ONCE_REWRITE_TAC [IMP_CONJ] THEN
    GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [NSUM_CLAUSES, LE_REFL, LE_ADD2, IN_INSERT])

  let NSUM_LT ← prove
   r"!f g s:A->bool.
         FINITE(s) /\ (!x. x IN s ==> f(x) <= g(x)) /\
         (?x. x IN s /\ f(x) < g(x))
         ==> nsum s f < nsum s g"
   (REPEAT GEN_TAC THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"s = (a:A) INSERT (s DELETE a)") SUBST1_TAC THENL
     [UNDISCH_TAC (← q r"a:A IN s") THEN SET_TAC [], ALL_TAC] THEN
    ASM_SIMP_TAC [NSUM_CLAUSES, FINITE_DELETE, IN_DELETE] THEN
    ASM_SIMP_TAC [LTE_ADD2, NSUM_LE, IN_DELETE, FINITE_DELETE])

  let NSUM_LT_ALL ← prove
   r"!f g s:A->bool.
        FINITE s /\ ~(s = {}) /\ (!x. x IN s ==> f(x) < g(x))
        ==> nsum s f < nsum s g"
   (MESON_TAC [MEMBER_NOT_EMPTY, LT_IMP_LE, NSUM_LT])

  let NSUM_EQ ← prove
   r"!f g s:A->bool. (!x. x IN s ==> f x = g x) ==> nsum s f = nsum s g"
   (REWRITE_TAC [nsum] THEN
    MATCH_MP_TAC ITERATE_EQ THEN REWRITE_TAC [MONOIDAL_ADD])

  let NSUM_CONST ← prove
   r"!c s:A->bool. FINITE s ==> (nsum s (\n. c) = (CARD s) * c)"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [NSUM_CLAUSES, CARD_CLAUSES] THEN
    REPEAT STRIP_TAC THEN ARITH_TAC)

  let NSUM_POS_BOUND ← prove
   r"!f b s:A->bool. FINITE s /\ nsum s f <= b ==> !x:A. x IN s ==> f x <= b"
   (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [NSUM_CLAUSES, NOT_IN_EMPTY, IN_INSERT] THEN
    MESON_TAC [LE_0, ← ARITH_RULE
     (← q r"0 <= x /\ 0 <= y /\ x + y <= b ==> x <= b /\ y <= b")])

  let NSUM_EQ_0_IFF ← prove
   r"!s:A->bool. FINITE s ==> (nsum s f = 0 <=> !x. x IN s ==> f x = 0)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC [NSUM_EQ_0] THEN
    ASM_MESON_TAC [← ARITH_RULE (← q r"n = 0 <=> n <= 0"), NSUM_POS_BOUND])

  let NSUM_POS_LT ← prove
   r"!f s:A->bool.
        FINITE s /\ (?x. x IN s /\ 0 < f x)
        ==> 0 < nsum s f"
   (SIMP_TAC [← ARITH_RULE (← q r"0 < n <=> ~(n = 0)"), NSUM_EQ_0_IFF] THEN MESON_TAC [])

  let NSUM_POS_LT_ALL ← prove
   r"!s f:A->num.
     FINITE s /\ ~(s = {}) /\ (!i. i IN s ==> 0 < f i) ==> 0 < nsum s f"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC NSUM_POS_LT THEN
    ASM_MESON_TAC [MEMBER_NOT_EMPTY, REAL_LT_IMP_LE])

  let NSUM_DELETE ← prove
   r"!f s a:A. FINITE s /\ a IN s ==> f(a) + nsum(s DELETE a) f = nsum s f"
   (SIMP_TAC [nsum, ITERATE_DELETE, MONOIDAL_ADD])

  let NSUM_SING ← prove
   r"!f x:A. nsum {x} f = f(x)"
   (SIMP_TAC [NSUM_CLAUSES, FINITE_RULES, NOT_IN_EMPTY, ADD_CLAUSES])

  let NSUM_DELTA ← prove
   r"!s a. nsum s (\x. if x = a:A then b else 0) = if a IN s then b else 0"
   (REWRITE_TAC [nsum, ← GSYM NEUTRAL_ADD] THEN
    SIMP_TAC [ITERATE_DELTA, MONOIDAL_ADD])

  let NSUM_SWAP ← prove
   r"!f:A->B->num s t.
      FINITE(s) /\ FINITE(t)
      ==> (nsum s (\i. nsum t (f i)) = nsum t (\j. nsum s (\i. f i j)))"
   (GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [NSUM_CLAUSES, NSUM_0, NSUM_ADD, ETA_AX])

  return {
    nsum, NEUTRAL_ADD, MONOIDAL_ADD, NSUM_DEGENERATE, NSUM_CLAUSES, NSUM_UNION,
    NSUM_DIFF, NSUM_INCL_EXCL, NSUM_SUPPORT, NSUM_ADD, NSUM_ADD_GEN, NSUM_EQ_0,
    NSUM_0, NSUM_LMUL, NSUM_RMUL, NSUM_LE, NSUM_LT, NSUM_LT_ALL, NSUM_EQ,
    NSUM_CONST, NSUM_POS_BOUND, NSUM_EQ_0_IFF, NSUM_POS_LT, NSUM_POS_LT_ALL,
    NSUM_DELETE, NSUM_SING, NSUM_DELTA, NSUM_SWAP }

/-- The SECOND nsum bundle, iterate.ml 1462-1745: `NSUM_IMAGE` to `NSUM_CASES`
    - the image/superset/restriction lemmas, the counting lemmas
    (`NSUM_MULTICOUNT`/`NSUM_GROUP`/...), subset monotonicity, the
    bijection/injection/product transfer lemmas, and `NSUM_UNIONS_NONZERO`.
    This bundle carries ALL the section's heaviest structured proofs and nine
    of its twelve THENL sites. -/
structure IterateNsum2 where
  /-- `NSUM_IMAGE` (iterate.ml 1462): sum over an injective image. -/
  NSUM_IMAGE : thm
  /-- `NSUM_SUPERSET` (iterate.ml 1469): drop zero-valued extra points. -/
  NSUM_SUPERSET : thm
  /-- `NSUM_UNIV` (iterate.ml 1475): sum over the universe via the support. -/
  NSUM_UNIV : thm
  /-- `NSUM_UNION_RZERO` (iterate.ml 1480): union whose right excess is zero. -/
  NSUM_UNION_RZERO : thm
  /-- `NSUM_UNION_LZERO` (iterate.ml 1488): union whose left excess is zero. -/
  NSUM_UNION_LZERO : thm
  /-- `NSUM_RESTRICT` (iterate.ml 1494): restricting the summand to the set. -/
  NSUM_RESTRICT : thm
  /-- `NSUM_BOUND` (iterate.ml 1499): `nsum s f <= CARD s * b`. -/
  NSUM_BOUND : thm
  /-- `NSUM_BOUND_GEN` (iterate.ml 1504): bound via `b DIV CARD s`. -/
  NSUM_BOUND_GEN : thm
  /-- `NSUM_BOUND_LT` (iterate.ml 1512): strict bound with a strict witness. -/
  NSUM_BOUND_LT : thm
  /-- `NSUM_BOUND_LT_ALL` (iterate.ml 1520): strict bound, everywhere strict. -/
  NSUM_BOUND_LT_ALL : thm
  /-- `NSUM_BOUND_LT_GEN` (iterate.ml 1525): strict bound via `b DIV CARD s`. -/
  NSUM_BOUND_LT_GEN : thm
  /-- `NSUM_UNION_EQ` (iterate.ml 1534): a partition into `s`/`t` gives `u`. -/
  NSUM_UNION_EQ : thm
  /-- `NSUM_EQ_SUPERSET` (iterate.ml 1540): equal on `t`, zero on `s DIFF t`. -/
  NSUM_EQ_SUPERSET : thm
  /-- `NSUM_RESTRICT_SET` (iterate.ml 1548): sum over `{x | x IN s /\ P x}`. -/
  NSUM_RESTRICT_SET : thm
  /-- `NSUM_NSUM_RESTRICT` (iterate.ml 1553): swap of restricted double sums. -/
  NSUM_NSUM_RESTRICT : thm
  /-- `CARD_EQ_NSUM` (iterate.ml 1561): `CARD s = nsum s (\x. 1)`. -/
  CARD_EQ_NSUM : thm
  /-- `NSUM_MULTICOUNT_GEN` (iterate.ml 1565): a general counting identity. -/
  NSUM_MULTICOUNT_GEN : thm
  /-- `NSUM_MULTICOUNT` (iterate.ml 1582): the uniform-multiplicity count. -/
  NSUM_MULTICOUNT : thm
  /-- `NSUM_IMAGE_GEN` (iterate.ml 1592): fibre decomposition of a sum. -/
  NSUM_IMAGE_GEN : thm
  /-- `NSUM_GROUP` (iterate.ml 1600): grouping a sum by a function's value. -/
  NSUM_GROUP : thm
  /-- `NSUM_GROUP_RELATION` (iterate.ml 1610): grouping by a relation. -/
  NSUM_GROUP_RELATION : thm
  /-- `NSUM_SUBSET` (iterate.ml 1624): subset monotonicity via a zero excess. -/
  NSUM_SUBSET : thm
  /-- `NSUM_SUBSET_SIMPLE` (iterate.ml 1637): subset monotonicity, simple. -/
  NSUM_SUBSET_SIMPLE : thm
  /-- `NSUM_LE_GEN` (iterate.ml 1642): monotonicity under a finite support. -/
  NSUM_LE_GEN : thm
  /-- `NSUM_MUL_BOUND` (iterate.ml 1657): `nsum s (a*b) <= nsum s a * nsum s b`. -/
  NSUM_MUL_BOUND : thm
  /-- `NSUM_IMAGE_NONZERO` (iterate.ml 1668): image sum with zero collisions. -/
  NSUM_IMAGE_NONZERO : thm
  /-- `NSUM_BIJECTION` (iterate.ml 1676): sum invariance under a bijection. -/
  NSUM_BIJECTION : thm
  /-- `NSUM_NSUM_PRODUCT` (iterate.ml 1684): double sum as a product sum. -/
  NSUM_NSUM_PRODUCT : thm
  /-- `NSUM_EQ_GENERAL` (iterate.ml 1692): equality via a transfer function. -/
  NSUM_EQ_GENERAL : thm
  /-- `NSUM_EQ_GENERAL_INVERSES` (iterate.ml 1700): equality via inverses. -/
  NSUM_EQ_GENERAL_INVERSES : thm
  /-- `NSUM_INJECTION` (iterate.ml 1708): sum invariance under an injection. -/
  NSUM_INJECTION : thm
  /-- `NSUM_UNION_NONZERO` (iterate.ml 1717): union sum with zero overlap. -/
  NSUM_UNION_NONZERO : thm
  /-- `NSUM_UNIONS_NONZERO` (iterate.ml 1724): union of a family, zero overlap. -/
  NSUM_UNIONS_NONZERO : thm
  /-- `NSUM_CASES` (iterate.ml 1739): split a summand by a predicate. -/
  NSUM_CASES : thm
  deriving Inhabited

@[nospecialize]
def setupIterateNsum2 [HolBase]
    (MESON_TAC : List thm → tactic)
    (SET_TAC : List thm → tactic)
    (ARITH_TAC : tactic)
    (ARITH_RULE' : term → IO (Except String thm))
    (IGen : IterateGeneric) (IK2 : IterateKey2)
    (IK3 : IterateKey3) (N1 : IterateNsum1)
    (EQ_TRANS DISJOINT FINITE_INDUCT_STRONG MULT_CLAUSES MULT_AC
     LE_MULT_RCANCEL LE_MULT_LCANCEL LE_RDIV_EQ LE_REFL LE_TRANS LT_IMP_LE
     MEMBER_NOT_EMPTY
     CARD_EQ_0 SING_SUBSET IN_DIFF SUBSET_UNION LE LTE_TRANS
     FINITE_DIFF FINITE_INTER FINITE_RESTRICT FINITE_UNIONS FINITE_SUBSET
     UNION_COMM UNIONS_0 UNIONS_INSERT IN_UNION IN_INTER IN_UNIONS IN_INSERT
     IN_ELIM_THM FORALL_IN_IMAGE SUBSET IMP_CONJ CONJ_ASSOC : thm) :
    ExceptT String IO IterateNsum2 := do
  let ARITH_RULE (t : term) : ExceptT String IO thm := ARITH_RULE' t
  let SET_RULE (t : term) : ExceptT String IO thm :=
    HolCore.Tactics.prove HolBase.B t (SET_TAC [])
  let ASM_MESON_TAC := ASM MESON_TAC
  let { support, .. } := IGen
  let { ITERATE_IMAGE, ITERATE_RESTRICT_SET, ITERATE_EQ_GENERAL,
        ITERATE_EQ_GENERAL_INVERSES, ITERATE_INJECTION, ITERATE_UNION_NONZERO,
        ITERATE_BIJECTION, ITERATE_ITERATE_PRODUCT, .. } := IK2
  let { ITERATE_SUPERSET, ITERATE_UNIV, ITERATE_IMAGE_GEN, ITERATE_IMAGE_NONZERO,
        ITERATE_CASES, .. } := IK3
  let { nsum, NEUTRAL_ADD, MONOIDAL_ADD, NSUM_CLAUSES, NSUM_UNION, NSUM_SUPPORT,
        NSUM_EQ_0, NSUM_LMUL, NSUM_LE, NSUM_LT, NSUM_LT_ALL, NSUM_EQ, NSUM_CONST,
        NSUM_SING, NSUM_SWAP, .. } := N1

  let NSUM_IMAGE ← prove
   r"!(f:A->B) g s.
        (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
        ==> (nsum (IMAGE f s) g = nsum s (g o f))"
   (REWRITE_TAC [nsum, ← GSYM NEUTRAL_ADD] THEN
    MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC [MONOIDAL_ADD])

  let NSUM_SUPERSET ← prove
   r"!f:A->num u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = 0))
        ==> (nsum v f = nsum u f)"
   (SIMP_TAC [nsum, ← GSYM NEUTRAL_ADD, ITERATE_SUPERSET, MONOIDAL_ADD])

  let NSUM_UNIV ← prove
   r"!f:A->num s. support (+) f (:A) SUBSET s ==> nsum s f = nsum (:A) f"
   (REWRITE_TAC [nsum] THEN MATCH_MP_TAC ITERATE_UNIV THEN
    REWRITE_TAC [MONOIDAL_ADD])

  let NSUM_UNION_RZERO ← prove
   r"!f:A->num u v.
        FINITE u /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = 0))
        ==> nsum (u UNION v) f = nsum u f"
   (← do
    let lemma ← prove r"u UNION v = u UNION (v DIFF u)" (SET_TAC [])
    pure
     (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [lemma] THEN
      MATCH_MP_TAC NSUM_SUPERSET THEN ASM_MESON_TAC [IN_UNION, IN_DIFF, SUBSET]))

  let NSUM_UNION_LZERO ← prove
   r"!f:A->num u v.
        FINITE v /\ (!x. x IN u /\ ~(x IN v) ==> (f(x) = 0))
        ==> nsum (u UNION v) f = nsum v f"
   (MESON_TAC [NSUM_UNION_RZERO, UNION_COMM])

  let NSUM_RESTRICT ← prove
   r"!f s:A->bool.
        FINITE s ==> nsum s (\x. if x IN s then f(x) else 0) = nsum s f"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC [])

  let NSUM_BOUND ← prove
   r"!s f b. FINITE s /\ (!x:A. x IN s ==> f(x) <= b)
           ==> nsum s f <= (CARD s) * b"
   (SIMP_TAC [← GSYM NSUM_CONST, NSUM_LE])

  let NSUM_BOUND_GEN ← prove
   r"!s f b. FINITE s /\ ~(s = {}) /\ (!x:A. x IN s ==> f(x) <= b DIV (CARD s))
           ==> nsum s f <= b"
   (SIMP_TAC [IMP_CONJ, CARD_EQ_0, LE_RDIV_EQ] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"nsum s (\x. CARD(s:A->bool) * f x) <= CARD s * b") MP_TAC THENL
     [ASM_SIMP_TAC [NSUM_BOUND],
      ASM_SIMP_TAC [NSUM_LMUL, LE_MULT_LCANCEL, CARD_EQ_0]])

  let NSUM_BOUND_LT ← prove
   r"!s f b. FINITE s /\ (!x:A. x IN s ==> f x <= b) /\ (?x. x IN s /\ f x < b)
           ==> nsum s f < (CARD s) * b"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC (← q r"nsum s (\x:A. b)") THEN CONJ_TAC THENL
     [MATCH_MP_TAC NSUM_LT THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [],
      ASM_SIMP_TAC [NSUM_CONST, LE_REFL]])

  let NSUM_BOUND_LT_ALL ← prove
   r"!s f b. FINITE s /\ ~(s = {}) /\ (!x:A. x IN s ==> f(x) < b)
           ==> nsum s f < (CARD s) * b"
   (MESON_TAC [MEMBER_NOT_EMPTY, LT_IMP_LE, NSUM_BOUND_LT])

  let NSUM_BOUND_LT_GEN ← prove
   r"!s f b. FINITE s /\ ~(s = {}) /\ (!x:A. x IN s ==> f(x) < b DIV (CARD s))
           ==> nsum s f < b"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC (← q r"nsum (s:A->bool) (\a. f(a) + 1)") THEN CONJ_TAC THENL
     [MATCH_MP_TAC NSUM_LT_ALL THEN ASM_SIMP_TAC [] THEN ARITH_TAC,
      MATCH_MP_TAC NSUM_BOUND_GEN THEN
      ASM_REWRITE_TAC [← ARITH_RULE (← q r"a + 1 <= b <=> a < b")]])

  let NSUM_UNION_EQ ← prove
   r"!s t u:A->bool.
        FINITE u /\ (s INTER t = {}) /\ (s UNION t = u)
        ==> nsum s f + nsum t f = nsum u f"
   (MESON_TAC [NSUM_UNION, DISJOINT, FINITE_SUBSET, SUBSET_UNION])

  let NSUM_EQ_SUPERSET ← prove
   r"!f s t:A->bool.
        FINITE t /\ t SUBSET s /\
        (!x. x IN t ==> (f x = g x)) /\
        (!x. x IN s /\ ~(x IN t) ==> (f(x) = 0))
        ==> (nsum s f = nsum t g)"
   (MESON_TAC [NSUM_SUPERSET, NSUM_EQ])

  let NSUM_RESTRICT_SET ← prove
   r"!P s f. nsum {x:A | x IN s /\ P x} f = nsum s (\x. if P x then f(x) else 0)"
   (REWRITE_TAC [nsum, ← GSYM NEUTRAL_ADD] THEN
    MATCH_MP_TAC ITERATE_RESTRICT_SET THEN REWRITE_TAC [MONOIDAL_ADD])

  let NSUM_NSUM_RESTRICT ← prove
   r"!(R:A->B->bool) f s t.
        FINITE s /\ FINITE t
        ==> (nsum s (\x. nsum {y | y IN t /\ R x y} (\y. f x y)) =
             nsum t (\y. nsum {x | x IN s /\ R x y} (\x. f x y)))"
   (REPEAT GEN_TAC THEN SIMP_TAC [NSUM_RESTRICT_SET] THEN
    DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP NSUM_SWAP th])))

  let CARD_EQ_NSUM ← prove
   r"!s:A->bool. FINITE s ==> ((CARD s) = nsum s (\x. 1))"
   (SIMP_TAC [NSUM_CONST, MULT_CLAUSES])

  let NSUM_MULTICOUNT_GEN ← prove
   r"!R:A->B->bool s t k.
        FINITE s /\ FINITE t /\
        (!j. j IN t ==> (CARD {i | i IN s /\ R i j} = k(j)))
        ==> (nsum s (\i. (CARD {j | j IN t /\ R i j})) =
             nsum t (\i. (k i)))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [CONJ_ASSOC] THEN
    DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"nsum s (\i:A. nsum {j:B | j IN t /\ R i j} (\j. 1))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NSUM_EQ THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC [CARD_EQ_NSUM, FINITE_RESTRICT],
      FIRST_ASSUM (fun t => tactic_of do pure (
        ONCE_REWRITE_TAC [← MATCH_MP NSUM_NSUM_RESTRICT t])) THEN
      MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC [NSUM_CONST, FINITE_RESTRICT] THEN
      REWRITE_TAC [MULT_CLAUSES]])

  let NSUM_MULTICOUNT ← prove
   r"!R:A->B->bool s t k.
        FINITE s /\ FINITE t /\
        (!j. j IN t ==> (CARD {i | i IN s /\ R i j} = k))
        ==> (nsum s (\i. (CARD {j | j IN t /\ R i j})) = (k * CARD t))"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"nsum t (\i:B. k)") THEN CONJ_TAC THENL
     [MATCH_MP_TAC NSUM_MULTICOUNT_GEN THEN ASM_REWRITE_TAC [],
      ASM_SIMP_TAC [NSUM_CONST] THEN REWRITE_TAC [MULT_AC]])

  let NSUM_IMAGE_GEN ← prove
   r"!f:A->B g s.
        FINITE s
        ==> nsum s g =
            nsum (IMAGE f s) (\y. nsum {x | x IN s /\ f x = y} g)"
   (REWRITE_TAC [nsum] THEN MATCH_MP_TAC ITERATE_IMAGE_GEN THEN
    REWRITE_TAC [MONOIDAL_ADD])

  let NSUM_GROUP ← prove
   r"!f:A->B g s t.
        FINITE s /\ IMAGE f s SUBSET t
        ==> nsum t (\y. nsum {x | x IN s /\ f(x) = y} g) = nsum s g"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A->B", ← q r"g:A->num", ← q r"s:A->bool"] NSUM_IMAGE_GEN) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC NSUM_SUPERSET THEN ASM_REWRITE_TAC [] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NSUM_EQ_0 THEN ASM SET_TAC [])

  let NSUM_GROUP_RELATION ← prove
   r"!R:A->B->bool g s t.
         FINITE s /\
         (!x. x IN s ==> ?!y. y IN t /\ R x y)
         ==> nsum t (\y. nsum {x | x IN s /\ R x y} g) = nsum s g"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"\x:A. @y:B. y IN t /\ R x y", ← q r"g:A->num",
                      ← q r"s:A->bool", ← q r"t:B->bool"]
          NSUM_GROUP) THEN
    ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC NSUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC [])

  -- The two SET_RULEs run (and print) right to left, as in OCaml.
  let NSUM_SUBSET ← prove
   r"!u v f. FINITE u /\ FINITE v /\ (!x:A. x IN (u DIFF v) ==> f(x) = 0)
           ==> nsum u f <= nsum v f"
   (← do
    let r2 ← SET_RULE (← q r"(u INTER v) UNION (v DIFF u) = v")
    let r1 ← SET_RULE (← q r"(u INTER v) UNION (u DIFF v) = u")
    pure
     (REPEAT STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"f:A->num", ← q r"u INTER v :A->bool"] NSUM_UNION) THEN
      DISCH_THEN (fun th => tactic_of do pure (
        MP_TAC (← SPEC (← q r"v DIFF u :A->bool") th) THEN
        MP_TAC (← SPEC (← q r"u DIFF v :A->bool") th))) THEN
      REWRITE_TAC [r1, r2] THEN
      ASM_SIMP_TAC [FINITE_DIFF, FINITE_INTER] THEN
      REPEAT (ANTS_TAC THENL [SET_TAC [], DISCH_THEN SUBST1_TAC]) THEN
      ASM_SIMP_TAC [NSUM_EQ_0] THEN ARITH_TAC))

  let NSUM_SUBSET_SIMPLE ← prove
   r"!u v f:A->num. FINITE v /\ u SUBSET v ==> nsum u f <= nsum v f"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC NSUM_SUBSET THEN
    ASM_MESON_TAC [IN_DIFF, SUBSET, FINITE_SUBSET])

  let NSUM_LE_GEN ← prove
   r"!f g s. (!x:A. x IN s ==> f x <= g x) /\ FINITE {x | x IN s /\ ~(g x = 0)}
           ==> nsum s f <= nsum s g"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM NSUM_SUPPORT] THEN
    REWRITE_TAC [support, NEUTRAL_ADD] THEN
    TRANS_TAC LE_TRANS (← q r"nsum {x | x IN s /\ ~(g(x:A) = 0)} f") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NSUM_SUBSET THEN
      ASM_REWRITE_TAC [IN_ELIM_THM, IN_DIFF] THEN
      CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [LE]] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
        FINITE_SUBSET)) THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [LE],
      MATCH_MP_TAC NSUM_LE THEN ASM_SIMP_TAC [IN_ELIM_THM]])

  let NSUM_MUL_BOUND ← prove
   r"!a b s:A->bool.
        FINITE s
        ==> nsum s (\i. a i * b i) <= nsum s a * nsum s b"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM NSUM_LMUL] THEN
    MATCH_MP_TAC NSUM_LE THEN ASM_REWRITE_TAC [LE_MULT_RCANCEL] THEN
    X_GEN_TAC (← q r"i:A") THEN DISCH_TAC THEN DISJ1_TAC THEN
    ASM_SIMP_TAC [] THEN GEN_REWRITE_TAC LAND_CONV [← GSYM NSUM_SING] THEN
    MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN
    ASM_SIMP_TAC [SING_SUBSET, IN_DIFF])

  let NSUM_IMAGE_NONZERO ← prove
   r"!d:B->num i:A->B s.
    FINITE s /\
    (!x y. x IN s /\ y IN s /\ ~(x = y) /\ i x = i y ==> d(i x) = 0)
    ==> nsum (IMAGE i s) d = nsum s (d o i)"
   (REWRITE_TAC [← GSYM NEUTRAL_ADD, nsum] THEN
    MATCH_MP_TAC ITERATE_IMAGE_NONZERO THEN REWRITE_TAC [MONOIDAL_ADD])

  let NSUM_BIJECTION ← prove
   r"!f p s:A->bool.
        (!x. x IN s ==> p(x) IN s) /\
        (!y. y IN s ==> ?!x. x IN s /\ p(x) = y)
        ==> nsum s f = nsum s (f o p)"
   (REWRITE_TAC [nsum] THEN MATCH_MP_TAC ITERATE_BIJECTION THEN
    REWRITE_TAC [MONOIDAL_ADD])

  let NSUM_NSUM_PRODUCT ← prove
   r"!s:A->bool t:A->B->bool x.
        FINITE s /\ (!i. i IN s ==> FINITE(t i))
        ==> nsum s (\i. nsum (t i) (x i)) =
            nsum {i,j | i IN s /\ j IN t i} (\(i,j). x i j)"
   (REWRITE_TAC [nsum] THEN MATCH_MP_TAC ITERATE_ITERATE_PRODUCT THEN
    REWRITE_TAC [MONOIDAL_ADD])

  let NSUM_EQ_GENERAL ← prove
   r"!s:A->bool t:B->bool f g h.
        (!y. y IN t ==> ?!x. x IN s /\ h(x) = y) /\
        (!x. x IN s ==> h(x) IN t /\ g(h x) = f x)
        ==> nsum s f = nsum t g"
   (REWRITE_TAC [nsum] THEN MATCH_MP_TAC ITERATE_EQ_GENERAL THEN
    REWRITE_TAC [MONOIDAL_ADD])

  let NSUM_EQ_GENERAL_INVERSES ← prove
   r"!s:A->bool t:B->bool f g h k.
        (!y. y IN t ==> k(y) IN s /\ h(k y) = y) /\
        (!x. x IN s ==> h(x) IN t /\ k(h x) = x /\ g(h x) = f x)
        ==> nsum s f = nsum t g"
   (REWRITE_TAC [nsum] THEN MATCH_MP_TAC ITERATE_EQ_GENERAL_INVERSES THEN
    REWRITE_TAC [MONOIDAL_ADD])

  let NSUM_INJECTION ← prove
   r"!f p s:A->bool.
        FINITE s /\
        (!x. x IN s ==> p x IN s) /\
        (!x y. x IN s /\ y IN s /\ p x = p y ==> x = y)
        ==> nsum s (f o p) = nsum s f"
   (REWRITE_TAC [nsum] THEN MATCH_MP_TAC ITERATE_INJECTION THEN
    REWRITE_TAC [MONOIDAL_ADD])

  let NSUM_UNION_NONZERO ← prove
   r"!f s t:A->bool.
        FINITE s /\ FINITE t /\ (!x. x IN s INTER t ==> f(x) = 0)
        ==> nsum (s UNION t) f = nsum s f + nsum t f"
   (REWRITE_TAC [nsum, ← GSYM NEUTRAL_ADD] THEN
    MATCH_MP_TAC ITERATE_UNION_NONZERO THEN REWRITE_TAC [MONOIDAL_ADD])

  let NSUM_UNIONS_NONZERO ← prove
   r"!f s. FINITE s /\ (!t:A->bool. t IN s ==> FINITE t) /\
         (!t1 t2 x. t1 IN s /\ t2 IN s /\ ~(t1 = t2) /\ x IN t1 /\ x IN t2
                    ==> f x = 0)
         ==> nsum (UNIONS s) f = nsum s (\t. nsum t f)"
   (GEN_TAC THEN ONCE_REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [UNIONS_0, UNIONS_INSERT, NSUM_CLAUSES, IN_INSERT] THEN
    MAP_EVERY X_GEN_TAC [← q r"t:A->bool", ← q r"s:(A->bool)->bool"] THEN
    DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
    ONCE_REWRITE_TAC [IMP_CONJ] THEN ASM_SIMP_TAC [NSUM_CLAUSES] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN (SUBST_ALL_TAC o SYM)] THEN
    STRIP_TAC THEN MATCH_MP_TAC NSUM_UNION_NONZERO THEN
    ASM_SIMP_TAC [FINITE_UNIONS, IN_INTER, IN_UNIONS] THEN ASM_MESON_TAC [])

  let NSUM_CASES ← prove
   r"!s P f g. FINITE s
             ==> nsum s (\x:A. if P x then f x else g x) =
                 nsum {x | x IN s /\ P x} f + nsum {x | x IN s /\ ~P x} g"
   (REWRITE_TAC [nsum, ← GSYM NEUTRAL_ADD] THEN
    MATCH_MP_TAC ITERATE_CASES THEN REWRITE_TAC [MONOIDAL_ADD])

  return {
    NSUM_IMAGE, NSUM_SUPERSET, NSUM_UNIV, NSUM_UNION_RZERO, NSUM_UNION_LZERO,
    NSUM_RESTRICT, NSUM_BOUND, NSUM_BOUND_GEN, NSUM_BOUND_LT,
    NSUM_BOUND_LT_ALL, NSUM_BOUND_LT_GEN, NSUM_UNION_EQ, NSUM_EQ_SUPERSET,
    NSUM_RESTRICT_SET, NSUM_NSUM_RESTRICT, CARD_EQ_NSUM, NSUM_MULTICOUNT_GEN,
    NSUM_MULTICOUNT, NSUM_IMAGE_GEN, NSUM_GROUP, NSUM_GROUP_RELATION,
    NSUM_SUBSET, NSUM_SUBSET_SIMPLE, NSUM_LE_GEN, NSUM_MUL_BOUND,
    NSUM_IMAGE_NONZERO, NSUM_BIJECTION, NSUM_NSUM_PRODUCT, NSUM_EQ_GENERAL,
    NSUM_EQ_GENERAL_INVERSES, NSUM_INJECTION, NSUM_UNION_NONZERO,
    NSUM_UNIONS_NONZERO, NSUM_CASES }

/-- The THIRD nsum bundle, iterate.ml 1746-1917: the closure/relation
    induction principles (`NSUM_CLOSED`/`NSUM_RELATED` and their nonempty
    variants), the numeral-segment theorems (`NSUM_*_NUMSEG`, the numseg
    recursion clauses, offset/split/reflect/pair), the modular-arithmetic
    lemmas (`MOD_NSUM_MOD`), the congruence `CONG_NSUM`, and the final
    `extend_basic_congs` registration of the three nsum congruence rules. -/
structure IterateNsum3 where
  /-- `NSUM_CLOSED` (iterate.ml 1746): a closed predicate is preserved. -/
  NSUM_CLOSED : thm
  /-- `NSUM_RELATED` (iterate.ml 1754): a compatible relation lifts to sums. -/
  NSUM_RELATED : thm
  /-- `NSUM_CLOSED_NONEMPTY` (iterate.ml 1766): closure, nonempty variant. -/
  NSUM_CLOSED_NONEMPTY : thm
  /-- `NSUM_RELATED_NONEMPTY` (iterate.ml 1776): relation, nonempty variant. -/
  NSUM_RELATED_NONEMPTY : thm
  /-- `NSUM_ADD_NUMSEG` (iterate.ml 1787): additivity over `m..n`. -/
  NSUM_ADD_NUMSEG : thm
  /-- `NSUM_LE_NUMSEG` (iterate.ml 1791): monotonicity over `m..n`. -/
  NSUM_LE_NUMSEG : thm
  /-- `NSUM_EQ_NUMSEG` (iterate.ml 1796): extensional equality over `m..n`. -/
  NSUM_EQ_NUMSEG : thm
  /-- `NSUM_CONST_NUMSEG` (iterate.ml 1801): `nsum(m..n)(\n. c) = (n+1-m)*c`. -/
  NSUM_CONST_NUMSEG : thm
  /-- `NSUM_EQ_0_NUMSEG` (iterate.ml 1805): zero summand over `m..n`. -/
  NSUM_EQ_0_NUMSEG : thm
  /-- `NSUM_EQ_0_IFF_NUMSEG` (iterate.ml 1809): `nsum(m..n) f = 0 <=> ...`. -/
  NSUM_EQ_0_IFF_NUMSEG : thm
  /-- `NSUM_TRIV_NUMSEG` (iterate.ml 1813): `n < m ==> nsum(m..n) f = 0`. -/
  NSUM_TRIV_NUMSEG : thm
  /-- `NSUM_SING_NUMSEG` (iterate.ml 1817): `nsum(n..n) f = f n`. -/
  NSUM_SING_NUMSEG : thm
  /-- `NSUM_CLAUSES_NUMSEG` (iterate.ml 1821): the `m..0`/`m..SUC n` clauses. -/
  NSUM_CLAUSES_NUMSEG : thm
  /-- `NSUM_CLAUSES_NUMSEG_LT` (iterate.ml 1828): the `{i | i < k}` clauses. -/
  NSUM_CLAUSES_NUMSEG_LT : thm
  /-- `NSUM_CLAUSES_NUMSEG_LE` (iterate.ml 1834): the `{i | i <= k}` clauses. -/
  NSUM_CLAUSES_NUMSEG_LE : thm
  /-- `NSUM_SWAP_NUMSEG` (iterate.ml 1840): exchange of two segment sums. -/
  NSUM_SWAP_NUMSEG : thm
  /-- `NSUM_ADD_SPLIT` (iterate.ml 1846): split `m..(n+p)` at `n`. -/
  NSUM_ADD_SPLIT : thm
  /-- `NSUM_OFFSET` (iterate.ml 1852): `nsum(m+p..n+p) f = nsum(m..n)(f(.+p))`. -/
  NSUM_OFFSET : thm
  /-- `NSUM_OFFSET_0` (iterate.ml 1857): offset to a zero-based segment. -/
  NSUM_OFFSET_0 : thm
  /-- `NSUM_CLAUSES_LEFT` (iterate.ml 1861): peel the left endpoint. -/
  NSUM_CLAUSES_LEFT : thm
  /-- `NSUM_CLAUSES_RIGHT` (iterate.ml 1866): peel the right endpoint. -/
  NSUM_CLAUSES_RIGHT : thm
  /-- `NSUM_PAIR` (iterate.ml 1871): pair adjacent terms `2i`,`2i+1`. -/
  NSUM_PAIR : thm
  /-- `NSUM_REFLECT` (iterate.ml 1876): reflect the summation index. -/
  NSUM_REFLECT : thm
  /-- `MOD_NSUM_MOD` (iterate.ml 1882): push a sum under `MOD n`. -/
  MOD_NSUM_MOD : thm
  /-- `MOD_NSUM_MOD_NUMSEG` (iterate.ml 1892): the `m..n` variant. -/
  MOD_NSUM_MOD_NUMSEG : thm
  /-- `CONG_NSUM` (iterate.ml 1897): congruence `(mod n)` of two sums. -/
  CONG_NSUM : thm
  /-- `NSUM_CONG` (iterate.ml 1907): the three-way congruence theorem whose
      `SPEC_ALL`'d conjuncts are registered with `extend_basic_congs`. -/
  NSUM_CONG : thm
  deriving Inhabited

@[nospecialize]
def setupIterateNsum3 [HolBase]
    (MESON_TAC : List thm → tactic)
    (INDUCT_TAC : tactic)
    (ARITH_TAC : tactic)
    (ARITH_RULE' : term → IO (Except String thm))
    (extend_basic_congs : List thm → IO Unit)
    (NUMBER_RULE : ioconv)
    (IK1 : IterateKey1) (IK3 : IterateKey3)
    (ISeg : IterateSegments) (N1 : IterateNsum1) (N2 : IterateNsum2)
    (FINITE_INDUCT_STRONG FINITE_NUMSEG NUMSEG_SING ETA_AX MOD_ZERO
     MOD_ADD_MOD MOD_MOD_REFL SUC_SUB1 SUB_ADD ADD_CLAUSES LT_REFL NOT_LT
     LE_TRANS EQ_ADD_RCANCEL o_DEF IN_NUMSEG IN_ELIM_THM
     IMP_CONJ RIGHT_FORALL_IMP_THM : thm) :
    ExceptT String IO IterateNsum3 := do
  let ARITH_RULE (t : term) : ExceptT String IO thm := ARITH_RULE' t
  let ASM_MESON_TAC := ASM MESON_TAC
  let { ITERATE_CLOSED, ITERATE_RELATED, ITERATE_CLOSED_NONEMPTY,
        ITERATE_RELATED_NONEMPTY, .. } := IK1
  let { ITERATE_CLAUSES_NUMSEG, ITERATE_CLAUSES_NUMSEG_LT, ITERATE_CLAUSES_NUMSEG_LE,
        ITERATE_PAIR, ITERATE_REFLECT, .. } := IK3
  let { CARD_NUMSEG, NUMSEG_ADD_SPLIT, DISJOINT_NUMSEG, NUMSEG_OFFSET_IMAGE,
        NUMSEG_LREC, .. } := ISeg
  let { nsum, NEUTRAL_ADD, MONOIDAL_ADD, NSUM_CLAUSES, NSUM_ADD, NSUM_EQ,
        NSUM_EQ_0, NSUM_LE, NSUM_CONST, NSUM_SING, NSUM_UNION, NSUM_EQ_0_IFF,
        NSUM_SWAP, .. } := N1
  let { NSUM_IMAGE, .. } := N2

  let NSUM_CLOSED ← prove
   r"!P f:A->num s.
        P(0) /\ (!x y. P x /\ P y ==> P(x + y)) /\ (!a. a IN s ==> P(f a))
        ==> P(nsum s f)"
   (REPEAT STRIP_TAC THEN MP_TAC (← MATCH_MP ITERATE_CLOSED MONOIDAL_ADD) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"P:num->bool")) THEN
    ASM_SIMP_TAC [NEUTRAL_ADD, ← GSYM nsum])

  let NSUM_RELATED ← prove
   r"!R (f:A->num) g s.
        R 0 0 /\
        (!m n m' n'. R m n /\ R m' n' ==> R (m + m') (n + n')) /\
        FINITE s /\ (!x. x IN s ==> R (f x) (g x))
        ==> R (nsum s f) (nsum s g)"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN REPEAT DISCH_TAC THEN
    MP_TAC (← ISPEC (← q r"R:num->num->bool")
      (← MATCH_MP ITERATE_RELATED MONOIDAL_ADD)) THEN
    ASM_REWRITE_TAC [← GSYM nsum, NEUTRAL_ADD] THEN ASM_MESON_TAC [])

  let NSUM_CLOSED_NONEMPTY ← prove
   r"!P f:A->num s.
        FINITE s /\ ~(s = {}) /\
        (!x y. P x /\ P y ==> P(x + y)) /\ (!a. a IN s ==> P(f a))
        ==> P(nsum s f)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← MATCH_MP ITERATE_CLOSED_NONEMPTY MONOIDAL_ADD) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"P:num->bool")) THEN
    ASM_SIMP_TAC [NEUTRAL_ADD, ← GSYM nsum])

  let NSUM_RELATED_NONEMPTY ← prove
   r"!R (f:A->num) g s.
        (!m n m' n'. R m n /\ R m' n' ==> R (m + m') (n + n')) /\
        FINITE s /\ ~(s = {}) /\ (!x. x IN s ==> R (f x) (g x))
        ==> R (nsum s f) (nsum s g)"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN REPEAT DISCH_TAC THEN
    MP_TAC (← ISPEC (← q r"R:num->num->bool")
      (← MATCH_MP ITERATE_RELATED_NONEMPTY MONOIDAL_ADD)) THEN
    ASM_REWRITE_TAC [← GSYM nsum, NEUTRAL_ADD] THEN ASM_MESON_TAC [])

  let NSUM_ADD_NUMSEG ← prove
   r"!f g m n. nsum(m..n) (\i. f(i) + g(i)) = nsum(m..n) f + nsum(m..n) g"
   (SIMP_TAC [NSUM_ADD, FINITE_NUMSEG])

  let NSUM_LE_NUMSEG ← prove
   r"!f g m n. (!i. m <= i /\ i <= n ==> f(i) <= g(i))
             ==> nsum(m..n) f <= nsum(m..n) g"
   (SIMP_TAC [NSUM_LE, FINITE_NUMSEG, IN_NUMSEG])

  let NSUM_EQ_NUMSEG ← prove
   r"!f g m n. (!i. m <= i /\ i <= n ==> (f(i) = g(i)))
             ==> (nsum(m..n) f = nsum(m..n) g)"
   (MESON_TAC [NSUM_EQ, FINITE_NUMSEG, IN_NUMSEG])

  let NSUM_CONST_NUMSEG ← prove
   r"!c m n. nsum(m..n) (\n. c) = ((n + 1) - m) * c"
   (SIMP_TAC [NSUM_CONST, FINITE_NUMSEG, CARD_NUMSEG])

  let NSUM_EQ_0_NUMSEG ← prove
   r"!f m n. (!i. m <= i /\ i <= n ==> (f(i) = 0)) ==> (nsum(m..n) f = 0)"
   (SIMP_TAC [NSUM_EQ_0, IN_NUMSEG])

  let NSUM_EQ_0_IFF_NUMSEG ← prove
   r"!f m n. nsum (m..n) f = 0 <=> !i. m <= i /\ i <= n ==> f i = 0"
   (SIMP_TAC [NSUM_EQ_0_IFF, FINITE_NUMSEG, IN_NUMSEG])

  let NSUM_TRIV_NUMSEG ← prove
   r"!f m n. n < m ==> (nsum(m..n) f = 0)"
   (MESON_TAC [NSUM_EQ_0_NUMSEG, LE_TRANS, NOT_LT])

  let NSUM_SING_NUMSEG ← prove
   r"!f n. nsum(n..n) f = f(n)"
   (SIMP_TAC [NSUM_SING, NUMSEG_SING])

  let NSUM_CLAUSES_NUMSEG ← prove
   r"(!m. nsum(m..0) f = if m = 0 then f(0) else 0) /\
   (!m n. nsum(m..SUC n) f = if m <= SUC n then nsum(m..n) f + f(SUC n)
                             else nsum(m..n) f)"
   (MP_TAC (← MATCH_MP ITERATE_CLAUSES_NUMSEG MONOIDAL_ADD) THEN
    REWRITE_TAC [NEUTRAL_ADD, nsum])

  let NSUM_CLAUSES_NUMSEG_LT ← prove
   r"nsum {i | i < 0} f = 0 /\
   (!k. nsum {i | i < SUC k} f = nsum {i | i < k} f + f k)"
   (MP_TAC (← MATCH_MP ITERATE_CLAUSES_NUMSEG_LT MONOIDAL_ADD) THEN
    REWRITE_TAC [NEUTRAL_ADD, nsum])

  let NSUM_CLAUSES_NUMSEG_LE ← prove
   r"nsum {i | i <= 0} f = f 0 /\
   (!k. nsum {i | i <= SUC k} f = nsum {i | i <= k} f + f(SUC k))"
   (MP_TAC (← MATCH_MP ITERATE_CLAUSES_NUMSEG_LE MONOIDAL_ADD) THEN
    REWRITE_TAC [NEUTRAL_ADD, nsum])

  let NSUM_SWAP_NUMSEG ← prove
   r"!a b c d f.
     nsum(a..b) (\i. nsum(c..d) (f i)) =
     nsum(c..d) (\j. nsum(a..b) (\i. f i j))"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC NSUM_SWAP THEN REWRITE_TAC [FINITE_NUMSEG])

  let NSUM_ADD_SPLIT ← prove
   r"!f m n p.
        m <= n + 1 ==> (nsum (m..(n+p)) f = nsum(m..n) f + nsum(n+1..n+p) f)"
   (SIMP_TAC [NUMSEG_ADD_SPLIT, NSUM_UNION, DISJOINT_NUMSEG, FINITE_NUMSEG,
              ← ARITH_RULE (← q r"x < x + 1")])

  let NSUM_OFFSET ← prove
   r"!p f m n. nsum(m+p..n+p) f = nsum(m..n) (\i. f(i + p))"
   (SIMP_TAC [NUMSEG_OFFSET_IMAGE, NSUM_IMAGE, EQ_ADD_RCANCEL, FINITE_NUMSEG] THEN
    REWRITE_TAC [o_DEF])

  let NSUM_OFFSET_0 ← prove
   r"!f m n. m <= n ==> (nsum(m..n) f = nsum(0..n-m) (\i. f(i + m)))"
   (SIMP_TAC [← GSYM NSUM_OFFSET, ADD_CLAUSES, SUB_ADD])

  let NSUM_CLAUSES_LEFT ← prove
   r"!f m n. m <= n ==> nsum(m..n) f = f(m) + nsum(m+1..n) f"
   (SIMP_TAC [← GSYM NUMSEG_LREC, NSUM_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] THEN
    ARITH_TAC)

  let NSUM_CLAUSES_RIGHT ← prove
   r"!f m n. 0 < n /\ m <= n ==> nsum(m..n) f = nsum(m..n-1) f + f(n)"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    SIMP_TAC [LT_REFL, NSUM_CLAUSES_NUMSEG, SUC_SUB1])

  let NSUM_PAIR ← prove
   r"!f m n. nsum(2*m..2*n+1) f = nsum(m..n) (\i. f(2*i) + f(2*i+1))"
   (MP_TAC (← MATCH_MP ITERATE_PAIR MONOIDAL_ADD) THEN
    REWRITE_TAC [nsum, NEUTRAL_ADD])

  let NSUM_REFLECT ← prove
   r"!x m n. nsum(m..n) x = if n < m then 0 else nsum(0..n-m) (\i. x(n - i))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [nsum] THEN
    GEN_REWRITE_TAC LAND_CONV [← MATCH_MP ITERATE_REFLECT MONOIDAL_ADD] THEN
    REWRITE_TAC [NEUTRAL_ADD])

  let MOD_NSUM_MOD ← prove
   r"!f:A->num n s.
        FINITE s ==> (nsum s f) MOD n = nsum s (\i. f(i) MOD n) MOD n"
   (GEN_TAC THEN GEN_TAC THEN
    ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [MOD_ZERO, ETA_AX] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN SIMP_TAC [NSUM_CLAUSES] THEN
    REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM MOD_ADD_MOD] THEN
    ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [← GSYM MOD_ADD_MOD] THEN
    REWRITE_TAC [MOD_MOD_REFL])

  let MOD_NSUM_MOD_NUMSEG ← prove
   r"!f a b n.
        (nsum(a..b) f) MOD n = nsum(a..b) (\i. f i MOD n) MOD n"
   (MESON_TAC [MOD_NSUM_MOD, FINITE_NUMSEG])

  let CONG_NSUM ← prove
   r"!n (f:A->num) g s.
        FINITE s /\ (!x. x IN s ==> (f x == g x) (mod n))
        ==> (nsum s f == nsum s g) (mod n)"
   (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL
     [← q r"\x y:num. (x == y) (mod n)", ← q r"f:A->num", ← q r"g:A->num", ← q r"s:A->bool"]
          NSUM_RELATED) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONV_TAC NUMBER_RULE)

  -- `let th = prove (...) in extend_basic_congs (map SPEC_ALL (CONJUNCTS th))`
  -- (iterate.ml 1906); kept as the field NSUM_CONG.
  let NSUM_CONG ← prove
   r"(!f g s:A->bool.
        (!x. x IN s ==> f(x) = g(x))
        ==> nsum s (\i. f(i)) = nsum s g) /\
   (!f g a b. (!i. a <= i /\ i <= b ==> f(i) = g(i))
              ==> nsum(a..b) (\i. f(i)) = nsum(a..b) g) /\
   (!f g p. (!x. p x ==> f x = g x)
            ==> nsum {y | p y} (\i. f(i)) = nsum {y | p y} g)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC NSUM_EQ THEN
    ASM_SIMP_TAC [IN_ELIM_THM, IN_NUMSEG])
  liftM (extend_basic_congs (← (CONJUNCTS NSUM_CONG).mapM SPEC_ALL))

  return {
    NSUM_CLOSED, NSUM_RELATED, NSUM_CLOSED_NONEMPTY, NSUM_RELATED_NONEMPTY,
    NSUM_ADD_NUMSEG, NSUM_LE_NUMSEG, NSUM_EQ_NUMSEG, NSUM_CONST_NUMSEG,
    NSUM_EQ_0_NUMSEG, NSUM_EQ_0_IFF_NUMSEG, NSUM_TRIV_NUMSEG, NSUM_SING_NUMSEG,
    NSUM_CLAUSES_NUMSEG, NSUM_CLAUSES_NUMSEG_LT, NSUM_CLAUSES_NUMSEG_LE,
    NSUM_SWAP_NUMSEG, NSUM_ADD_SPLIT, NSUM_OFFSET, NSUM_OFFSET_0,
    NSUM_CLAUSES_LEFT, NSUM_CLAUSES_RIGHT, NSUM_PAIR, NSUM_REFLECT,
    MOD_NSUM_MOD, MOD_NSUM_MOD_NUMSEG, CONG_NSUM, NSUM_CONG }

/- ---------------------------------------------------------------------- -/
/- Thanks to finite sums, we can express cardinality of finite union.     -/
/- ---------------------------------------------------------------------- -/

/-- The cardinality/expansion bundle, iterate.ml 1920-1978: `CARD_UNIONS_IMAGE`
    and `CARD_UNIONS` (cardinality of a finite disjoint union via `nsum`), the
    three `EXPAND_NSUM_CONV` proformas, and `EXPAND_NSUM_CONV` itself (an
    `ioconv`, tested behaviourally). -/
structure IterateNsumCard where
  /-- `CARD_UNIONS_IMAGE` (iterate.ml 1923): `CARD(UNIONS(IMAGE f s)) =
      nsum s (\i. CARD(f i))` for a disjoint image family. -/
  CARD_UNIONS_IMAGE : thm
  /-- `CARD_UNIONS` (iterate.ml 1939): `CARD(UNIONS s) = nsum s CARD` for a
      pairwise-disjoint finite family. -/
  CARD_UNIONS : thm
  /-- `EXPAND_NSUM_CONV`'s `pth_0` (iterate.ml 1953): `n < m ==> nsum(m..n) f
      = 0`. -/
  pth_0 : thm
  /-- `EXPAND_NSUM_CONV`'s `pth_1` (iterate.ml 1954): `nsum(m..m) f = f m`. -/
  pth_1 : thm
  /-- `EXPAND_NSUM_CONV`'s `pth_2` (iterate.ml 1955): `m <= n ==> nsum(m..n) f
      = f m + nsum(m+1..n) f`. -/
  pth_2 : thm
  /-- `EXPAND_NSUM_CONV` (iterate.ml 1948-1978): expand `nsum(m..n) f` for
      numeral `m`, `n`.  A CONVERSION, so probed behaviourally. -/
  EXPAND_NSUM_CONV : ioconv
  deriving Inhabited

/-- `let rec conv tm = ...` inside EXPAND_NSUM_CONV (iterate.ml 1957). -/
partial def expandNsumConvImpl [HolBase]
    (NUM_LT_CONV NUM_LE_CONV NUM_ADD_CONV : ioconv)
    (pth_0 pth_1 pth_2 : thm) (ns_tm f_tm m_tm n_tm : term) : ioconv :=
  fun tm => ExceptT.run do
  let conv := expandNsumConvImpl NUM_LT_CONV NUM_LE_CONV NUM_ADD_CONV
    pth_0 pth_1 pth_2 ns_tm f_tm m_tm n_tm
  let (smn, ftm) ← dest_comb tm
  let (s, mn) ← dest_comb smn
  if !(is_const s && (match dest_const s with | .ok (c, _) => c == "nsum" | _ => false))
  then throw "EXPAND_NSUM_CONV" else
  let (mtm, ntm) ← dest_binop ns_tm mn
  let m ← dest_numeral mtm
  let n ← dest_numeral ntm
  if n < m then
    let th1 ← INST [(ftm, f_tm), (mtm, m_tm), (ntm, n_tm)] pth_0
    MP th1 (← EQT_ELIM (← NUM_LT_CONV (← lhand (concl th1))))
  else if n == m then CONV_RULE (RAND_CONV (TRY_CONV BETA_CONV))
                                 (← INST [(ftm, f_tm), (mtm, m_tm)] pth_1)
  else
    let th1 ← INST [(ftm, f_tm), (mtm, m_tm), (ntm, n_tm)] pth_2
    let th2 ← MP th1 (← EQT_ELIM (← NUM_LE_CONV (← lhand (concl th1))))
    CONV_RULE (RAND_CONV (COMB2_CONV (RAND_CONV (TRY_CONV BETA_CONV))
     (LAND_CONV (LAND_CONV NUM_ADD_CONV) THENC conv))) th2

@[nospecialize]
def setupIterateNsumCard [HolBase]
    (SET_TAC : List thm → tactic)
    (NUM_LT_CONV NUM_LE_CONV NUM_ADD_CONV : ioconv)
    (N1 : IterateNsum1) (N3 : IterateNsum3)
    (CARD_UNION_EQ FINITE_INDUCT_STRONG FINITE_IMAGE FINITE_UNIONS FINITE_UNION
     IMAGE_CLAUSES IMAGE_ID INTER_UNIONS UNIONS_0 UNIONS_INSERT NOT_IN_EMPTY
     IN_INSERT CARD_CLAUSES ETA_AX IMP_CONJ : thm) :
    ExceptT String IO IterateNsumCard := do
  let { NSUM_CLAUSES, .. } := N1
  let { NSUM_CLAUSES_LEFT, NSUM_SING_NUMSEG, NSUM_TRIV_NUMSEG, .. } := N3

  let CARD_UNIONS_IMAGE ← prove
   r"!(f:K->A->bool) s.
        FINITE s /\ (!t. t IN s ==> FINITE(f t)) /\
        (!t u. t IN s /\ u IN s /\ ~(t = u) ==> f t INTER f u = {})
        ==> CARD(UNIONS(IMAGE f s)) = nsum s (\i. CARD(f i))"
   (GEN_TAC THEN ONCE_REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC [IMAGE_CLAUSES] THEN
    REWRITE_TAC [UNIONS_0, UNIONS_INSERT, NOT_IN_EMPTY, IN_INSERT] THEN
    REWRITE_TAC [CARD_CLAUSES, NSUM_CLAUSES] THEN REPEAT GEN_TAC THEN
    DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC [NSUM_CLAUSES] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
    ASM_SIMP_TAC [FINITE_IMAGE, FINITE_UNIONS, FINITE_UNION, INTER_UNIONS] THEN
    ASM SET_TAC [])

  let CARD_UNIONS ← prove
   r"!s:(A->bool)->bool.
        FINITE s /\ (!t. t IN s ==> FINITE t) /\
        (!t u. t IN s /\ u IN s /\ ~(t = u) ==> t INTER u = {})
        ==> CARD(UNIONS s) = nsum s CARD"
   (MP_TAC (← ISPEC (← q r"\x:A->bool. x") CARD_UNIONS_IMAGE) THEN
    REWRITE_TAC [IMAGE_ID, ETA_AX])

  /- Expand "nsum (m..n) f" where m and n are numerals. -/

  let [pth_0, pth_1, pth_2] := CONJUNCTS (← prove
   r"(n < m ==> nsum(m..n) f = 0) /\
     nsum(m..m) f = f m /\
     (m <= n ==> nsum (m..n) f = f m + nsum (m + 1..n) f)"
    (REWRITE_TAC [NSUM_CLAUSES_LEFT, NSUM_SING_NUMSEG, NSUM_TRIV_NUMSEG]))
    | throw "EXPAND_NSUM_CONV"
  let ns_tm ← q r".."
  let f_tm ← q r"f:num->num"
  let m_tm ← q r"m:num"
  let n_tm ← q r"n:num"
  let EXPAND_NSUM_CONV := expandNsumConvImpl NUM_LT_CONV NUM_LE_CONV NUM_ADD_CONV
    pth_0 pth_1 pth_2 ns_tm f_tm m_tm n_tm

  return {
    CARD_UNIONS_IMAGE, CARD_UNIONS, pth_0, pth_1, pth_2, EXPAND_NSUM_CONV }

/- ---------------------------------------------------------------------- -/
/- Sums of real numbers.                                                  -/
/- (`prioritize_real()` at iterate.ml 1982 is run by Session.)            -/
/- ---------------------------------------------------------------------- -/

/-- iterate.ml 1984-2211: the `sum` definition and the first thirty-three
    theorems, `SUM_DEGENERATE` through `SUM_SWAP`. -/
structure IterateSum1 where
  /-- `sum` (iterate.ml 1984): `sum = iterate ((+):real->real->real)`, the
      finite sum over `:real`.  `new_definition`; neutral `&0`. -/
  sum : thm
  /-- `NEUTRAL_REAL_ADD` (iterate.ml 1987): `neutral((+):real->real->real)
      = &0`. -/
  NEUTRAL_REAL_ADD : thm
  /-- `MONOIDAL_REAL_ADD` (iterate.ml 1992): `monoidal((+):real->real->real)`. -/
  MONOIDAL_REAL_ADD : thm
  /-- `SUM_DEGENERATE` (iterate.ml 1996): infinite support gives `sum = &0`. -/
  SUM_DEGENERATE : thm
  /-- `SUM_CLAUSES` (iterate.ml 2001): the empty/insert recursion clauses. -/
  SUM_CLAUSES : thm
  /-- `SUM_UNION` (iterate.ml 2011): sum over a disjoint union. -/
  SUM_UNION : thm
  /-- `SUM_DIFF` (iterate.ml 2017): sum over a set difference. -/
  SUM_DIFF : thm
  /-- `SUM_INCL_EXCL` (iterate.ml 2021): the inclusion-exclusion identity. -/
  SUM_INCL_EXCL : thm
  /-- `SUM_SUPPORT` (iterate.ml 2028): `sum (support (+) f s) f = sum s f`. -/
  SUM_SUPPORT : thm
  /-- `SUM_ADD` (iterate.ml 2032): additivity of the summand. -/
  SUM_ADD : thm
  /-- `SUM_ADD_GEN` (iterate.ml 2036): additivity under finite support. -/
  SUM_ADD_GEN : thm
  /-- `SUM_EQ_0` (iterate.ml 2043): a summand identically `&0` gives `&0`. -/
  SUM_EQ_0 : thm
  /-- `SUM_0` (iterate.ml 2048): `sum s (\n. &0) = &0`. -/
  SUM_0 : thm
  /-- `SUM_LMUL` (iterate.ml 2052): `sum s (\x. c * f x) = c * sum s f`. -/
  SUM_LMUL : thm
  /-- `SUM_RMUL` (iterate.ml 2066): `sum s (\x. f x * c) = sum s f * c`. -/
  SUM_RMUL : thm
  /-- `SUM_NEG` (iterate.ml 2070): `sum s (\x. --(f x)) = --(sum s f)`. -/
  SUM_NEG : thm
  /-- `SUM_SUB` (iterate.ml 2075): subtractivity of the summand. -/
  SUM_SUB : thm
  /-- `SUM_LE` (iterate.ml 2079): monotonicity in the summand. -/
  SUM_LE : thm
  /-- `SUM_LT` (iterate.ml 2086): strict monotonicity with a strict witness. -/
  SUM_LT : thm
  /-- `SUM_LT_ALL` (iterate.ml 2099): strict monotonicity, everywhere strict. -/
  SUM_LT_ALL : thm
  /-- `SUM_POS_LT` (iterate.ml 2105): a positive term gives a positive sum. -/
  SUM_POS_LT : thm
  /-- `SUM_POS_LT_ALL` (iterate.ml 2117): all-positive terms give positive sum. -/
  SUM_POS_LT_ALL : thm
  /-- `SUM_EQ` (iterate.ml 2123): extensional equality of the summand. -/
  SUM_EQ : thm
  /-- `SUM_ABS` (iterate.ml 2128): the triangle inequality for finite sums. -/
  SUM_ABS : thm
  /-- `SUM_ABS_LE` (iterate.ml 2134): a bound via the absolute-value sum. -/
  SUM_ABS_LE : thm
  /-- `SUM_CONST` (iterate.ml 2143): `sum s (\n. c) = &(CARD s) * c`. -/
  SUM_CONST : thm
  /-- `SUM_POS_LE` (iterate.ml 2149): nonnegative terms give a nonnegative sum. -/
  SUM_POS_LE : thm
  /-- `SUM_POS_BOUND` (iterate.ml 2160): a bound on the sum bounds each term. -/
  SUM_POS_BOUND : thm
  /-- `SUM_POS_EQ_0` (iterate.ml 2170): a zero sum of nonnegatives is all zero. -/
  SUM_POS_EQ_0 : thm
  /-- `SUM_ZERO_EXISTS` (iterate.ml 2177): a zero sum is all zero or has a
      strictly negative and a strictly positive term. -/
  SUM_ZERO_EXISTS : thm
  /-- `SUM_DELETE` (iterate.ml 2190): `sum (s DELETE a) f = sum s f - f a`. -/
  SUM_DELETE : thm
  /-- `SUM_DELETE_CASES` (iterate.ml 2195): the case split of `SUM_DELETE`. -/
  SUM_DELETE_CASES : thm
  /-- `SUM_SING` (iterate.ml 2202): `sum {x} f = f x`. -/
  SUM_SING : thm
  /-- `SUM_DELTA` (iterate.ml 2206): sum of a delta function. -/
  SUM_DELTA : thm
  /-- `SUM_SWAP` (iterate.ml 2211): exchange of two finite summations. -/
  SUM_SWAP : thm
  deriving Inhabited

@[nospecialize]
def setupIterateSum1 [HolBase]
    (new_definition' : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic)
    (MESON' : List thm → term → IO (Except String thm))
    (SET_TAC : List thm → tactic)
    (SET_RULE' : term → IO (Except String thm))
    (REAL_ARITH' : term → IO (Except String thm))
    (REAL_ARITH_TAC : tactic)
    (IGen : IterateGeneric) (IK1 : IterateKey1) (IK2 : IterateKey2)
    (IK3 : IterateKey3)
    (SELECT_UNIQUE REAL_ADD_LID REAL_ADD_RID REAL_MUL_LZERO REAL_MUL_RZERO
     REAL_MUL_SYM REAL_ENTIRE REAL_ADD_LDISTRIB REAL_LE_REFL REAL_LE_ADD2
     REAL_LTE_ADD2 REAL_LET_TRANS REAL_LE_TRANS REAL_LE_ANTISYM REAL_ABS_NUM
     REAL_OF_NUM_SUC REAL_EQ_SUB_LADD REAL_NEG_0 REAL_LT_IMP_LE real_sub
     FINITE_RULES FINITE_INDUCT_STRONG FINITE_DELETE NOT_IN_EMPTY IN_INSERT
     IN_DELETE IN_ELIM_THM MEMBER_NOT_EMPTY CARD_CLAUSES ETA_AX
     SWAP_FORALL_THM RIGHT_FORALL_IMP_THM IMP_CONJ : thm) :
    ExceptT String IO IterateSum1 := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let MESON (ths : List thm) (t : term) : ExceptT String IO thm := MESON' ths t
  let SET_RULE (t : term) : ExceptT String IO thm := SET_RULE' t
  let REAL_ARITH (t : term) : ExceptT String IO thm := REAL_ARITH' t
  let ASM_MESON_TAC := ASM MESON_TAC
  let { neutral, monoidal, iterate, support, SUPPORT_SUPPORT, .. } := IGen
  let { ITERATE_CLAUSES, ITERATE_UNION, ITERATE_DIFF, ITERATE_INCL_EXCL,
        ITERATE_EQ_NEUTRAL, ITERATE_EXPAND_CASES, ITERATE_DELETE, .. } := IK1
  let { ITERATE_OP, ITERATE_EQ, ITERATE_DELTA, .. } := IK2
  let { ITERATE_OP_GEN, .. } := IK3

  let sum ← new_definition
    r"sum:(A->bool)->(A->real)->real = iterate (+)"

  let NEUTRAL_REAL_ADD ← prove
   r"neutral((+):real->real->real) = &0"
   (REWRITE_TAC [neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    MESON_TAC [REAL_ADD_LID, REAL_ADD_RID])

  let MONOIDAL_REAL_ADD ← prove
   r"monoidal((+):real->real->real)"
   (REWRITE_TAC [monoidal, NEUTRAL_REAL_ADD] THEN REAL_ARITH_TAC)

  let SUM_DEGENERATE ← prove
   r"!f s:A->bool. ~(FINITE {x | x IN s /\ ~(f x = &0)}) ==> sum s f = &0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [sum] THEN
    SIMP_TAC [iterate, support, NEUTRAL_REAL_ADD])

  let SUM_CLAUSES ← prove
   r"(!f:A->real. sum {} f = &0) /\
   (!x (f:B->real) s.
        FINITE(s)
        ==> (sum (x INSERT s) f =
             if x IN s then sum s f else f(x) + sum s f))"
   (REWRITE_TAC [sum, ← GSYM NEUTRAL_REAL_ADD] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC [MONOIDAL_REAL_ADD])

  let SUM_UNION ← prove
   r"!f s t:A->bool.
        FINITE s /\ FINITE t /\ DISJOINT s t
        ==> sum (s UNION t) f = sum s f + sum t f"
   (SIMP_TAC [sum, ITERATE_UNION, MONOIDAL_REAL_ADD])

  let SUM_DIFF ← prove
   r"!f s t:A->bool. FINITE s /\ t SUBSET s ==> (sum (s DIFF t) f = sum s f - sum t f)"
   (SIMP_TAC [REAL_EQ_SUB_LADD, sum, ITERATE_DIFF, MONOIDAL_REAL_ADD])

  let SUM_INCL_EXCL ← prove
   r"!s t (f:A->real).
     FINITE s /\ FINITE t
     ==> sum s f + sum t f = sum (s UNION t) f + sum (s INTER t) f"
   (REWRITE_TAC [sum, ← GSYM NEUTRAL_REAL_ADD] THEN
    MATCH_MP_TAC ITERATE_INCL_EXCL THEN REWRITE_TAC [MONOIDAL_REAL_ADD])

  let SUM_SUPPORT ← prove
   r"!f s:A->bool. sum (support (+) f s) f = sum s f"
   (SIMP_TAC [sum, iterate, SUPPORT_SUPPORT])

  let SUM_ADD ← prove
   r"!f g s:A->bool. FINITE s ==> (sum s (\x. f(x) + g(x)) = sum s f + sum s g)"
   (SIMP_TAC [sum, ITERATE_OP, MONOIDAL_REAL_ADD])

  let SUM_ADD_GEN ← prove
   r"!f g s:A->bool.
       FINITE {x | x IN s /\ ~(f x = &0)} /\ FINITE {x | x IN s /\ ~(g x = &0)}
       ==> sum s (\x. f x + g x) = sum s f + sum s g"
   (REWRITE_TAC [← GSYM NEUTRAL_REAL_ADD, ← GSYM support, sum] THEN
    MATCH_MP_TAC ITERATE_OP_GEN THEN ACCEPT_TAC MONOIDAL_REAL_ADD)

  let SUM_EQ_0 ← prove
   r"!f s. (!x:A. x IN s ==> (f(x) = &0)) ==> (sum s f = &0)"
   (REWRITE_TAC [sum, ← GSYM NEUTRAL_REAL_ADD] THEN
    SIMP_TAC [ITERATE_EQ_NEUTRAL, MONOIDAL_REAL_ADD])

  let SUM_0 ← prove
   r"!s:A->bool. sum s (\n. &0) = &0"
   (SIMP_TAC [SUM_EQ_0])

  let SUM_LMUL ← prove
   r"!f c s:A->bool. sum s (\x. c * f(x)) = c * sum s f"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"c = &0") THEN
    ASM_REWRITE_TAC [REAL_MUL_LZERO, SUM_0] THEN REWRITE_TAC [sum] THEN
    ONCE_REWRITE_TAC [ITERATE_EXPAND_CASES] THEN
    SUBGOAL_THEN (← q r"support (+) (\x:A. c * f(x)) s = support (+) f s") SUBST1_TAC
    THENL [ASM_SIMP_TAC [support, REAL_ENTIRE, NEUTRAL_REAL_ADD], ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC [NEUTRAL_REAL_ADD, REAL_MUL_RZERO] THEN
    UNDISCH_TAC (← q r"FINITE (support (+) f (s:A->bool))") THEN
    SPEC_TAC ((← q r"support (+) f (s:A->bool)"), (← q r"t:A->bool")) THEN
    REWRITE_TAC [← GSYM sum] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [SUM_CLAUSES, REAL_MUL_RZERO, REAL_MUL_LZERO,
              REAL_ADD_LDISTRIB])

  let SUM_RMUL ← prove
   r"!f c s:A->bool. sum s (\x. f(x) * c) = sum s f * c"
   (ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [SUM_LMUL])

  let SUM_NEG ← prove
   r"!f s:A->bool. sum s (\x. --(f(x))) = --(sum s f)"
   (ONCE_REWRITE_TAC [← REAL_ARITH (← q r"--x = --(&1) * x")] THEN
    SIMP_TAC [SUM_LMUL])

  let SUM_SUB ← prove
   r"!f g s:A->bool. FINITE s ==> sum s (\x. f(x) - g(x)) = sum s f - sum s g"
   (ONCE_REWRITE_TAC [real_sub] THEN SIMP_TAC [SUM_NEG, SUM_ADD])

  let SUM_LE ← prove
   r"!f g s:A->bool.
        FINITE(s) /\ (!x. x IN s ==> f(x) <= g(x)) ==> sum s f <= sum s g"
   (ONCE_REWRITE_TAC [IMP_CONJ] THEN
    GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [SUM_CLAUSES, REAL_LE_REFL, REAL_LE_ADD2, IN_INSERT])

  let SUM_LT ← prove
   r"!f g s:A->bool.
        FINITE(s) /\ (!x. x IN s ==> f(x) <= g(x)) /\
        (?x. x IN s /\ f(x) < g(x))
         ==> sum s f < sum s g"
   (REPEAT GEN_TAC THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"s = (a:A) INSERT (s DELETE a)") SUBST1_TAC THENL
     [UNDISCH_TAC (← q r"a:A IN s") THEN SET_TAC [], ALL_TAC] THEN
    ASM_SIMP_TAC [SUM_CLAUSES, FINITE_DELETE, IN_DELETE] THEN
    ASM_SIMP_TAC [REAL_LTE_ADD2, SUM_LE, IN_DELETE, FINITE_DELETE])

  let SUM_LT_ALL ← prove
   r"!f g s:A->bool.
        FINITE s /\ ~(s = {}) /\ (!x. x IN s ==> f(x) < g(x))
        ==> sum s f < sum s g"
   (MESON_TAC [MEMBER_NOT_EMPTY, REAL_LT_IMP_LE, SUM_LT])

  let SUM_POS_LT ← prove
   r"!f s:A->bool.
        FINITE s /\
        (!x. x IN s ==> &0 <= f x) /\
        (?x. x IN s /\ &0 < f x)
        ==> &0 < sum s f"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (← q r"sum (s:A->bool) (\i. &0)") THEN CONJ_TAC THENL
     [REWRITE_TAC [SUM_0, REAL_LE_REFL], MATCH_MP_TAC SUM_LT] THEN
    ASM_MESON_TAC [])

  let SUM_POS_LT_ALL ← prove
   r"!s f:A->real.
     FINITE s /\ ~(s = {}) /\ (!i. i IN s ==> &0 < f i) ==> &0 < sum s f"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_POS_LT THEN
    ASM_MESON_TAC [MEMBER_NOT_EMPTY, REAL_LT_IMP_LE])

  let SUM_EQ ← prove
   r"!f g s:A->bool. (!x. x IN s ==> (f x = g x)) ==> (sum s f = sum s g)"
   (REWRITE_TAC [sum] THEN
    MATCH_MP_TAC ITERATE_EQ THEN REWRITE_TAC [MONOIDAL_REAL_ADD])

  let SUM_ABS ← prove
   r"!f s:A->bool. FINITE(s) ==> abs(sum s f) <= sum s (\x. abs(f x))"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [SUM_CLAUSES, REAL_ABS_NUM, REAL_LE_REFL,
              ← REAL_ARITH (← q r"abs(a) <= b ==> abs(x + a) <= abs(x) + b")])

  let SUM_ABS_LE ← prove
   r"!f:A->real g s:A->bool.
        FINITE s /\ (!x. x IN s ==> abs(f x) <= g x)
        ==> abs(sum s f) <= sum s g"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"sum s (\x:A. abs(f x))") THEN
    ASM_SIMP_TAC [SUM_ABS] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_REWRITE_TAC [])

  let SUM_CONST ← prove
   r"!c s:A->bool. FINITE s ==> (sum s (\n. c) = &(CARD s) * c)"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [SUM_CLAUSES, CARD_CLAUSES, ← GSYM REAL_OF_NUM_SUC] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC)

  let SUM_POS_LE ← prove
   r"!s:A->bool. (!x. x IN s ==> &0 <= f x) ==> &0 <= sum s f"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"FINITE {x:A | x IN s /\ ~(f x = &0)}") THEN
    ASM_SIMP_TAC [SUM_DEGENERATE, REAL_LE_REFL] THEN
    ONCE_REWRITE_TAC [← GSYM SUM_SUPPORT] THEN
    REWRITE_TAC [support, NEUTRAL_REAL_ADD] THEN
    MP_TAC (← ISPECL [← q r"\x:A. &0", ← q r"f:A->real",
                      ← q r"{x:A | x IN s /\ ~(f x = &0)}"]
          SUM_LE) THEN
    ASM_SIMP_TAC [SUM_0, IN_ELIM_THM])

  let SUM_POS_BOUND ← prove
   r"!f b s:A->bool.
        FINITE s /\ (!x. x IN s ==> &0 <= f x) /\ sum s f <= b
        ==> !x:A. x IN s ==> f x <= b"
   (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [SUM_CLAUSES, NOT_IN_EMPTY, IN_INSERT] THEN
    MESON_TAC [SUM_POS_LE,
     ← REAL_ARITH (← q r"&0 <= x /\ &0 <= y /\ x + y <= b ==> x <= b /\ y <= b")])

  let SUM_POS_EQ_0 ← prove
   r"!f s:A->bool.
        FINITE s /\ (!x. x IN s ==> &0 <= f x) /\ (sum s f = &0)
        ==> !x. x IN s ==> f x = &0"
   (REWRITE_TAC [← GSYM REAL_LE_ANTISYM] THEN
    MESON_TAC [SUM_POS_BOUND, SUM_POS_LE])

  let SUM_ZERO_EXISTS ← prove
   r"!(u:A->real) s.
         FINITE s /\ sum s u = &0
         ==> (!i. i IN s ==> u i = &0) \/
             (?j k. j IN s /\ u j < &0 /\ k IN s /\ u k > &0)"
   (REPEAT STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (← MESON [← REAL_ARITH (← q r"(&0 <= --u <=> ~(u > &0)) /\ (&0 <= u <=> ~(u < &0))")]
       (← q r"(?j k:A. j IN s /\ u j < &0 /\ k IN s /\ u k > &0) \/
        (!i. i IN s ==> &0 <= u i) \/ (!i. i IN s ==> &0 <= --(u i))")) THEN
    ASM_REWRITE_TAC [] THEN DISJ1_TAC THENL
     [ALL_TAC, ONCE_REWRITE_TAC [← REAL_ARITH (← q r"x = &0 <=> --x = &0")]] THEN
    MATCH_MP_TAC SUM_POS_EQ_0 THEN ASM_REWRITE_TAC [SUM_NEG, REAL_NEG_0])

  let SUM_DELETE ← prove
   r"!f s a:A. FINITE s /\ a IN s ==> sum (s DELETE a) f = sum s f - f(a)"
   (SIMP_TAC [← REAL_ARITH (← q r"y = z - x <=> x + y = z:real"), sum, ITERATE_DELETE,
              MONOIDAL_REAL_ADD])

  let SUM_DELETE_CASES ← prove
   r"!f s a:A. FINITE s
             ==> sum (s DELETE a) f = if a IN s then sum s f - f(a)
                                      else sum s f"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [← SET_RULE (← q r"~(a IN s) ==> (s DELETE a = s)"), SUM_DELETE])

  let SUM_SING ← prove
   r"!f x:A. sum {x} f = f(x)"
   (SIMP_TAC [SUM_CLAUSES, FINITE_RULES, NOT_IN_EMPTY, REAL_ADD_RID])

  let SUM_DELTA ← prove
   r"!s a. sum s (\x. if x = a:A then b else &0) = if a IN s then b else &0"
   (REWRITE_TAC [sum, ← GSYM NEUTRAL_REAL_ADD] THEN
    SIMP_TAC [ITERATE_DELTA, MONOIDAL_REAL_ADD])

  let SUM_SWAP ← prove
   r"!f:A->B->real s t.
      FINITE(s) /\ FINITE(t)
      ==> (sum s (\i. sum t (f i)) = sum t (\j. sum s (\i. f i j)))"
   (GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [SUM_CLAUSES, SUM_0, SUM_ADD, ETA_AX])

  return {
    sum, NEUTRAL_REAL_ADD, MONOIDAL_REAL_ADD, SUM_DEGENERATE, SUM_CLAUSES,
    SUM_UNION, SUM_DIFF, SUM_INCL_EXCL, SUM_SUPPORT, SUM_ADD, SUM_ADD_GEN,
    SUM_EQ_0, SUM_0, SUM_LMUL, SUM_RMUL, SUM_NEG, SUM_SUB, SUM_LE, SUM_LT,
    SUM_LT_ALL, SUM_POS_LT, SUM_POS_LT_ALL, SUM_EQ, SUM_ABS, SUM_ABS_LE,
    SUM_CONST, SUM_POS_LE, SUM_POS_BOUND, SUM_POS_EQ_0, SUM_ZERO_EXISTS,
    SUM_DELETE, SUM_DELETE_CASES, SUM_SING, SUM_DELTA, SUM_SWAP }

/-- iterate.ml 2219-2598: the second `sum` bundle - image/superset/restriction,
    counting, subset monotonicity, product/general transfer, and the
    closure/relation lemmas, `SUM_IMAGE` through `REAL_OF_NUM_SUM_GEN`. -/
structure IterateSum2 where
  /-- `SUM_IMAGE` (iterate.ml 2219): sum over an injective image. -/
  SUM_IMAGE : thm
  /-- `SUM_SUPERSET` (iterate.ml 2226): drop points where the summand is `&0`. -/
  SUM_SUPERSET : thm
  /-- `SUM_UNIV` (iterate.ml 2232): extend a sum to the universe. -/
  SUM_UNIV : thm
  /-- `SUM_UNION_RZERO` (iterate.ml 2237): union with a right zero part. -/
  SUM_UNION_RZERO : thm
  /-- `SUM_UNION_LZERO` (iterate.ml 2246): union with a left zero part. -/
  SUM_UNION_LZERO : thm
  /-- `SUM_RESTRICT` (iterate.ml 2252): restrict the summand to the set. -/
  SUM_RESTRICT : thm
  /-- `SUM_BOUND` (iterate.ml 2257): a pointwise bound bounds the sum. -/
  SUM_BOUND : thm
  /-- `SUM_BOUND_GEN` (iterate.ml 2262): the averaged form of `SUM_BOUND`. -/
  SUM_BOUND_GEN : thm
  /-- `SUM_ABS_BOUND` (iterate.ml 2268): an absolute pointwise bound. -/
  SUM_ABS_BOUND : thm
  /-- `SUM_BOUND_LT` (iterate.ml 2275): a strict pointwise bound. -/
  SUM_BOUND_LT : thm
  /-- `SUM_BOUND_LT_ALL` (iterate.ml 2283): everywhere strict pointwise bound. -/
  SUM_BOUND_LT_ALL : thm
  /-- `SUM_BOUND_LT_GEN` (iterate.ml 2288): the averaged strict form. -/
  SUM_BOUND_LT_GEN : thm
  /-- `SUM_UNION_EQ` (iterate.ml 2294): a partition equation for sums. -/
  SUM_UNION_EQ : thm
  /-- `SUM_EQ_SUPERSET` (iterate.ml 2300): equality up to a zero superset. -/
  SUM_EQ_SUPERSET : thm
  /-- `SUM_RESTRICT_SET` (iterate.ml 2308): sum over a comprehension. -/
  SUM_RESTRICT_SET : thm
  /-- `SUM_SUM_RESTRICT` (iterate.ml 2313): swap two restricted sums. -/
  SUM_SUM_RESTRICT : thm
  /-- `CARD_EQ_SUM` (iterate.ml 2321): `&(CARD s) = sum s (\x. &1)`. -/
  CARD_EQ_SUM : thm
  /-- `SUM_MULTICOUNT_GEN` (iterate.ml 2325): the general counting identity. -/
  SUM_MULTICOUNT_GEN : thm
  /-- `SUM_MULTICOUNT` (iterate.ml 2344): the uniform counting identity. -/
  SUM_MULTICOUNT : thm
  /-- `SUM_IMAGE_GEN` (iterate.ml 2354): the general image decomposition. -/
  SUM_IMAGE_GEN : thm
  /-- `SUM_GROUP` (iterate.ml 2362): grouping by a function's fibres. -/
  SUM_GROUP : thm
  /-- `SUM_GROUP_RELATION` (iterate.ml 2372): grouping by a relation. -/
  SUM_GROUP_RELATION : thm
  /-- `REAL_OF_NUM_SUM` (iterate.ml 2386): `&(nsum s f) = sum s (\x. &(f x))`. -/
  REAL_OF_NUM_SUM : thm
  /-- `SUM_SUBSET` (iterate.ml 2391): subset monotonicity with sign control. -/
  SUM_SUBSET : thm
  /-- `SUM_SUBSET_SIMPLE` (iterate.ml 2409): the simple subset form. -/
  SUM_SUBSET_SIMPLE : thm
  /-- `SUM_MUL_BOUND` (iterate.ml 2416): a product bound for two sums. -/
  SUM_MUL_BOUND : thm
  /-- `SUM_IMAGE_NONZERO` (iterate.ml 2427): image sum with a nonzero clause. -/
  SUM_IMAGE_NONZERO : thm
  /-- `SUM_BIJECTION` (iterate.ml 2435): sum invariance under a bijection. -/
  SUM_BIJECTION : thm
  /-- `SUM_SUM_PRODUCT` (iterate.ml 2443): the iterated-product identity. -/
  SUM_SUM_PRODUCT : thm
  /-- `SUM_EQ_GENERAL` (iterate.ml 2451): equality via a general correspondence. -/
  SUM_EQ_GENERAL : thm
  /-- `SUM_EQ_GENERAL_INVERSES` (iterate.ml 2459): equality via inverse maps. -/
  SUM_EQ_GENERAL_INVERSES : thm
  /-- `SUM_INJECTION` (iterate.ml 2467): sum invariance under an injection. -/
  SUM_INJECTION : thm
  /-- `SUM_UNION_NONZERO` (iterate.ml 2476): union sum with a nonzero overlap. -/
  SUM_UNION_NONZERO : thm
  /-- `SUM_UNIONS_NONZERO` (iterate.ml 2483): a nonzero union-of-family sum. -/
  SUM_UNIONS_NONZERO : thm
  /-- `SUM_CASES` (iterate.ml 2498): split a sum by a predicate. -/
  SUM_CASES : thm
  /-- `SUM_CASES_1` (iterate.ml 2505): the single-point case split. -/
  SUM_CASES_1 : thm
  /-- `SUM_LE_INCLUDED` (iterate.ml 2513): a bound via an inclusion map. -/
  SUM_LE_INCLUDED : thm
  /-- `SUM_IMAGE_LE` (iterate.ml 2539): a bound for an image sum. -/
  SUM_IMAGE_LE : thm
  /-- `SUM_CLOSED` (iterate.ml 2549): a closure property of the sum. -/
  SUM_CLOSED : thm
  /-- `SUM_RELATED` (iterate.ml 2557): a relation preserved by the sum. -/
  SUM_RELATED : thm
  /-- `SUM_CLOSED_NONEMPTY` (iterate.ml 2569): closure over a nonempty set. -/
  SUM_CLOSED_NONEMPTY : thm
  /-- `SUM_RELATED_NONEMPTY` (iterate.ml 2579): relation over a nonempty set. -/
  SUM_RELATED_NONEMPTY : thm
  /-- `REAL_OF_NUM_SUM_GEN` (iterate.ml 2590): the finite-support transfer. -/
  REAL_OF_NUM_SUM_GEN : thm
  deriving Inhabited

@[nospecialize]
def setupIterateSum2 [HolBase]
    (MESON_TAC : List thm → tactic)
    (SET_TAC : List thm → tactic)
    (SET_RULE' : term → IO (Except String thm))
    (REAL_ARITH' : term → IO (Except String thm))
    (REAL_ARITH_TAC : tactic)
    (IGen : IterateGeneric) (IK1 : IterateKey1) (IK2 : IterateKey2)
    (IK3 : IterateKey3) (IS1 : IterateSum1)
    (NEUTRAL_ADD FINITE_INDUCT_STRONG FINITE_IMAGE FINITE_RESTRICT FINITE_DIFF
     FINITE_INTER FINITE_UNIONS FINITE_SUBSET IN_INSERT IN_ELIM_THM IN_DIFF
     IN_INTER IN_UNION IN_UNIONS FORALL_IN_IMAGE SING_SUBSET SUBSET SUBSET_UNION
     UNION_COMM UNIONS_0 UNIONS_INSERT DELETE EQ_TRANS DISJOINT CONJ_ASSOC
     IMP_CONJ RIGHT_FORALL_IMP_THM LEFT_IMP_EXISTS_THM o_THM MEMBER_NOT_EMPTY
     REAL_LE_TRANS REAL_LTE_TRANS REAL_EQ_IMP_LE REAL_LE_RMUL REAL_LE_RNEG
     REAL_LE_REFL REAL_ADD_LID REAL_MUL_RID REAL_OF_NUM_ADD REAL_OF_NUM_MUL
     REAL_OF_NUM_EQ REAL_DIV_LMUL REAL_LT_IMP_LE HAS_SIZE HAS_SIZE_0 MULT_AC
     NSUM_CLAUSES NSUM_SUPPORT : thm) :
    ExceptT String IO IterateSum2 := do
  let SET_RULE (t : term) : ExceptT String IO thm := SET_RULE' t
  let REAL_ARITH (t : term) : ExceptT String IO thm := REAL_ARITH' t
  let ASM_MESON_TAC := ASM MESON_TAC
  let { support, .. } := IGen
  let { ITERATE_CLOSED, ITERATE_RELATED, ITERATE_CLOSED_NONEMPTY,
        ITERATE_RELATED_NONEMPTY, .. } := IK1
  let { ITERATE_IMAGE, ITERATE_RESTRICT_SET, ITERATE_EQ_GENERAL,
        ITERATE_EQ_GENERAL_INVERSES, ITERATE_INJECTION, ITERATE_UNION_NONZERO,
        ITERATE_BIJECTION, ITERATE_ITERATE_PRODUCT, .. } := IK2
  let { ITERATE_SUPERSET, ITERATE_UNIV, ITERATE_IMAGE_GEN, ITERATE_IMAGE_NONZERO,
        ITERATE_CASES, .. } := IK3
  let { sum, NEUTRAL_REAL_ADD, MONOIDAL_REAL_ADD, SUM_CLAUSES, SUM_UNION,
        SUM_SUPPORT, SUM_EQ_0, SUM_LMUL, SUM_NEG, SUM_LE, SUM_LT, SUM_EQ, SUM_ABS,
        SUM_CONST, SUM_POS_LE, SUM_DELETE, SUM_SING, SUM_SWAP, .. } := IS1

  let SUM_IMAGE ← prove
   r"!(f:A->B) g s.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> sum (IMAGE f s) g = sum s (g o f)"
   (REWRITE_TAC [sum, ← GSYM NEUTRAL_REAL_ADD] THEN
    MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC [MONOIDAL_REAL_ADD])

  let SUM_SUPERSET ← prove
   r"!f:A->real u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = &0))
        ==> (sum v f = sum u f)"
   (SIMP_TAC [sum, ← GSYM NEUTRAL_REAL_ADD, ITERATE_SUPERSET, MONOIDAL_REAL_ADD])

  let SUM_UNIV ← prove
   r"!f:A->real s. support (+) f (:A) SUBSET s ==> sum s f = sum (:A) f"
   (REWRITE_TAC [sum] THEN MATCH_MP_TAC ITERATE_UNIV THEN
    REWRITE_TAC [MONOIDAL_REAL_ADD])

  let SUM_UNION_RZERO ← prove
   r"!f:A->real u v.
        FINITE u /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = &0))
        ==> sum (u UNION v) f = sum u f"
   (← do
    let lemma ← prove r"u UNION v = u UNION (v DIFF u)" (SET_TAC [])
    pure
     (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [lemma] THEN
      MATCH_MP_TAC SUM_SUPERSET THEN
      ASM_MESON_TAC [IN_UNION, IN_DIFF, SUBSET]))

  let SUM_UNION_LZERO ← prove
   r"!f:A->real u v.
        FINITE v /\ (!x. x IN u /\ ~(x IN v) ==> (f(x) = &0))
        ==> sum (u UNION v) f = sum v f"
   (MESON_TAC [SUM_UNION_RZERO, UNION_COMM])

  let SUM_RESTRICT ← prove
   r"!f s:A->bool.
        FINITE s ==> sum s (\x. if x IN s then f(x) else &0) = sum s f"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC [])

  let SUM_BOUND ← prove
   r"!s f b. FINITE s /\ (!x:A. x IN s ==> f(x) <= b)
           ==> sum s f <= &(CARD s) * b"
   (SIMP_TAC [← GSYM SUM_CONST, SUM_LE])

  let SUM_BOUND_GEN ← prove
   r"!s f b. FINITE s /\ ~(s = {}) /\ (!x:A. x IN s ==> f(x) <= b / &(CARD s))
           ==> sum s f <= b"
   (MESON_TAC [SUM_BOUND, REAL_DIV_LMUL, REAL_OF_NUM_EQ, HAS_SIZE_0,
               HAS_SIZE])

  let SUM_ABS_BOUND ← prove
   r"!s f b. FINITE s /\ (!x:A. x IN s ==> abs(f(x)) <= b)
           ==> abs(sum s f) <= &(CARD s) * b"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"sum s (\x:A. abs(f x))") THEN
    ASM_SIMP_TAC [SUM_BOUND, SUM_ABS])

  let SUM_BOUND_LT ← prove
   r"!s f b. FINITE s /\ (!x:A. x IN s ==> f x <= b) /\ (?x. x IN s /\ f x < b)
           ==> sum s f < &(CARD s) * b"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC (← q r"sum s (\x:A. b)") THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LT THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [],
      ASM_SIMP_TAC [SUM_CONST, REAL_LE_REFL]])

  let SUM_BOUND_LT_ALL ← prove
   r"!s f b. FINITE s /\ ~(s = {}) /\ (!x:A. x IN s ==> f(x) < b)
           ==> sum s f <  &(CARD s) * b"
   (MESON_TAC [MEMBER_NOT_EMPTY, REAL_LT_IMP_LE, SUM_BOUND_LT])

  let SUM_BOUND_LT_GEN ← prove
   r"!s f b. FINITE s /\ ~(s = {}) /\ (!x:A. x IN s ==> f(x) < b / &(CARD s))
           ==> sum s f < b"
   (MESON_TAC [SUM_BOUND_LT_ALL, REAL_DIV_LMUL, REAL_OF_NUM_EQ, HAS_SIZE_0,
               HAS_SIZE])

  let SUM_UNION_EQ ← prove
   r"!s t u:A->bool.
        FINITE u /\ s INTER t = {} /\ s UNION t = u
        ==> sum s f + sum t f = sum u f"
   (MESON_TAC [SUM_UNION, DISJOINT, FINITE_SUBSET, SUBSET_UNION])

  let SUM_EQ_SUPERSET ← prove
   r"!f s t:A->bool.
        FINITE t /\ t SUBSET s /\
        (!x. x IN t ==> (f x = g x)) /\
        (!x. x IN s /\ ~(x IN t) ==> (f(x) = &0))
        ==> (sum s f = sum t g)"
   (MESON_TAC [SUM_SUPERSET, SUM_EQ])

  let SUM_RESTRICT_SET ← prove
   r"!P s f. sum {x:A | x IN s /\ P x} f = sum s (\x. if P x then f x else &0)"
   (REWRITE_TAC [sum, ← GSYM NEUTRAL_REAL_ADD] THEN
    MATCH_MP_TAC ITERATE_RESTRICT_SET THEN REWRITE_TAC [MONOIDAL_REAL_ADD])

  let SUM_SUM_RESTRICT ← prove
   r"!(R:A->B->bool) f s t.
        FINITE s /\ FINITE t
        ==> (sum s (\x. sum {y | y IN t /\ R x y} (\y. f x y)) =
             sum t (\y. sum {x | x IN s /\ R x y} (\x. f x y)))"
   (REPEAT GEN_TAC THEN SIMP_TAC [SUM_RESTRICT_SET] THEN
    DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP SUM_SWAP th])))

  let CARD_EQ_SUM ← prove
   r"!s:A->bool. FINITE s ==> (&(CARD s) = sum s (\x. &1))"
   (SIMP_TAC [SUM_CONST, REAL_MUL_RID])

  let SUM_MULTICOUNT_GEN ← prove
   r"!R:A->B->bool s t k.
        FINITE s /\ FINITE t /\
        (!j. j IN t ==> (CARD {i | i IN s /\ R i j} = k(j)))
        ==> (sum s (\i. &(CARD {j | j IN t /\ R i j})) =
             sum t (\i. &(k i)))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [CONJ_ASSOC] THEN
    DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"sum s (\i:A. sum {j:B | j IN t /\ R i j} (\j. &1))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC [CARD_EQ_SUM, FINITE_RESTRICT],
      FIRST_ASSUM (fun th => tactic_of do pure (
        ONCE_REWRITE_TAC [← MATCH_MP SUM_SUM_RESTRICT th])) THEN
      MATCH_MP_TAC SUM_EQ THEN
      ASM_SIMP_TAC [SUM_CONST, FINITE_RESTRICT] THEN
      REWRITE_TAC [REAL_MUL_RID]])

  let SUM_MULTICOUNT ← prove
   r"!R:A->B->bool s t k.
        FINITE s /\ FINITE t /\
        (!j. j IN t ==> (CARD {i | i IN s /\ R i j} = k))
        ==> (sum s (\i. &(CARD {j | j IN t /\ R i j})) = &(k * CARD t))"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"sum t (\i:B. &k)") THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_MULTICOUNT_GEN THEN ASM_REWRITE_TAC [],
      ASM_SIMP_TAC [SUM_CONST, REAL_OF_NUM_MUL] THEN REWRITE_TAC [MULT_AC]])

  let SUM_IMAGE_GEN ← prove
   r"!f:A->B g s.
        FINITE s
        ==> sum s g =
            sum (IMAGE f s) (\y. sum {x | x IN s /\ f x = y} g)"
   (REWRITE_TAC [sum] THEN MATCH_MP_TAC ITERATE_IMAGE_GEN THEN
    REWRITE_TAC [MONOIDAL_REAL_ADD])

  let SUM_GROUP ← prove
   r"!f:A->B g s t.
        FINITE s /\ IMAGE f s SUBSET t
        ==> sum t (\y. sum {x | x IN s /\ f(x) = y} g) = sum s g"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A->B", ← q r"g:A->real", ← q r"s:A->bool"] SUM_IMAGE_GEN) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_SUPERSET THEN ASM_REWRITE_TAC [] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_0 THEN ASM SET_TAC [])

  let SUM_GROUP_RELATION ← prove
   r"!R:A->B->bool g s t.
         FINITE s /\
         (!x. x IN s ==> ?!y. y IN t /\ R x y)
         ==> sum t (\y. sum {x | x IN s /\ R x y} g) = sum s g"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"\x:A. @y:B. y IN t /\ R x y", ← q r"g:A->real",
                      ← q r"s:A->bool", ← q r"t:B->bool"]
          SUM_GROUP) THEN
    ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC [])

  let REAL_OF_NUM_SUM ← prove
   r"!f s:A->bool. FINITE s ==> (&(nsum s f) = sum s (\x. &(f x)))"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [SUM_CLAUSES, NSUM_CLAUSES, ← GSYM REAL_OF_NUM_ADD])

  -- The two SET_RULEs run (and print) right to left, as in OCaml.
  let SUM_SUBSET ← prove
   r"!u v f. FINITE u /\ FINITE v /\
           (!x. x IN (u DIFF v) ==> f(x) <= &0) /\
           (!x:A. x IN (v DIFF u) ==> &0 <= f(x))
           ==> sum u f <= sum v f"
   (← do
    let ra ← REAL_ARITH (← q r"&0 <= --x /\ &0 <= y ==> a + x <= a + y")
    let r2 ← SET_RULE (← q r"(u INTER v) UNION (v DIFF u) = v")
    let r1 ← SET_RULE (← q r"(u INTER v) UNION (u DIFF v) = u")
    pure
     (REPEAT STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"f:A->real", ← q r"u INTER v :A->bool"] SUM_UNION) THEN
      DISCH_THEN (fun th => tactic_of do pure (
        MP_TAC (← SPEC (← q r"v DIFF u :A->bool") th) THEN
        MP_TAC (← SPEC (← q r"u DIFF v :A->bool") th))) THEN
      REWRITE_TAC [r1, r2] THEN
      ASM_SIMP_TAC [FINITE_DIFF, FINITE_INTER] THEN
      REPEAT (ANTS_TAC THENL [SET_TAC [], DISCH_THEN SUBST1_TAC]) THEN
      MATCH_MP_TAC ra THEN
      ASM_SIMP_TAC [← GSYM SUM_NEG, FINITE_DIFF] THEN CONJ_TAC THEN
      MATCH_MP_TAC SUM_POS_LE THEN
      ASM_SIMP_TAC [FINITE_DIFF, REAL_LE_RNEG, REAL_ADD_LID]))

  let SUM_SUBSET_SIMPLE ← prove
   r"!u v f.
        FINITE v /\ u SUBSET v /\ (!x:A. x IN (v DIFF u) ==> &0 <= f(x))
        ==> sum u f <= sum v f"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_SUBSET THEN
    ASM_MESON_TAC [IN_DIFF, SUBSET, FINITE_SUBSET])

  let SUM_MUL_BOUND ← prove
   r"!a b s:A->bool.
        FINITE s /\ (!i. i IN s ==> &0 <= a i /\ &0 <= b i)
        ==> sum s (\i. a i * b i) <= sum s a * sum s b"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"i:A") THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC [] THEN GEN_REWRITE_TAC LAND_CONV [← GSYM SUM_SING] THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_SIMP_TAC [SING_SUBSET, IN_DIFF])

  let SUM_IMAGE_NONZERO ← prove
   r"!d:B->real i:A->B s.
    FINITE s /\
    (!x y. x IN s /\ y IN s /\ ~(x = y) /\ i x = i y ==> d(i x) = &0)
    ==> sum (IMAGE i s) d = sum s (d o i)"
   (REWRITE_TAC [← GSYM NEUTRAL_REAL_ADD, sum] THEN
    MATCH_MP_TAC ITERATE_IMAGE_NONZERO THEN REWRITE_TAC [MONOIDAL_REAL_ADD])

  let SUM_BIJECTION ← prove
   r"!f p s:A->bool.
        (!x. x IN s ==> p(x) IN s) /\
        (!y. y IN s ==> ?!x. x IN s /\ p(x) = y)
        ==> sum s f = sum s (f o p)"
   (REWRITE_TAC [sum] THEN MATCH_MP_TAC ITERATE_BIJECTION THEN
    REWRITE_TAC [MONOIDAL_REAL_ADD])

  let SUM_SUM_PRODUCT ← prove
   r"!s:A->bool t:A->B->bool x.
        FINITE s /\ (!i. i IN s ==> FINITE(t i))
        ==> sum s (\i. sum (t i) (x i)) =
            sum {i,j | i IN s /\ j IN t i} (\(i,j). x i j)"
   (REWRITE_TAC [sum] THEN MATCH_MP_TAC ITERATE_ITERATE_PRODUCT THEN
    REWRITE_TAC [MONOIDAL_REAL_ADD])

  let SUM_EQ_GENERAL ← prove
   r"!s:A->bool t:B->bool f g h.
        (!y. y IN t ==> ?!x. x IN s /\ h(x) = y) /\
        (!x. x IN s ==> h(x) IN t /\ g(h x) = f x)
        ==> sum s f = sum t g"
   (REWRITE_TAC [sum] THEN MATCH_MP_TAC ITERATE_EQ_GENERAL THEN
    REWRITE_TAC [MONOIDAL_REAL_ADD])

  let SUM_EQ_GENERAL_INVERSES ← prove
   r"!s:A->bool t:B->bool f g h k.
        (!y. y IN t ==> k(y) IN s /\ h(k y) = y) /\
        (!x. x IN s ==> h(x) IN t /\ k(h x) = x /\ g(h x) = f x)
        ==> sum s f = sum t g"
   (REWRITE_TAC [sum] THEN MATCH_MP_TAC ITERATE_EQ_GENERAL_INVERSES THEN
    REWRITE_TAC [MONOIDAL_REAL_ADD])

  let SUM_INJECTION ← prove
   r"!f p s:A->bool.
           FINITE s /\
           (!x. x IN s ==> p x IN s) /\
           (!x y. x IN s /\ y IN s /\ p x = p y ==> x = y)
           ==> sum s (f o p) = sum s f"
   (REWRITE_TAC [sum] THEN MATCH_MP_TAC ITERATE_INJECTION THEN
    REWRITE_TAC [MONOIDAL_REAL_ADD])

  let SUM_UNION_NONZERO ← prove
   r"!f s t:A->bool.
        FINITE s /\ FINITE t /\ (!x. x IN s INTER t ==> f(x) = &0)
        ==> sum (s UNION t) f = sum s f + sum t f"
   (REWRITE_TAC [sum, ← GSYM NEUTRAL_REAL_ADD] THEN
    MATCH_MP_TAC ITERATE_UNION_NONZERO THEN REWRITE_TAC [MONOIDAL_REAL_ADD])

  let SUM_UNIONS_NONZERO ← prove
   r"!f s. FINITE s /\ (!t:A->bool. t IN s ==> FINITE t) /\
         (!t1 t2 x. t1 IN s /\ t2 IN s /\ ~(t1 = t2) /\ x IN t1 /\ x IN t2
                    ==> f x = &0)
         ==> sum (UNIONS s) f = sum s (\t. sum t f)"
   (GEN_TAC THEN ONCE_REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [UNIONS_0, UNIONS_INSERT, SUM_CLAUSES, IN_INSERT] THEN
    MAP_EVERY X_GEN_TAC [← q r"t:A->bool", ← q r"s:(A->bool)->bool"] THEN
    DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
    ONCE_REWRITE_TAC [IMP_CONJ] THEN ASM_SIMP_TAC [SUM_CLAUSES] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN (SUBST_ALL_TAC o SYM)] THEN
    STRIP_TAC THEN MATCH_MP_TAC SUM_UNION_NONZERO THEN
    ASM_SIMP_TAC [FINITE_UNIONS, IN_INTER, IN_UNIONS] THEN ASM_MESON_TAC [])

  let SUM_CASES ← prove
   r"!s P f g. FINITE s
             ==> sum s (\x:A. if P x then f x else g x) =
                 sum {x | x IN s /\ P x} f + sum {x | x IN s /\ ~P x} g"
   (REWRITE_TAC [sum, ← GSYM NEUTRAL_REAL_ADD] THEN
    MATCH_MP_TAC ITERATE_CASES THEN REWRITE_TAC [MONOIDAL_REAL_ADD])

  let SUM_CASES_1 ← prove
   r"!s a:A. FINITE s /\ a IN s
           ==> sum s (\x. if x = a then y else f(x)) = sum s f + (y - f a)"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [SUM_CASES] THEN
    ASM_SIMP_TAC [← GSYM DELETE, SUM_DELETE] THEN
    ASM_SIMP_TAC [← SET_RULE (← q r"a IN s ==> {x | x IN s /\ x = a} = {a}")] THEN
    REWRITE_TAC [SUM_SING] THEN REAL_ARITH_TAC)

  let SUM_LE_INCLUDED ← prove
   r"!f:A->real g:B->real s t i.
        FINITE s /\ FINITE t /\
        (!y. y IN t ==> &0 <= g y) /\
        (!x. x IN s ==> ?y. y IN t /\ i y = x /\ f(x) <= g(y))
        ==> sum s f <= sum t g"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"sum (IMAGE (i:B->A) t) (\y. sum {x | x IN t /\ i x = y} g)") THEN
    CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      MATCH_MP_TAC (← GSYM SUM_IMAGE_GEN) THEN ASM_REWRITE_TAC []] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"sum s (\y. sum {x | x IN t /\ (i:B->A) x = y} g)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"x:A") THEN
      DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:A")) THEN
      ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"y:B") THEN
      STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"sum {y:B} g") THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC [SUM_SING], ALL_TAC],
      ALL_TAC] THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_SIMP_TAC [FINITE_IMAGE] THEN
    ASM_SIMP_TAC [SUM_POS_LE, FINITE_RESTRICT, IN_ELIM_THM] THEN
    ASM SET_TAC [])

  let SUM_IMAGE_LE ← prove
   r"!f:A->B g s.
        FINITE s /\
        (!x. x IN s ==> &0 <= g(f x))
        ==> sum (IMAGE f s) g <= sum s (g o f)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_LE_INCLUDED THEN
    ASM_SIMP_TAC [FINITE_IMAGE, FORALL_IN_IMAGE] THEN
    ASM_REWRITE_TAC [o_THM] THEN EXISTS_TAC (← q r"f:A->B") THEN
    MESON_TAC [REAL_LE_REFL])

  let SUM_CLOSED ← prove
   r"!P f:A->real s.
        P(&0) /\ (!x y. P x /\ P y ==> P(x + y)) /\ (!a. a IN s ==> P(f a))
        ==> P(sum s f)"
   (REPEAT STRIP_TAC THEN MP_TAC (← MATCH_MP ITERATE_CLOSED MONOIDAL_REAL_ADD) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"P:real->bool")) THEN
    ASM_SIMP_TAC [NEUTRAL_REAL_ADD, ← GSYM sum])

  let SUM_RELATED ← prove
   r"!R (f:A->real) g s.
        R (&0) (&0) /\
        (!m n m' n'. R m n /\ R m' n' ==> R (m + m') (n + n')) /\
        FINITE s /\ (!x. x IN s ==> R (f x) (g x))
        ==> R (sum s f) (sum s g)"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN REPEAT DISCH_TAC THEN
    MP_TAC (← ISPEC (← q r"R:real->real->bool")
      (← MATCH_MP ITERATE_RELATED MONOIDAL_REAL_ADD)) THEN
    ASM_REWRITE_TAC [← GSYM sum, NEUTRAL_REAL_ADD] THEN ASM_MESON_TAC [])

  let SUM_CLOSED_NONEMPTY ← prove
   r"!P f:A->real s.
        FINITE s /\ ~(s = {}) /\
        (!x y. P x /\ P y ==> P(x + y)) /\ (!a. a IN s ==> P(f a))
        ==> P(sum s f)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← MATCH_MP ITERATE_CLOSED_NONEMPTY MONOIDAL_REAL_ADD) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"P:real->bool")) THEN
    ASM_SIMP_TAC [NEUTRAL_REAL_ADD, ← GSYM sum])

  let SUM_RELATED_NONEMPTY ← prove
   r"!R (f:A->real) g s.
        (!m n m' n'. R m n /\ R m' n' ==> R (m + m') (n + n')) /\
        FINITE s /\ ~(s = {}) /\ (!x. x IN s ==> R (f x) (g x))
        ==> R (sum s f) (sum s g)"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN REPEAT DISCH_TAC THEN
    MP_TAC (← ISPEC (← q r"R:real->real->bool")
      (← MATCH_MP ITERATE_RELATED_NONEMPTY MONOIDAL_REAL_ADD)) THEN
    ASM_REWRITE_TAC [← GSYM sum, NEUTRAL_REAL_ADD] THEN ASM_MESON_TAC [])

  let REAL_OF_NUM_SUM_GEN ← prove
   r"!f s:A->bool.
       FINITE {i | i IN s /\ ~(f i = 0)} ==> &(nsum s f) = sum s (\x. &(f x))"
   (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [← GSYM SUM_SUPPORT, ← GSYM NSUM_SUPPORT] THEN
    REWRITE_TAC [support, NEUTRAL_ADD, NEUTRAL_REAL_ADD, REAL_OF_NUM_EQ] THEN
    ASM_SIMP_TAC [REAL_OF_NUM_SUM])

  return {
    SUM_IMAGE, SUM_SUPERSET, SUM_UNIV, SUM_UNION_RZERO, SUM_UNION_LZERO,
    SUM_RESTRICT, SUM_BOUND, SUM_BOUND_GEN, SUM_ABS_BOUND, SUM_BOUND_LT,
    SUM_BOUND_LT_ALL, SUM_BOUND_LT_GEN, SUM_UNION_EQ, SUM_EQ_SUPERSET,
    SUM_RESTRICT_SET, SUM_SUM_RESTRICT, CARD_EQ_SUM, SUM_MULTICOUNT_GEN,
    SUM_MULTICOUNT, SUM_IMAGE_GEN, SUM_GROUP, SUM_GROUP_RELATION,
    REAL_OF_NUM_SUM, SUM_SUBSET, SUM_SUBSET_SIMPLE, SUM_MUL_BOUND,
    SUM_IMAGE_NONZERO, SUM_BIJECTION, SUM_SUM_PRODUCT, SUM_EQ_GENERAL,
    SUM_EQ_GENERAL_INVERSES, SUM_INJECTION, SUM_UNION_NONZERO,
    SUM_UNIONS_NONZERO, SUM_CASES, SUM_CASES_1, SUM_LE_INCLUDED, SUM_IMAGE_LE,
    SUM_CLOSED, SUM_RELATED, SUM_CLOSED_NONEMPTY, SUM_RELATED_NONEMPTY,
    REAL_OF_NUM_SUM_GEN }

/- ---------------------------------------------------------------------- -/
/- Specialize them to sums over intervals of numbers.                     -/
/- ---------------------------------------------------------------------- -/

/-- iterate.ml 2599-2778: `sum` specialised to intervals of numbers, and
    partial summation.  `SUM_ADD_NUMSEG` through `SUM_COMBINE_L`. -/
structure IterateSum3 where
  /-- `SUM_ADD_NUMSEG` (iterate.ml 2602): additivity over a segment. -/
  SUM_ADD_NUMSEG : thm
  /-- `SUM_SUB_NUMSEG` (iterate.ml 2606): subtractivity over a segment. -/
  SUM_SUB_NUMSEG : thm
  /-- `SUM_LE_NUMSEG` (iterate.ml 2610): monotonicity over a segment. -/
  SUM_LE_NUMSEG : thm
  /-- `SUM_EQ_NUMSEG` (iterate.ml 2615): extensional equality over a segment. -/
  SUM_EQ_NUMSEG : thm
  /-- `SUM_ABS_NUMSEG` (iterate.ml 2620): the triangle inequality on a segment. -/
  SUM_ABS_NUMSEG : thm
  /-- `SUM_CONST_NUMSEG` (iterate.ml 2624): sum of a constant over a segment. -/
  SUM_CONST_NUMSEG : thm
  /-- `SUM_EQ_0_NUMSEG` (iterate.ml 2628): a zero summand over a segment. -/
  SUM_EQ_0_NUMSEG : thm
  /-- `SUM_TRIV_NUMSEG` (iterate.ml 2632): the empty-segment sum. -/
  SUM_TRIV_NUMSEG : thm
  /-- `SUM_POS_LE_NUMSEG` (iterate.ml 2636): nonnegativity over a segment. -/
  SUM_POS_LE_NUMSEG : thm
  /-- `SUM_POS_EQ_0_NUMSEG` (iterate.ml 2640): a zero nonnegative segment sum. -/
  SUM_POS_EQ_0_NUMSEG : thm
  /-- `SUM_SING_NUMSEG` (iterate.ml 2645): `sum(n..n) f = f n`. -/
  SUM_SING_NUMSEG : thm
  /-- `SUM_CLAUSES_NUMSEG` (iterate.ml 2649): the segment recursion clauses. -/
  SUM_CLAUSES_NUMSEG : thm
  /-- `SUM_CLAUSES_NUMSEG_LT` (iterate.ml 2656): the `< k` recursion clauses. -/
  SUM_CLAUSES_NUMSEG_LT : thm
  /-- `SUM_CLAUSES_NUMSEG_LE` (iterate.ml 2662): the `<= k` recursion clauses. -/
  SUM_CLAUSES_NUMSEG_LE : thm
  /-- `SUM_SWAP_NUMSEG` (iterate.ml 2668): exchange of two segment sums. -/
  SUM_SWAP_NUMSEG : thm
  /-- `SUM_ADD_SPLIT` (iterate.ml 2674): split a segment at `n`. -/
  SUM_ADD_SPLIT : thm
  /-- `SUM_OFFSET` (iterate.ml 2680): shift a segment by `p`. -/
  SUM_OFFSET : thm
  /-- `SUM_OFFSET_0` (iterate.ml 2686): normalise a segment to start at `0`. -/
  SUM_OFFSET_0 : thm
  /-- `SUM_CLAUSES_LEFT` (iterate.ml 2690): peel the left endpoint. -/
  SUM_CLAUSES_LEFT : thm
  /-- `SUM_CLAUSES_RIGHT` (iterate.ml 2695): peel the right endpoint. -/
  SUM_CLAUSES_RIGHT : thm
  /-- `SUM_PAIR` (iterate.ml 2700): pair consecutive terms. -/
  SUM_PAIR : thm
  /-- `SUM_REFLECT` (iterate.ml 2705): reflect a segment. -/
  SUM_REFLECT : thm
  /-- `REAL_OF_NUM_SUM_NUMSEG` (iterate.ml 2711): the segment transfer. -/
  REAL_OF_NUM_SUM_NUMSEG : thm
  /-- `SUM_PARTIAL_SUC` (iterate.ml 2719): summation by parts (successor). -/
  SUM_PARTIAL_SUC : thm
  /-- `SUM_PARTIAL_PRE` (iterate.ml 2735): summation by parts (predecessor). -/
  SUM_PARTIAL_PRE : thm
  /-- `SUM_DIFFS` (iterate.ml 2747): a telescoping sum. -/
  SUM_DIFFS : thm
  /-- `SUM_DIFFS_ALT` (iterate.ml 2755): the reversed telescoping sum. -/
  SUM_DIFFS_ALT : thm
  /-- `SUM_COMBINE_R` (iterate.ml 2762): combine adjacent segments (right). -/
  SUM_COMBINE_R : thm
  /-- `SUM_COMBINE_L` (iterate.ml 2770): combine adjacent segments (left). -/
  SUM_COMBINE_L : thm
  deriving Inhabited

@[nospecialize]
def setupIterateSum3 [HolBase]
    (MESON_TAC : List thm → tactic)
    (REAL_ARITH' : term → IO (Except String thm))
    (REAL_ARITH_TAC : tactic)
    (ARITH_TAC : tactic)
    (ASM_ARITH_TAC : tactic)
    (ARITH_RULE' : term → IO (Except String thm))
    (INDUCT_TAC : tactic)
    (IK3 : IterateKey3) (ISeg : IterateSegments)
    (IS1 : IterateSum1) (IS2 : IterateSum2)
    (FINITE_NUMSEG IN_NUMSEG NUMSEG_SING NUMSEG_ADD_SPLIT NUMSEG_OFFSET_IMAGE
     NUMSEG_LREC DISJOINT_NUMSEG LE_thm LE_TRANS NOT_LT NOT_LE LT_REFL
     SUC_SUB1 SUB_ADD ADD_CLAUSES ADD1 ADD_SUB EQ_ADD_RCANCEL
     o_DEF REAL_SUB_REFL REAL_MUL_RZERO
     REAL_NEG_SUB REAL_NEG_0 EXTENSION IN_INTER IN_UNION NOT_IN_EMPTY : thm) :
    ExceptT String IO IterateSum3 := do
  let REAL_ARITH (t : term) : ExceptT String IO thm := REAL_ARITH' t
  let ARITH_RULE (t : term) : ExceptT String IO thm := ARITH_RULE' t
  let LE := LE_thm
  let { ITERATE_CLAUSES_NUMSEG, ITERATE_CLAUSES_NUMSEG_LT, ITERATE_CLAUSES_NUMSEG_LE,
        ITERATE_PAIR, ITERATE_REFLECT, .. } := IK3
  let { CARD_NUMSEG, .. } := ISeg
  let { sum, NEUTRAL_REAL_ADD, MONOIDAL_REAL_ADD, SUM_CLAUSES, SUM_UNION, SUM_ADD,
        SUM_SUB, SUM_LE, SUM_EQ, SUM_ABS, SUM_CONST, SUM_EQ_0, SUM_POS_LE,
        SUM_POS_EQ_0, SUM_SING, SUM_SWAP, SUM_0, SUM_NEG, .. } := IS1
  let { SUM_IMAGE, SUM_UNION_EQ, REAL_OF_NUM_SUM, .. } := IS2

  let SUM_ADD_NUMSEG ← prove
   r"!f g m n. sum(m..n) (\i. f(i) + g(i)) = sum(m..n) f + sum(m..n) g"
   (SIMP_TAC [SUM_ADD, FINITE_NUMSEG])

  let SUM_SUB_NUMSEG ← prove
   r"!f g m n. sum(m..n) (\i. f(i) - g(i)) = sum(m..n) f - sum(m..n) g"
   (SIMP_TAC [SUM_SUB, FINITE_NUMSEG])

  let SUM_LE_NUMSEG ← prove
   r"!f g m n. (!i. m <= i /\ i <= n ==> f(i) <= g(i))
             ==> sum(m..n) f <= sum(m..n) g"
   (SIMP_TAC [SUM_LE, FINITE_NUMSEG, IN_NUMSEG])

  let SUM_EQ_NUMSEG ← prove
   r"!f g m n. (!i. m <= i /\ i <= n ==> (f(i) = g(i)))
             ==> (sum(m..n) f = sum(m..n) g)"
   (MESON_TAC [SUM_EQ, FINITE_NUMSEG, IN_NUMSEG])

  let SUM_ABS_NUMSEG ← prove
   r"!f m n. abs(sum(m..n) f) <= sum(m..n) (\i. abs(f i))"
   (SIMP_TAC [SUM_ABS, FINITE_NUMSEG])

  let SUM_CONST_NUMSEG ← prove
   r"!c m n. sum(m..n) (\n. c) = &((n + 1) - m) * c"
   (SIMP_TAC [SUM_CONST, FINITE_NUMSEG, CARD_NUMSEG])

  let SUM_EQ_0_NUMSEG ← prove
   r"!f m n. (!i. m <= i /\ i <= n ==> (f(i) = &0)) ==> (sum(m..n) f = &0)"
   (SIMP_TAC [SUM_EQ_0, IN_NUMSEG])

  let SUM_TRIV_NUMSEG ← prove
   r"!f m n. n < m ==> (sum(m..n) f = &0)"
   (MESON_TAC [SUM_EQ_0_NUMSEG, LE_TRANS, NOT_LT])

  let SUM_POS_LE_NUMSEG ← prove
   r"!m n f. (!p. m <= p /\ p <= n ==> &0 <= f(p)) ==> &0 <= sum(m..n) f"
   (SIMP_TAC [SUM_POS_LE, FINITE_NUMSEG, IN_NUMSEG])

  let SUM_POS_EQ_0_NUMSEG ← prove
   r"!f m n. (!p. m <= p /\ p <= n ==> &0 <= f(p)) /\ (sum(m..n) f = &0)
           ==> !p. m <= p /\ p <= n ==> (f(p) = &0)"
   (MESON_TAC [SUM_POS_EQ_0, FINITE_NUMSEG, IN_NUMSEG])

  let SUM_SING_NUMSEG ← prove
   r"!f n. sum(n..n) f = f(n)"
   (SIMP_TAC [SUM_SING, NUMSEG_SING])

  let SUM_CLAUSES_NUMSEG ← prove
   r"(!m. sum(m..0) f = if m = 0 then f(0) else &0) /\
   (!m n. sum(m..SUC n) f = if m <= SUC n then sum(m..n) f + f(SUC n)
                            else sum(m..n) f)"
   (MP_TAC (← MATCH_MP ITERATE_CLAUSES_NUMSEG MONOIDAL_REAL_ADD) THEN
    REWRITE_TAC [NEUTRAL_REAL_ADD, sum])

  let SUM_CLAUSES_NUMSEG_LT ← prove
   r"sum {i | i < 0} f = &0 /\
   (!k. sum {i | i < SUC k} f = sum {i | i < k} f + f k)"
   (MP_TAC (← MATCH_MP ITERATE_CLAUSES_NUMSEG_LT MONOIDAL_REAL_ADD) THEN
    REWRITE_TAC [NEUTRAL_REAL_ADD, sum])

  let SUM_CLAUSES_NUMSEG_LE ← prove
   r"sum {i | i <= 0} f = f 0 /\
   (!k. sum {i | i <= SUC k} f = sum {i | i <= k} f + f(SUC k))"
   (MP_TAC (← MATCH_MP ITERATE_CLAUSES_NUMSEG_LE MONOIDAL_REAL_ADD) THEN
    REWRITE_TAC [NEUTRAL_REAL_ADD, sum])

  let SUM_SWAP_NUMSEG ← prove
   r"!a b c d f.
     sum(a..b) (\i. sum(c..d) (f i)) = sum(c..d) (\j. sum(a..b) (\i. f i j))"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_SWAP THEN
    REWRITE_TAC [FINITE_NUMSEG])

  let SUM_ADD_SPLIT ← prove
   r"!f m n p.
        m <= n + 1 ==> (sum (m..(n+p)) f = sum(m..n) f + sum(n+1..n+p) f)"
   (SIMP_TAC [NUMSEG_ADD_SPLIT, SUM_UNION, DISJOINT_NUMSEG, FINITE_NUMSEG,
              ← ARITH_RULE (← q r"x < x + 1")])

  let SUM_OFFSET ← prove
   r"!p f m n. sum(m+p..n+p) f = sum(m..n) (\i. f(i + p))"
   (SIMP_TAC [NUMSEG_OFFSET_IMAGE, SUM_IMAGE,
              EQ_ADD_RCANCEL, FINITE_NUMSEG] THEN
    REWRITE_TAC [o_DEF])

  let SUM_OFFSET_0 ← prove
   r"!f m n. m <= n ==> (sum(m..n) f = sum(0..n-m) (\i. f(i + m)))"
   (SIMP_TAC [← GSYM SUM_OFFSET, ADD_CLAUSES, SUB_ADD])

  let SUM_CLAUSES_LEFT ← prove
   r"!f m n. m <= n ==> sum(m..n) f = f(m) + sum(m+1..n) f"
   (SIMP_TAC [← GSYM NUMSEG_LREC, SUM_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] THEN
    ARITH_TAC)

  let SUM_CLAUSES_RIGHT ← prove
   r"!f m n. 0 < n /\ m <= n ==> sum(m..n) f = sum(m..n-1) f + f(n)"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    SIMP_TAC [LT_REFL, SUM_CLAUSES_NUMSEG, SUC_SUB1])

  let SUM_PAIR ← prove
   r"!f m n. sum(2*m..2*n+1) f = sum(m..n) (\i. f(2*i) + f(2*i+1))"
   (MP_TAC (← MATCH_MP ITERATE_PAIR MONOIDAL_REAL_ADD) THEN
    REWRITE_TAC [sum, NEUTRAL_REAL_ADD])

  let SUM_REFLECT ← prove
   r"!x m n. sum(m..n) x = if n < m then &0 else sum(0..n-m) (\i. x(n - i))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [sum] THEN
    GEN_REWRITE_TAC LAND_CONV [← MATCH_MP ITERATE_REFLECT MONOIDAL_REAL_ADD] THEN
    REWRITE_TAC [NEUTRAL_REAL_ADD])

  let REAL_OF_NUM_SUM_NUMSEG ← prove
   r"!f m n. (&(nsum(m..n) f) = sum (m..n) (\i. &(f i)))"
   (SIMP_TAC [REAL_OF_NUM_SUM, FINITE_NUMSEG])

  /- ---------------------------------------------------------------------- -/
  /- Partial summation and other theorems specific to number segments.      -/
  /- ---------------------------------------------------------------------- -/

  let SUM_PARTIAL_SUC ← prove
   r"!f g m n.
        sum (m..n) (\k. f(k) * (g(k + 1) - g(k))) =
            if m <= n then f(n + 1) * g(n + 1) - f(m) * g(m) -
                           sum (m..n) (\k. g(k + 1) * (f(k + 1) - f(k)))
            else &0"
   (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [SUM_TRIV_NUMSEG, ← GSYM NOT_LE] THEN
    ASM_REWRITE_TAC [SUM_CLAUSES_NUMSEG] THENL
     [COND_CASES_TAC THEN ASM_SIMP_TAC [] THENL [REAL_ARITH_TAC, ASM_ARITH_TAC],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [LE]) THEN
    DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    ASM_SIMP_TAC [← GSYM NOT_LT, SUM_TRIV_NUMSEG, ← ARITH_RULE (← q r"n < SUC n")] THEN
    ASM_SIMP_TAC [← GSYM ADD1, ADD_CLAUSES] THEN REAL_ARITH_TAC)

  let SUM_PARTIAL_PRE ← prove
   r"!f g m n.
        sum (m..n) (\k. f(k) * (g(k) - g(k - 1))) =
            if m <= n then f(n + 1) * g(n) - f(m) * g(m - 1) -
                           sum (m..n) (\k. g k * (f(k + 1) - f(k)))
            else &0"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"f:num->real", ← q r"\k. (g:num->real)(k - 1)",
                      ← q r"m:num", ← q r"n:num"] SUM_PARTIAL_SUC) THEN
    REWRITE_TAC [ADD_SUB] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC [])

  let SUM_DIFFS ← prove
   r"!m n. sum(m..n) (\k. f(k) - f(k + 1)) =
          if m <= n then f(m) - f(n + 1) else &0"
   (ONCE_REWRITE_TAC [← REAL_ARITH (← q r"a - b = -- &1 * (b - a)")] THEN
    ONCE_REWRITE_TAC [SUM_PARTIAL_SUC] THEN
    REWRITE_TAC [REAL_SUB_REFL, REAL_MUL_RZERO, SUM_0] THEN
    REAL_ARITH_TAC)

  let SUM_DIFFS_ALT ← prove
   r"!m n. sum(m..n) (\k. f(k + 1) - f(k)) =
          if m <= n then f(n + 1) - f(m) else &0"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_NEG_SUB] THEN
    SIMP_TAC [SUM_NEG, SUM_DIFFS] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_NEG_SUB, REAL_NEG_0])

  let SUM_COMBINE_R ← prove
   r"!f m n p. m <= n + 1 /\ n <= p
             ==> sum(m..n) f + sum(n+1..p) f = sum(m..p) f"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_UNION_EQ THEN
    REWRITE_TAC [FINITE_NUMSEG, EXTENSION, IN_INTER, IN_UNION, NOT_IN_EMPTY,
                 IN_NUMSEG] THEN
    ASM_ARITH_TAC)

  let SUM_COMBINE_L ← prove
   r"!f m n p. 0 < n /\ m <= n /\ n <= p + 1
             ==> sum(m..n-1) f + sum(n..p) f = sum(m..p) f"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_UNION_EQ THEN
    REWRITE_TAC [FINITE_NUMSEG, EXTENSION, IN_INTER, IN_UNION, NOT_IN_EMPTY,
                 IN_NUMSEG] THEN
    ASM_ARITH_TAC)

  return {
    SUM_ADD_NUMSEG, SUM_SUB_NUMSEG, SUM_LE_NUMSEG, SUM_EQ_NUMSEG,
    SUM_ABS_NUMSEG, SUM_CONST_NUMSEG, SUM_EQ_0_NUMSEG, SUM_TRIV_NUMSEG,
    SUM_POS_LE_NUMSEG, SUM_POS_EQ_0_NUMSEG, SUM_SING_NUMSEG,
    SUM_CLAUSES_NUMSEG, SUM_CLAUSES_NUMSEG_LT, SUM_CLAUSES_NUMSEG_LE,
    SUM_SWAP_NUMSEG, SUM_ADD_SPLIT, SUM_OFFSET, SUM_OFFSET_0, SUM_CLAUSES_LEFT,
    SUM_CLAUSES_RIGHT, SUM_PAIR, SUM_REFLECT, REAL_OF_NUM_SUM_NUMSEG,
    SUM_PARTIAL_SUC, SUM_PARTIAL_PRE, SUM_DIFFS, SUM_DIFFS_ALT, SUM_COMBINE_R,
    SUM_COMBINE_L }

/- ---------------------------------------------------------------------- -/
/- Extend congruences to deal with sum. Note that we must have the eta    -/
/- redex or we'll get a loop since f(x) will lambda-reduce recursively.   -/
/- ---------------------------------------------------------------------- -/

/-- iterate.ml 2779-2854: `sum` congruences (with the eta requirement),
    `EXPAND_SUM_CONV`, and the special algebraic rearrangements. -/
structure IterateSum4 where
  /-- `SUM_CONG` (the anonymous `th`, iterate.ml 2783): the three congruence
      rules registered with `extend_basic_congs`.  The eta redex `\i. f i` is
      ESSENTIAL - without it `f(x)` would lambda-reduce recursively and loop
      (iterate.ml comment 2779-2781). -/
  SUM_CONG : thm
  /-- `EXPAND_SUM_CONV`'s `pth_0` (iterate.ml 2801): `n < m ==> sum(m..n) f
      = &0`. -/
  pth_0 : thm
  /-- `EXPAND_SUM_CONV`'s `pth_1` (iterate.ml 2802): `sum(m..m) f = f m`. -/
  pth_1 : thm
  /-- `EXPAND_SUM_CONV`'s `pth_2` (iterate.ml 2803): `m <= n ==> sum(m..n) f
      = f m + sum(m+1..n) f`. -/
  pth_2 : thm
  /-- `EXPAND_SUM_CONV` (iterate.ml 2799-2826): expand `sum(m..n) f` for
      numeral `m`, `n`.  A CONVERSION, so probed behaviourally. -/
  EXPAND_SUM_CONV : ioconv
  /-- `REAL_SUB_POW` (iterate.ml 2830): `x pow n - y pow n` factorisation. -/
  REAL_SUB_POW : thm
  /-- `REAL_SUB_POW_R1` (iterate.ml 2843): the `y = &1` case. -/
  REAL_SUB_POW_R1 : thm
  /-- `REAL_SUB_POW_L1` (iterate.ml 2849): the `x = &1` case. -/
  REAL_SUB_POW_L1 : thm
  deriving Inhabited

/-- `let rec conv tm = ...` inside EXPAND_SUM_CONV (iterate.ml 2803). -/
partial def expandSumConvImpl [HolBase]
    (NUM_LT_CONV NUM_LE_CONV NUM_ADD_CONV : ioconv)
    (pth_0 pth_1 pth_2 : thm) (ns_tm f_tm m_tm n_tm : term) : ioconv :=
  fun tm => ExceptT.run do
  let conv := expandSumConvImpl NUM_LT_CONV NUM_LE_CONV NUM_ADD_CONV
    pth_0 pth_1 pth_2 ns_tm f_tm m_tm n_tm
  let (smn, ftm) ← dest_comb tm
  let (s, mn) ← dest_comb smn
  if !(is_const s && (match dest_const s with | .ok (c, _) => c == "sum" | _ => false))
  then throw "EXPAND_SUM_CONV" else
  let (mtm, ntm) ← dest_binop ns_tm mn
  let m ← dest_numeral mtm
  let n ← dest_numeral ntm
  if n < m then
    let th1 ← INST [(ftm, f_tm), (mtm, m_tm), (ntm, n_tm)] pth_0
    MP th1 (← EQT_ELIM (← NUM_LT_CONV (← lhand (concl th1))))
  else if n == m then CONV_RULE (RAND_CONV (TRY_CONV BETA_CONV))
                                 (← INST [(ftm, f_tm), (mtm, m_tm)] pth_1)
  else
    let th1 ← INST [(ftm, f_tm), (mtm, m_tm), (ntm, n_tm)] pth_2
    let th2 ← MP th1 (← EQT_ELIM (← NUM_LE_CONV (← lhand (concl th1))))
    CONV_RULE (RAND_CONV (COMB2_CONV (RAND_CONV (TRY_CONV BETA_CONV))
     (LAND_CONV (LAND_CONV NUM_ADD_CONV) THENC conv))) th2

@[nospecialize]
def setupIterateSum4 [HolBase]
    (extend_basic_congs : List thm → IO Unit)
    (NUM_LT_CONV NUM_LE_CONV NUM_ADD_CONV : ioconv)
    (REAL_ARITH' : term → IO (Except String thm))
    (ARITH_RULE' : term → IO (Except String thm))
    (IS1 : IterateSum1) (_IS2 : IterateSum2) (IS3 : IterateSum3)
    (IN_ELIM_THM IN_NUMSEG REAL_POW_ONE REAL_MUL_RID REAL_MUL_LID REAL_MUL_LNEG
     REAL_NEG_SUB real_pow ADD1 LE_0 SUB_0 SUB_ADD SUB_REFL : thm) :
    ExceptT String IO IterateSum4 := do
  let REAL_ARITH (t : term) : ExceptT String IO thm := REAL_ARITH' t
  let ARITH_RULE (t : term) : ExceptT String IO thm := ARITH_RULE' t
  let { SUM_LMUL, SUM_EQ, .. } := IS1
  let { SUM_CLAUSES_LEFT, SUM_SING_NUMSEG, SUM_TRIV_NUMSEG, SUM_DIFFS_ALT, .. } := IS3

  -- `let th = prove (...) in extend_basic_congs (map SPEC_ALL (CONJUNCTS th))`
  -- (iterate.ml 2783); kept as the field SUM_CONG.
  let SUM_CONG ← prove
   r"(!f g s:A->bool.
        (!x. x IN s ==> f(x) = g(x))
        ==> sum s (\i. f(i)) = sum s g) /\
   (!f g a b. (!i. a <= i /\ i <= b ==> f(i) = g(i))
              ==> sum(a..b) (\i. f(i)) = sum(a..b) g) /\
   (!f g p. (!x. p x ==> f x = g x)
            ==> sum {y | p y} (\i. f(i)) = sum {y | p y} g)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    ASM_SIMP_TAC [IN_ELIM_THM, IN_NUMSEG])
  liftM (extend_basic_congs (← (CONJUNCTS SUM_CONG).mapM SPEC_ALL))

  /- Expand "sum (m..n) f" where m and n are numerals. -/

  let [pth_0, pth_1, pth_2] := CONJUNCTS (← prove
   r"(n < m ==> sum(m..n) f = &0) /\
     sum(m..m) f = f m /\
     (m <= n ==> sum (m..n) f = f m + sum (m + 1..n) f)"
    (REWRITE_TAC [SUM_CLAUSES_LEFT, SUM_SING_NUMSEG, SUM_TRIV_NUMSEG]))
    | throw "EXPAND_SUM_CONV"
  let ns_tm ← q r".."
  let f_tm ← q r"f:num->real"
  let m_tm ← q r"m:num"
  let n_tm ← q r"n:num"
  let EXPAND_SUM_CONV := expandSumConvImpl NUM_LT_CONV NUM_LE_CONV NUM_ADD_CONV
    pth_0 pth_1 pth_2 ns_tm f_tm m_tm n_tm

  /- ---------------------------------------------------------------------- -/
  /- Some special algebraic rearrangements.                                 -/
  /- ---------------------------------------------------------------------- -/

  let REAL_SUB_POW ← prove
   r"!x y n.
        1 <= n ==> x pow n - y pow n =
                   (x - y) * sum(0..n-1) (\i. x pow i * y pow (n - 1 - i))"
   (REWRITE_TAC [← GSYM SUM_LMUL] THEN
    REWRITE_TAC [← REAL_ARITH
     (← q r"(x - y) * (a * b):real = (x * a) * b - a * (y * b)")] THEN
    SIMP_TAC [← GSYM real_pow, ADD1, ← ARITH_RULE
      (← q r"1 <= n /\ x <= n - 1
       ==> n - 1 - x = n - (x + 1) /\ SUC(n - 1 - x) = n - x")] THEN
    REWRITE_TAC [SUM_DIFFS_ALT, LE_0] THEN
    SIMP_TAC [SUB_0, SUB_ADD, SUB_REFL, real_pow, REAL_MUL_LID, REAL_MUL_RID])

  let REAL_SUB_POW_R1 ← prove
   r"!x n. 1 <= n ==> x pow n - &1 = (x - &1) * sum(0..n-1) (\i. x pow i)"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o SPECL [← q r"x:real", ← q r"&1"] o MATCH_MP REAL_SUB_POW) THEN
    REWRITE_TAC [REAL_POW_ONE, REAL_MUL_RID])

  let REAL_SUB_POW_L1 ← prove
   r"!x n. 1 <= n ==> &1 - x pow n = (&1 - x) * sum(0..n-1) (\i. x pow i)"
   (ONCE_REWRITE_TAC [← GSYM REAL_NEG_SUB] THEN
    SIMP_TAC [REAL_SUB_POW_R1] THEN REWRITE_TAC [REAL_MUL_LNEG])

  return {
    SUM_CONG, pth_0, pth_1, pth_2, EXPAND_SUM_CONV, REAL_SUB_POW,
    REAL_SUB_POW_R1, REAL_SUB_POW_L1 }

/- ---------------------------------------------------------------------- -/
/- Some useful facts about real polynomial functions.                     -/
/- ---------------------------------------------------------------------- -/

/-- iterate.ml 2855-3108: real polynomial functions.  The `REAL_SUB_POLYFUN*`
    factorisations, the root-bound theorems, `polynomial_function` and its
    closure properties. -/
structure IterateSum5 where
  /-- `REAL_SUB_POLYFUN` (iterate.ml 2858): the polynomial difference formula. -/
  REAL_SUB_POLYFUN : thm
  /-- `REAL_SUB_POLYFUN_ALT` (iterate.ml 2878): the reindexed difference. -/
  REAL_SUB_POLYFUN_ALT : thm
  /-- `REAL_POLYFUN_ROOTBOUND` (iterate.ml 2893): a degree-`n` polynomial has
      at most `n` roots. -/
  REAL_POLYFUN_ROOTBOUND : thm
  /-- `REAL_POLYFUN_FINITE_ROOTS` (iterate.ml 2925): finitely many roots iff
      not identically zero. -/
  REAL_POLYFUN_FINITE_ROOTS : thm
  /-- `REAL_POLYFUN_EQ_0` (iterate.ml 2935): identically zero iff all
      coefficients zero. -/
  REAL_POLYFUN_EQ_0 : thm
  /-- `REAL_POLYFUN_EQ_CONST` (iterate.ml 2945): identically constant. -/
  REAL_POLYFUN_EQ_CONST : thm
  /-- `polynomial_function` (iterate.ml 2966): the definition. -/
  polynomial_function : thm
  /-- `POLYNOMIAL_FUNCTION_CONST` (iterate.ml 2969). -/
  POLYNOMIAL_FUNCTION_CONST : thm
  /-- `POLYNOMIAL_FUNCTION_ID` (iterate.ml 2975). -/
  POLYNOMIAL_FUNCTION_ID : thm
  /-- `POLYNOMIAL_FUNCTION_I` (iterate.ml 2981). -/
  POLYNOMIAL_FUNCTION_I : thm
  /-- `POLYNOMIAL_FUNCTION_ADD` (iterate.ml 2985). -/
  POLYNOMIAL_FUNCTION_ADD : thm
  /-- `POLYNOMIAL_FUNCTION_LMUL` (iterate.ml 3000). -/
  POLYNOMIAL_FUNCTION_LMUL : thm
  /-- `POLYNOMIAL_FUNCTION_RMUL` (iterate.ml 3008). -/
  POLYNOMIAL_FUNCTION_RMUL : thm
  /-- `POLYNOMIAL_FUNCTION_NEG` (iterate.ml 3012). -/
  POLYNOMIAL_FUNCTION_NEG : thm
  /-- `POLYNOMIAL_FUNCTION_SUB` (iterate.ml 3018). -/
  POLYNOMIAL_FUNCTION_SUB : thm
  /-- `POLYNOMIAL_FUNCTION_MUL` (iterate.ml 3023). -/
  POLYNOMIAL_FUNCTION_MUL : thm
  /-- `POLYNOMIAL_FUNCTION_SUM` (iterate.ml 3052). -/
  POLYNOMIAL_FUNCTION_SUM : thm
  /-- `POLYNOMIAL_FUNCTION_POW` (iterate.ml 3061). -/
  POLYNOMIAL_FUNCTION_POW : thm
  /-- `POLYNOMIAL_FUNCTION_INDUCT` (iterate.ml 3067). -/
  POLYNOMIAL_FUNCTION_INDUCT : thm
  /-- `POLYNOMIAL_FUNCTION_o` (iterate.ml 3084). -/
  POLYNOMIAL_FUNCTION_o : thm
  /-- `POLYNOMIAL_FUNCTION_FINITE_ROOTS` (iterate.ml 3093). -/
  POLYNOMIAL_FUNCTION_FINITE_ROOTS : thm
  deriving Inhabited

@[nospecialize]
def setupIterateSum5 [HolBase]
    (new_definition' : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic)
    (MESON' : List thm → term → IO (Except String thm))
    (SET_RULE' : term → IO (Except String thm))
    (REAL_ARITH' : term → IO (Except String thm))
    (REAL_ARITH_TAC : tactic)
    (ARITH_RULE' : term → IO (Except String thm))
    (ARITH_TAC : tactic)
    (ASM_ARITH_TAC : tactic)
    (INDUCT_TAC : tactic)
    (IS1 : IterateSum1) (IS2 : IterateSum2) (IS3 : IterateSum3) (IS4 : IterateSum4)
    (ISeg : IterateSegments)
    (FINITE_NUMSEG FINITE_EMPTY CARD_CLAUSES FINITE_RULES real_INFINITE INFINITE
     real_pow REAL_POW_ADD REAL_POW_1 REAL_MUL_RID REAL_MUL_LZERO REAL_MUL_ASSOC
     REAL_ADD_RID REAL_ADD_LID REAL_ADD_RDISTRIB REAL_ADD_LDISTRIB REAL_MUL_SYM
     REAL_ENTIRE REAL_SUB_0 REAL_SUB_RZERO REAL_SUB_REFL REAL_SUB_LDISTRIB
     REAL_NEG_NEG REAL_MUL_LNEG REAL_MUL_LID REAL_MUL_RZERO ARITH EQ_TRANS
     IMP_CONJ IMP_CONJ_ALT SWAP_FORALL_THM RIGHT_FORALL_IMP_THM
     LE_thm LE_0 LE_1 LE_REFL NOT_FORALL_THM NOT_IMP NOT_EXISTS_THM DE_MORGAN_THM
     LEFT_OR_DISTRIB LEFT_IMP_EXISTS_THM UNWIND_THM2 IN_SING IN_NUMSEG IN_ELIM_THM
     IN_ELIM_PAIR_THM FORALL_IN_GSPEC UNIV_GSPEC EMPTY_GSPEC FINITE_INSERT
     FINITE_INDUCT_STRONG FORALL_IN_INSERT COND_RAND COND_RATOR EXTENSION ETA_AX
     ADD1 ADD_CLAUSES ADD_SUB ADD_EQ_0 ARITH_EQ SUC_SUB1 ADD_SYM
     I_DEF o_DEF FUN_EQ_THM EXISTS_REFL LEFT_FORALL_IMP_THM CONTRAPOS_THM
     REAL_MUL_AC MEMBER_NOT_EMPTY real_sub : thm) :
    ExceptT String IO IterateSum5 := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let MESON (ths : List thm) (t : term) : ExceptT String IO thm := MESON' ths t
  let SET_RULE (t : term) : ExceptT String IO thm := SET_RULE' t
  let REAL_ARITH (t : term) : ExceptT String IO thm := REAL_ARITH' t
  let ARITH_RULE (t : term) : ExceptT String IO thm := ARITH_RULE' t
  let ASM_MESON_TAC := ASM MESON_TAC
  let LE := LE_thm
  let { NUMSEG_SING, .. } := ISeg
  let { SUM_CLAUSES, SUM_LMUL, SUM_RMUL, SUM_0, SUM_EQ, .. } := IS1
  let { SUM_EQ_GENERAL_INVERSES, SUM_SUM_PRODUCT, SUM_RESTRICT_SET, .. } := IS2
  let { SUM_SUB_NUMSEG, SUM_CLAUSES_LEFT, SUM_CLAUSES_NUMSEG, SUM_SING_NUMSEG,
        SUM_EQ_NUMSEG, SUM_ADD_NUMSEG, SUM_OFFSET, .. } := IS3
  let { REAL_SUB_POW, .. } := IS4

  let REAL_SUB_POLYFUN ← prove
   r"!a x y n.
    1 <= n
    ==> sum(0..n) (\i. a i * x pow i) - sum(0..n) (\i. a i * y pow i) =
        (x - y) *
        sum(0..n-1) (\j. sum(j+1..n) (\i. a i * y pow (i - j - 1)) * x pow j)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [← GSYM SUM_SUB_NUMSEG, ← GSYM REAL_SUB_LDISTRIB] THEN
    GEN_REWRITE_TAC LAND_CONV [← MATCH_MP SUM_CLAUSES_LEFT (← SPEC_ALL LE_0)] THEN
    REWRITE_TAC [REAL_SUB_REFL, real_pow, REAL_MUL_RZERO, REAL_ADD_LID] THEN
    SIMP_TAC [REAL_SUB_POW, ADD_CLAUSES] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"a * x * s:real = x * a * s")] THEN
    REWRITE_TAC [SUM_LMUL] THEN AP_TERM_TAC THEN
    SIMP_TAC [← GSYM SUM_LMUL, ← GSYM SUM_RMUL, SUM_SUM_PRODUCT, FINITE_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
    REPEAT (EXISTS_TAC (← q r"\(x:num,y:num). (y,x)")) THEN
    REWRITE_TAC [FORALL_IN_GSPEC, IN_ELIM_PAIR_THM, IN_NUMSEG] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"a - b - c:num = a - (b + c)"), ADD_SYM] THEN
    REWRITE_TAC [REAL_MUL_AC] THEN ARITH_TAC)

  let REAL_SUB_POLYFUN_ALT ← prove
   r"!a x y n.
    1 <= n
    ==> sum(0..n) (\i. a i * x pow i) - sum(0..n) (\i. a i * y pow i) =
        (x - y) *
        sum(0..n-1) (\j. sum(0..n-j-1) (\k. a(j+k+1) * y pow k) * x pow j)"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [REAL_SUB_POLYFUN] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC (← q r"j:num") THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
    MAP_EVERY EXISTS_TAC
     [← q r"\i. i - (j + 1)", ← q r"\k. j + k + 1"] THEN
    REWRITE_TAC [IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    TRY (BINOP_TAC THEN AP_TERM_TAC) THEN ASM_ARITH_TAC)

  -- The tactic's MESON rule runs (and prints) before its SET_RULE, as in OCaml.
  let REAL_POLYFUN_ROOTBOUND ← prove
   r"!n c. ~(!i. i IN 0..n ==> c i = &0)
         ==> FINITE {x | sum(0..n) (\i. c i * x pow i) = &0} /\
             CARD {x | sum(0..n) (\i. c i * x pow i) = &0} <= n"
   (← do
    let m2 ← MESON [FINITE_INSERT, CARD_CLAUSES,
                    ← ARITH_RULE (← q r"x <= n ==> SUC x <= SUC n /\ x <= SUC n")]
      (← q r"FINITE s /\ CARD s <= n
       ==> FINITE(r INSERT s) /\ CARD(r INSERT s) <= SUC n")
    let r1 ← SET_RULE (← q r"{x | x = c \/ P x} = c INSERT {x | P x}")
    pure
     (REWRITE_TAC [NOT_FORALL_THM, NOT_IMP] THEN INDUCT_TAC THENL
       [REWRITE_TAC [NUMSEG_SING, IN_SING, UNWIND_THM2, SUM_CLAUSES_NUMSEG] THEN
        SIMP_TAC [real_pow, REAL_MUL_RID, EMPTY_GSPEC, CARD_CLAUSES, FINITE_EMPTY,
                  LE_REFL],
        X_GEN_TAC (← q r"c:num->real") THEN REWRITE_TAC [IN_NUMSEG] THEN
        DISCH_TAC THEN ASM_CASES_TAC (← q r"(c:num->real) (SUC n) = &0") THENL
         [ASM_SIMP_TAC [SUM_CLAUSES_NUMSEG, LE_0, REAL_MUL_LZERO, REAL_ADD_RID] THEN
          REWRITE_TAC [LE, LEFT_OR_DISTRIB] THEN DISJ2_TAC THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC [IN_NUMSEG, LE],
          ASM_CASES_TAC (← q r"{x | sum (0..SUC n) (\i. c i * x pow i) = &0} = {}") THEN
          ASM_REWRITE_TAC [FINITE_RULES, CARD_CLAUSES, LE_0] THEN
          FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
          REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
          X_GEN_TAC (← q r"r:real") THEN DISCH_TAC THEN
          MP_TAC (← GEN (← q r"x:real") (← ISPECL [← q r"c:num->real", ← q r"x:real",
            ← q r"r:real", ← q r"SUC n"] REAL_SUB_POLYFUN)) THEN
          ASM_REWRITE_TAC [← ARITH_RULE (← q r"1 <= SUC n"), REAL_SUB_RZERO] THEN
          DISCH_THEN (fun th => REWRITE_TAC [th, REAL_ENTIRE, REAL_SUB_0]) THEN
          REWRITE_TAC [r1] THEN
          MATCH_MP_TAC m2 THEN
          REWRITE_TAC [SUC_SUB1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          EXISTS_TAC (← q r"n:num") THEN REWRITE_TAC [IN_NUMSEG, ADD1, LE_REFL, LE_0] THEN
          REWRITE_TAC [SUM_SING_NUMSEG, ← ARITH_RULE (← q r"(n + 1) - n - 1 = 0")] THEN
          ASM_REWRITE_TAC [← GSYM ADD1, real_pow, REAL_MUL_RID]]]))

  let REAL_POLYFUN_FINITE_ROOTS ← prove
   r"!n c. FINITE {x | sum(0..n) (\i. c i * x pow i) = &0} <=>
         ?i. i IN 0..n /\ ~(c i = &0)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← TAUT (← q r"a /\ ~b <=> ~(a ==> b)")] THEN
    REWRITE_TAC [← GSYM NOT_FORALL_THM] THEN EQ_TAC THEN
    SIMP_TAC [REAL_POLYFUN_ROOTBOUND] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    SIMP_TAC [REAL_MUL_LZERO, SUM_0] THEN
    REWRITE_TAC [← SET_RULE (← q r"{x | T} = (:real)"), real_INFINITE, ← GSYM INFINITE])

  let REAL_POLYFUN_EQ_0 ← prove
   r"!n c. (!x. sum(0..n) (\i. c i * x pow i) = &0) <=>
         (!i. i IN 0..n ==> c i = &0)"
   (REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [GEN_REWRITE_TAC I [← TAUT (← q r"p <=> ~ ~p")] THEN DISCH_THEN (MP_TAC o MATCH_MP
       REAL_POLYFUN_ROOTBOUND) THEN
      ASM_REWRITE_TAC [real_INFINITE, ← GSYM INFINITE, DE_MORGAN_THM,
                       ← SET_RULE (← q r"{x | T} = (:real)")],
      ASM_SIMP_TAC [IN_NUMSEG, LE_0, REAL_MUL_LZERO, SUM_0]])

  let REAL_POLYFUN_EQ_CONST ← prove
   r"!n c k. (!x. sum(0..n) (\i. c i * x pow i) = k) <=>
           c 0 = k /\ (!i. i IN 1..n ==> c i = &0)"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     (← q r"!x. sum(0..n) (\i. (if i = 0 then c 0 - k else c i) * x pow i) = &0") THEN
    CONJ_TAC THENL
     [SIMP_TAC [SUM_CLAUSES_LEFT, LE_0, real_pow, REAL_MUL_RID] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"(c - k) + s = &0 <=> c + s = k")] THEN
      AP_TERM_TAC THEN ABS_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN GEN_TAC THEN
      REWRITE_TAC [IN_NUMSEG] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [ARITH],
      REWRITE_TAC [REAL_POLYFUN_EQ_0, IN_NUMSEG, LE_0] THEN
      GEN_REWRITE_TAC LAND_CONV [← MESON []
       (← q r"(!n. P n) <=> P 0 /\ (!n. ~(n = 0) ==> P n)")] THEN
      SIMP_TAC [LE_0, REAL_SUB_0] THEN MESON_TAC [LE_1]])

  /- ---------------------------------------------------------------------- -/
  /- A general notion of polynomial function.                               -/
  /- ---------------------------------------------------------------------- -/

  let polynomial_function ← new_definition
   r"polynomial_function p <=> ?m c. !x. p x = sum(0..m) (\i. c i * x pow i)"

  let POLYNOMIAL_FUNCTION_CONST ← prove
   r"!c. polynomial_function (\x. c)"
   (GEN_TAC THEN REWRITE_TAC [polynomial_function] THEN
    MAP_EVERY EXISTS_TAC [← q r"0", ← q r"(\i. c):num->real"] THEN
    REWRITE_TAC [SUM_SING_NUMSEG, real_pow, REAL_MUL_RID])

  let POLYNOMIAL_FUNCTION_ID ← prove
   r"polynomial_function (\x. x)"
   (REWRITE_TAC [polynomial_function] THEN
    MAP_EVERY EXISTS_TAC [← q r"SUC 0", ← q r"\i. if i = 1 then &1 else &0"] THEN
    REWRITE_TAC [SUM_CLAUSES_NUMSEG, LE_0, ARITH] THEN REAL_ARITH_TAC)

  let POLYNOMIAL_FUNCTION_I ← prove
   r"polynomial_function I"
   (REWRITE_TAC [I_DEF, POLYNOMIAL_FUNCTION_ID])

  let POLYNOMIAL_FUNCTION_ADD ← prove
   r"!p q. polynomial_function p /\ polynomial_function q
         ==> polynomial_function (\x. p x + q x)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [IMP_CONJ, polynomial_function, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"m:num", ← q r"a:num->real"] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"b:num->real"] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"MAX m n") THEN EXISTS_TAC
     (← q r"\i:num. (if i <= m then a i else &0) + (if i <= n then b i else &0)") THEN
    GEN_TAC THEN REWRITE_TAC [REAL_ADD_RDISTRIB, SUM_ADD_NUMSEG] THEN
    REWRITE_TAC [COND_RAND, COND_RATOR, REAL_MUL_LZERO] THEN
    REWRITE_TAC [← GSYM SUM_RESTRICT_SET] THEN BINOP_TAC THEN
    BINOP_TAC THEN REWRITE_TAC [] THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_NUMSEG] THEN ARITH_TAC)

  let POLYNOMIAL_FUNCTION_LMUL ← prove
   r"!p c. polynomial_function p ==> polynomial_function (\x. c * p x)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [IMP_CONJ, polynomial_function, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"a:num->real"] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [← q r"n:num", ← q r"\i. c * (a:num->real) i"] THEN
    ASM_REWRITE_TAC [SUM_LMUL, ← GSYM REAL_MUL_ASSOC])

  let POLYNOMIAL_FUNCTION_RMUL ← prove
   r"!p c. polynomial_function p ==> polynomial_function (\x. p x * c)"
   (ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [POLYNOMIAL_FUNCTION_LMUL])

  let POLYNOMIAL_FUNCTION_NEG ← prove
   r"!p. polynomial_function(\x. --(p x)) <=> polynomial_function p"
   (GEN_TAC THEN EQ_TAC THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"--(&1)") o MATCH_MP POLYNOMIAL_FUNCTION_LMUL) THEN
    REWRITE_TAC [REAL_MUL_LNEG, REAL_MUL_LID, ETA_AX, REAL_NEG_NEG])

  let POLYNOMIAL_FUNCTION_SUB ← prove
   r"!p q. polynomial_function p /\ polynomial_function q
         ==> polynomial_function (\x. p x - q x)"
   (SIMP_TAC [real_sub, POLYNOMIAL_FUNCTION_NEG, POLYNOMIAL_FUNCTION_ADD])

  let POLYNOMIAL_FUNCTION_MUL ← prove
   r"!p q. polynomial_function p /\ polynomial_function q
         ==> polynomial_function (\x. p x * q x)"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN DISCH_TAC THEN
    GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV) [polynomial_function] THEN
    SIMP_TAC [LEFT_IMP_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [← MESON [] (← q r"(!q m c. P q m c) <=> (!m c q. P q m c)")] THEN
    ONCE_REWRITE_TAC [← GSYM FUN_EQ_THM] THEN
    REWRITE_TAC [LEFT_FORALL_IMP_THM, EXISTS_REFL] THEN
    INDUCT_TAC THEN
    ASM_SIMP_TAC [SUM_SING_NUMSEG, real_pow, POLYNOMIAL_FUNCTION_RMUL] THEN
    X_GEN_TAC (← q r"c:num->real") THEN SIMP_TAC [SUM_CLAUSES_LEFT, LE_0, ADD1] THEN
    REWRITE_TAC [REAL_ADD_LDISTRIB, real_pow] THEN
    MATCH_MP_TAC POLYNOMIAL_FUNCTION_ADD THEN
    ASM_SIMP_TAC [POLYNOMIAL_FUNCTION_RMUL] THEN
    REWRITE_TAC [← SPEC (← q r"1") SUM_OFFSET] THEN
    REWRITE_TAC [REAL_POW_ADD, REAL_POW_1, REAL_MUL_ASSOC, SUM_RMUL] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"\i. (c:num->real)(i + 1)")) THEN
    ABBREV_TAC (← q r"q = \x. p x * sum (0..m) (\i. c (i + 1) * x pow i)") THEN
    RULE_ASSUM_TAC (REWRITE_RULE [FUN_EQ_THM]) THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [polynomial_function, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"a:num->real"] THEN STRIP_TAC THEN
    EXISTS_TAC (← q r"n + 1") THEN
    EXISTS_TAC (← q r"\i. if i = 0 then &0 else (a:num->real)(i - 1)") THEN
    SIMP_TAC [SUM_CLAUSES_LEFT, LE_0] THEN
    ASM_REWRITE_TAC [← SPEC (← q r"1") SUM_OFFSET, ADD_EQ_0, ARITH_EQ, ADD_SUB] THEN
    REWRITE_TAC [REAL_POW_ADD, REAL_MUL_ASSOC, SUM_RMUL] THEN REAL_ARITH_TAC)

  let POLYNOMIAL_FUNCTION_SUM ← prove
   r"!s:A->bool p.
        FINITE s /\ (!i. i IN s ==> polynomial_function(\x. p x i))
        ==> polynomial_function (\x. sum s (p x))"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [SUM_CLAUSES, POLYNOMIAL_FUNCTION_CONST] THEN
    SIMP_TAC [FORALL_IN_INSERT, POLYNOMIAL_FUNCTION_ADD])

  let POLYNOMIAL_FUNCTION_POW ← prove
   r"!p n. polynomial_function p ==> polynomial_function (\x. p x pow n)"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    INDUCT_TAC THEN
    ASM_SIMP_TAC [real_pow, POLYNOMIAL_FUNCTION_CONST, POLYNOMIAL_FUNCTION_MUL])

  let POLYNOMIAL_FUNCTION_INDUCT ← prove
   r"!P. P (\x. x) /\ (!c. P (\x. c)) /\
      (!p q. P p /\ P q ==> P (\x. p x + q x)) /\
      (!p q. P p /\ P q ==> P (\x. p x * q x))
      ==> !p. polynomial_function p ==> P p"
   (GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC [polynomial_function, LEFT_IMP_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [← MESON [] (← q r"(!q m c. P q m c) <=> (!m c q. P q m c)")] THEN
    ONCE_REWRITE_TAC [← GSYM FUN_EQ_THM] THEN
    SIMP_TAC [LEFT_FORALL_IMP_THM, EXISTS_REFL] THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [SUM_SING_NUMSEG, real_pow] THEN
    GEN_TAC THEN SIMP_TAC [SUM_CLAUSES_LEFT, ADD1, LE_0] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [real_pow] THEN
    REWRITE_TAC [← SPEC (← q r"1") SUM_OFFSET] THEN
    REWRITE_TAC [REAL_POW_ADD, REAL_POW_1, REAL_MUL_ASSOC, SUM_RMUL] THEN
    ASM_SIMP_TAC [])

  let POLYNOMIAL_FUNCTION_o ← prove
   r"!p q. polynomial_function p /\ polynomial_function q
         ==> polynomial_function (p o q)"
   (ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    REWRITE_TAC [IMP_CONJ_ALT, RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC POLYNOMIAL_FUNCTION_INDUCT THEN
    SIMP_TAC [o_DEF, POLYNOMIAL_FUNCTION_ADD, POLYNOMIAL_FUNCTION_MUL] THEN
    ASM_REWRITE_TAC [ETA_AX, POLYNOMIAL_FUNCTION_CONST])

  let POLYNOMIAL_FUNCTION_FINITE_ROOTS ← prove
   r"!p a. polynomial_function p
         ==> (FINITE {x | p x = a} <=> ~(!x. p x = a))"
   (ONCE_REWRITE_TAC [← GSYM REAL_SUB_0] THEN
    SUBGOAL_THEN
     (← q r"!p. polynomial_function p ==> (FINITE {x | p x = &0} <=> ~(!x. p x = &0))")
     (fun th =>
        SIMP_TAC [th, POLYNOMIAL_FUNCTION_SUB, POLYNOMIAL_FUNCTION_CONST]) THEN
    GEN_TAC THEN REWRITE_TAC [polynomial_function] THEN
    STRIP_TAC THEN EQ_TAC THEN ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THENL
     [SIMP_TAC [UNIV_GSPEC, ← GSYM INFINITE, real_INFINITE],
      ASM_REWRITE_TAC [REAL_POLYFUN_FINITE_ROOTS] THEN
      SIMP_TAC [NOT_EXISTS_THM, ← TAUT (← q r"~(p /\ ~q) <=> p ==> q")] THEN
      REWRITE_TAC [REAL_MUL_LZERO, SUM_0]])

  return {
    REAL_SUB_POLYFUN, REAL_SUB_POLYFUN_ALT, REAL_POLYFUN_ROOTBOUND,
    REAL_POLYFUN_FINITE_ROOTS, REAL_POLYFUN_EQ_0, REAL_POLYFUN_EQ_CONST,
    polynomial_function, POLYNOMIAL_FUNCTION_CONST, POLYNOMIAL_FUNCTION_ID,
    POLYNOMIAL_FUNCTION_I, POLYNOMIAL_FUNCTION_ADD, POLYNOMIAL_FUNCTION_LMUL,
    POLYNOMIAL_FUNCTION_RMUL, POLYNOMIAL_FUNCTION_NEG, POLYNOMIAL_FUNCTION_SUB,
    POLYNOMIAL_FUNCTION_MUL, POLYNOMIAL_FUNCTION_SUM, POLYNOMIAL_FUNCTION_POW,
    POLYNOMIAL_FUNCTION_INDUCT, POLYNOMIAL_FUNCTION_o,
    POLYNOMIAL_FUNCTION_FINITE_ROOTS }

/- ---------------------------------------------------------------------- -/
/- Make natural numbers the default again.                                -/
/- (`prioritize_num()` at iterate.ml 3112 is run by Session.)             -/
/- ---------------------------------------------------------------------- -/

end HolMath.Iterate
