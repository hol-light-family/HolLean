/- ---------------------------------------------------------------------- -/
/- File: Define.lean
Automated support for general recursive definitions.
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026

  This is the last file `hol_lib.ml` loads.  Nothing follows
  `loads "define.ml"` except `check_axioms ()`, which asserts that only
  INFINITY_AX, SELECT_AX and ETA_AX were ever introduced, so this file
  completes the HOL Light core library.

  What it provides.  `define` (957) is the user-facing entry point: it
  accepts a general recursive definition, written as a conjunction of
  clauses that may use pattern matching, and discharges the proof
  obligations automatically.  Underneath, the file proves that a
  definition is *admissible* (the recursive calls are on smaller
  arguments), reduces the clauses to a single `CASEWISE` application, and
  then appeals to wellfounded recursion.

  The file is ML-dominated, like impconv.ml and normalizer.ml, and its
  shape is decided by one enormous binding.  define.ml 467-469 is
      let instantiate_casewise_recursion,
          pure_prove_recursive_function_exists,
          prove_general_recursive_function_exists =
  a single `let` binding three names whose body runs to line 953 - 487
  lines, nearly half the file.  Its seven documented sub-sections (472,
  528, 546, 599, 692, 811, 854) are all inside that one binding, so they
  are local helpers, not top-level names.

  Prerequisites.  The pattern-matching constants this file leans on most
  heavily - `_MATCH`, `GEQ`, `_SEQPATTERN`, `_UNGUARDED_PATTERN`,
  `_GUARDED_PATTERN` - come from `pair.ml` 29-38, and on our side they are
  fields of `HolMath.Pair.PairDefs`, with the leading underscores dropped
  from the Lean field names: `SEQPATTERN`, `UNGUARDED_PATTERN`,
  `GUARDED_PATTERN`, `MATCH`, plus `GEQ_DEF`.  `list_RECURSION` and
  `WF_REC_TAIL_GENERAL` are bare Session accessors.

  Section map (define.ml line ranges):
      10- 25  CASEWISE_DEF, the constant supporting casewise definitions
      26- 47  conditions for all the clauses of a casewise definition to hold
      48- 69  admissible, tailadmissible, superadmissible
      70- 78  a lemma (MATCH_SEQPATTERN)
      79-222  the admissibility combinators - twenty theorems
     223-356  superadmissible generalizations where applicable.  The OCaml
              carries an unusually long explanatory comment here: the
              "higher type" route cannot be taken in ADMISSIBLE_MATCH
              because that is not a context where tail recursion makes
              sense, and there is "some delicacy over assessing
              welldefinedness"
     357-463  combining the general WF/tail-recursion theorem with casewise
              definitions
     464-953  the main suite, one binding, three names:
              472-527  basic simplification of welldefinedness conjunctions
              528-545  simplifying an existential question about a pattern
              546-598  hacking a proforma to introduce pairing/pattern vars
              599-691  hack and apply
              692-810  instantiating the casewise recursion theorem, with a
                       first attempt at simplifying the distinctness clause
              811-853  justifying the existence assertion and removing
                       side-conditions
              854-953  the same, but guessing the wellfoundedness hypothesis
     954-1028  the simple `define` function
-/

import HolMath.Cart
import HolMath.Base

namespace HolMath.Define

set_option maxRecDepth 8000

/- ---------------------------------------------------------------------- -/
/- Constant supporting casewise definitions.  (define.ml 10-47)            -/
/- ---------------------------------------------------------------------- -/

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/-- define.ml 10-47: the `CASEWISE` constant supporting casewise definitions
    and the three theorems giving the conditions for all clauses of a casewise
    definition to hold.

    `CASEWISE_DEF` (13) is the file's ONLY `new_recursive_definition`, taken
    over `list_RECURSION`.  `new_recursive_definition` is a SIDE-EFFECTING
    kernel primitive (it introduces a constant via `new_specification`), so -
    exactly as cart.ml threads `new_definition`/`new_type_definition` - it is
    passed into this pure HolMath layer as a PARAMETER from Session (its exact
    signature is `ax : thm -> tm : term -> IO (Except String thm)`, `ax` being
    the recursion theorem `list_RECURSION`).  This layer carries ZERO `unsafe`.

    `CASEWISE` (19), `CASEWISE_CASES` (29) and `CASEWISE_WORKS` (39) are plain
    `prove`s.  Everything later in define.ml rests on these, so the statements
    are transcribed VERBATIM.

    Depends on `list_RECURSION` and `list_INDUCT` (bare Session accessors), the
    pair theorems `FORALL_PAIR_THM`/`PAIR_EQ`, the list theorems
    `MEM`/`ALL_MEM` (the `ALL` constant appears only symbolically in the
    `CASEWISE_WORKS` statement, never as a rewrite, so it is NOT threaded), and
    the decision procedures `MESON_TAC`/`ASM_MESON_TAC`.  ZERO `o`-compositions
    in the range; all four proofs are straight `THEN` chains. -/
structure DefineCasewise where
  /-- `CASEWISE_DEF` (define.ml 13): the primitive-recursive definition
      `(CASEWISE [] f x = @y. T) /\ (CASEWISE (CONS h t) f x = if ?y. FST h y =
      x then SND h f (@y. FST h y = x) else CASEWISE t f x)`, via
      `new_recursive_definition list_RECURSION`. -/
  CASEWISE_DEF : thm
  /-- `CASEWISE` (define.ml 19): the destructured-clause form
      `(CASEWISE [] f x = @y. T) /\ (CASEWISE (CONS (s,t) clauses) f x = if ?y.
      s y = x then t f (@y. s y = x) else CASEWISE clauses f x)`.
      `REWRITE_TAC[CASEWISE_DEF]`. -/
  CASEWISE : thm
  /-- `CASEWISE_CASES` (define.ml 29): the case analysis
      `!clauses c x. (?s t a. MEM (s,t) clauses /\ (s a = x) /\ (CASEWISE
      clauses c x = t c a)) \/ ~(?s t a. MEM (s,t) clauses /\ (s a = x)) /\
      (CASEWISE clauses c x = @y. T)`.  `MATCH_MP_TAC list_INDUCT THEN
      REWRITE_TAC[MEM; CASEWISE; FORALL_PAIR_THM; PAIR_EQ] THEN REPEAT STRIP_TAC
      THEN COND_CASES_TAC THEN ASM_MESON_TAC[]`. -/
  CASEWISE_CASES : thm
  /-- `CASEWISE_WORKS` (define.ml 39): the conditions for all clauses to hold,
      `!clauses c:C. (!s t s' t' x y. MEM (s,t) clauses /\ MEM (s',t') clauses
      /\ (s x = s' y) ==> (t c x = t' c y)) ==> ALL (\(s:P->A,t). !x. CASEWISE
      clauses c (s x) :B = t c x) clauses`.  `REWRITE_TAC[GSYM ALL_MEM;
      FORALL_PAIR_THM] THEN MESON_TAC[CASEWISE_CASES]`. -/
  CASEWISE_WORKS : thm
  deriving Inhabited

/-- define.ml 9-45: the constant supporting casewise definitions, and the
    conditions for all its clauses to hold. -/
@[nospecialize]
def setupDefineCasewise [HolBase]
    (new_recursive_definition' : thm → term → IO (Except String thm))
    (MESON_TAC ASM_MESON_TAC : List thm → tactic)
    (list_RECURSION list_INDUCT : thm)
    (MEM ALL_MEM FORALL_PAIR_THM PAIR_EQ : thm) :
    ExceptT String IO DefineCasewise := do
  let new_recursive_definition (ax : thm) (s : String) : ExceptT String IO thm := do
    new_recursive_definition' ax (← q s)

  /- Constant supporting casewise definitions. -/

  let CASEWISE_DEF ← new_recursive_definition list_RECURSION
   r"(CASEWISE [] f x = @y. T) /\
  (CASEWISE (CONS h t) f x =
        if ?y. FST h y = x then SND h f (@y. FST h y = x)
        else CASEWISE t f x)"

  let CASEWISE ← prove
   r"(CASEWISE [] f x = @y. T) /\
   (CASEWISE (CONS (s,t) clauses) f x =
        if ?y. s y = x then t f (@y. s y = x) else CASEWISE clauses f x)"
   (REWRITE_TAC [CASEWISE_DEF])

  /- Conditions for all the clauses in a casewise definition to hold. -/

  let CASEWISE_CASES ← prove
   r"!clauses c x.
    (?s t a. MEM (s,t) clauses /\ (s a = x) /\
             (CASEWISE clauses c x = t c a)) \/
    ~(?s t a. MEM (s,t) clauses /\ (s a = x)) /\
    (CASEWISE clauses c x = @y. T)"
   (MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [MEM, CASEWISE, FORALL_PAIR_THM, PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC [])

  let CASEWISE_WORKS ← prove
   r"!clauses c:C.
     (!s t s' t' x y. MEM (s,t) clauses /\ MEM (s',t') clauses /\ (s x = s' y)
                      ==> (t c x = t' c y))
     ==> ALL (\(s:P->A,t). !x. CASEWISE clauses c (s x) :B = t c x) clauses"
   (REWRITE_TAC [← GSYM ALL_MEM, FORALL_PAIR_THM] THEN
    MESON_TAC [CASEWISE_CASES])

  return {
    CASEWISE_DEF, CASEWISE, CASEWISE_CASES, CASEWISE_WORKS }

/-- define.ml 48-78: the three definitions on which the entire file rests -
    `admissible` (51), `tailadmissible` (56), `superadmissible` (65) - and
    the `MATCH_SEQPATTERN` lemma (73).

    `admissible` says that a recursive definition's result depends only on the
    recursion argument's predecessors under `<<`: if two functions `f` and `g`
    agree on everything `<< s(a)`, then `t f a = t g a`.

    `tailadmissible` is the tail-recursive refinement: the recursive call is
    conditional, with an explicit precondition `P`, guard-value `G` and non-
    recursive fallback `H`.  It is NOT the same shape as `admissible` - it has
    a three-way existential over `P`, `G`, `H`, and requires `f(G f a)`, not
    just agreement under `<<`.

    `superadmissible` wraps both: it says that if the PRECONDITION `p` is
    itself admissible (with a vacuous guard `\f a. T`), then the BODY `t` is
    tailadmissible.  This is the version the combinators actually chain.

    `MATCH_SEQPATTERN` (73) rewrites `_MATCH x (_SEQPATTERN r s)` into the
    conditional form, using `_MATCH` and `_SEQPATTERN` from `pair.ml`.  The
    constants come from `HolMath.Pair.PairDefs` with leading underscores
    DROPPED: `pairAux.MATCH` and `pairAux.SEQPATTERN`.

    ZERO `o`-compositions in the range.  ZERO THENL sites.  The three
    definitions are straight `new_definition` calls; the lemma is a straight
    `THEN` chain `REWRITE_TAC[_MATCH;_SEQPATTERN] THEN MESON_TAC[]`. -/
structure DefineAdmissible where
  /-- `admissible` (define.ml 51):
      `admissible(<<) p s t <=>
        !f g a. p f a /\ p g a /\ (!z. z << s(a) ==> (f z = g z))
                ==> (t f a = t g a)`. -/
  admissible : thm
  /-- `tailadmissible` (define.ml 56):
      `tailadmissible(<<) p s t <=>
        ?P G H. (!f a y. P f a /\ y << G f a ==> y << s a) /\
                (!f g a. (!z. z << s(a) ==> (f z = g z))
                         ==> (P f a = P g a) /\
                             (G f a = G g a) /\ (H f a = H g a)) /\
                (!f a:P. p f a ==> (t (f:A->B) a =
                                    if P f a then f(G f a) else H f a))`. -/
  tailadmissible : thm
  /-- `superadmissible` (define.ml 65):
      `superadmissible(<<) p s t <=>
        admissible(<<) (\f a. T) s p ==> tailadmissible(<<) p s t`. -/
  superadmissible : thm
  /-- `MATCH_SEQPATTERN` (define.ml 73):
      `_MATCH x (_SEQPATTERN r s) =
        if ?y. r x y then _MATCH x r else _MATCH x s`.
      `REWRITE_TAC[_MATCH; _SEQPATTERN] THEN MESON_TAC[]`. -/
  MATCH_SEQPATTERN : thm
  deriving Inhabited

/-- define.ml 47-78: various notions of admissibility, and a lemma. -/
@[nospecialize]
def setupDefineAdmissible [HolBase]
    (new_definition' : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic)
    (_MATCH _SEQPATTERN : thm) :
    ExceptT String IO DefineAdmissible := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)

  /- Various notions of admissibility, with tail recursion and preconditions. -/

  let admissible ← new_definition
   r"admissible(<<) p s t <=>
        !f g a. p f a /\ p g a /\ (!z. z << s(a) ==> (f z = g z))
                ==> (t f a = t g a)"

  let tailadmissible ← new_definition
   r"tailadmissible(<<) p s t <=>
        ?P G H. (!f a y. P f a /\ y << G f a ==> y << s a) /\
                (!f g a. (!z. z << s(a) ==> (f z = g z))
                         ==> (P f a = P g a) /\
                             (G f a = G g a) /\ (H f a = H g a)) /\
                (!f a:P. p f a ==> (t (f:A->B) a =
                                    if P f a then f(G f a) else H f a))"

  let superadmissible ← new_definition
   r"superadmissible(<<) p s t <=>
        admissible(<<) (\f a. T) s p ==> tailadmissible(<<) p s t"

  /- A lemma. -/

  let MATCH_SEQPATTERN ← prove
   r"_MATCH x (_SEQPATTERN r s) =
   if ?y. r x y then _MATCH x r else _MATCH x s"
   (REWRITE_TAC [_MATCH, _SEQPATTERN] THEN MESON_TAC [])

  return {
    admissible, tailadmissible, superadmissible, MATCH_SEQPATTERN }

/-- define.ml 79-222: the fifteen admissibility combinators, `ADMISSIBLE_CONST`
    (82) through `ADMISSIBLE_MATCH_SEQPATTERN` (211).  (The source contains
    exactly fifteen `^let ... = prove` bindings in this range, extracted with a
    regex; there is no larger count.)

    Every one elaborates the single `admissible` definition (define.ml 51,
    threaded here as `admissible`): each says that if a definition's SUBTERMS
    are admissible then a particular COMPOUND term built from them is
    admissible.  These are the workhorses the `define` proof suite chains
    automatically once the file is complete, so each statement is transcribed
    VERBATIM and every proof preserved character for character - a weakened
    statement would silently narrow the class of definitions `define` accepts,
    not fail locally.

    They form ONE contiguous OCaml section and share one dependency set, so
    they live in ONE bundle.  `ADMISSIBLE_MATCH_SEQPATTERN` (211) rewrites with
    `ADMISSIBLE_COND` (117) proved earlier in the same bundle, so a split would
    sever an internal reference.

    CROSS-FILE REACH (three combinators leave define.ml):
      * `ADMISSIBLE_NSUM` (182) uses `nsum` (iterate.ml 1288, at `:num`) and is
        proved by `NSUM_EQ_NUMSEG` (iterate.ml 1796) - both from the Iterate
        layer's `IterateNsum3` bundle.
      * `ADMISSIBLE_SUM` (190) uses `sum` (iterate.ml 1984, at `:real`, NOT the
        same constant as `nsum`) and is proved by `SUM_EQ_NUMSEG`
        (iterate.ml 2615) - the Iterate layer's `IterateSum3` bundle.
      * `ADMISSIBLE_MAP` (198) uses `MAP` (lists.ml) and is proved by `MAP_EQ`
        and `ALL_MEM` - the Lists layer's `ListThms1` bundle.
    All four supporting theorems (`NSUM_EQ_NUMSEG`, `SUM_EQ_NUMSEG`, `MAP_EQ`,
    `ALL_MEM`) are threaded as ordinary `thm`s from Session.

    PATTERN-MATCHING CONSTANTS.  `ADMISSIBLE_MATCH` (129), `ADMISSIBLE_SEQPATTERN`
    (136), `ADMISSIBLE_UNGUARDED_PATTERN` (146), `ADMISSIBLE_GUARDED_PATTERN`
    (162) and `ADMISSIBLE_MATCH_SEQPATTERN` (211) rewrite with the `pair.ml`
    constants, which on our side are `HolMath.Pair.PairDefs` fields with the
    LEADING UNDERSCORES DROPPED: `pairAux.MATCH` (`_MATCH`), `pairAux.SEQPATTERN`
    (`_SEQPATTERN`), `pairAux.UNGUARDED_PATTERN` (`_UNGUARDED_PATTERN`),
    `pairAux.GUARDED_PATTERN` (`_GUARDED_PATTERN`) and `pairAux.GEQ_DEF`
    (`GEQ_DEF`).  `MATCH_SEQPATTERN` (define.ml 73) is threaded from the
    `DefineAdmissible` bundle.

    ZERO `o`-compositions in the range.  ONE THENL site: define.ml 206 in
    `ADMISSIBLE_MAP`, width 2, branch list `[ASM_MESON_TAC[]; ALL_TAC]`, with a
    trailing `THEN MATCH_MP_TAC ...` that applies to ALL survivors and so is
    built with a further `THEN` OUTSIDE the `THENL`. -/
structure DefineAdmissibleThms where
  /-- `ADMISSIBLE_CONST` (define.ml 82):
      `!p s c. admissible(<<) p s (\f. c)`.  `REWRITE_TAC[admissible]`. -/
  ADMISSIBLE_CONST : thm
  /-- `ADMISSIBLE_BASE` (define.ml 86):
      `!(<<) p s t. (!f a. p f a ==> t a << s a)
        ==> admissible((<<):A->A->bool) p s (\f:A->B x:P. f(t x))`.
      `REWRITE_TAC[admissible] THEN MESON_TAC[]`. -/
  ADMISSIBLE_BASE : thm
  /-- `ADMISSIBLE_COMB` (define.ml 92):
      `!(<<) p s:P->A g:(A->B)->P->C->D y:(A->B)->P->C.
        admissible(<<) p s g /\ admissible(<<) p s y
        ==> admissible(<<) p s (\f x. (g f x) (y f x))`.
      `SIMP_TAC[admissible] THEN MESON_TAC[]`. -/
  ADMISSIBLE_COMB : thm
  /-- `ADMISSIBLE_RAND` (define.ml 98):
      `!(<<) p s:P->A g:P->C->D y:(A->B)->P->C.
        admissible(<<) p s y ==> admissible(<<) p s (\f x. (g x) (y f x))`.
      `SIMP_TAC[admissible] THEN MESON_TAC[]`. -/
  ADMISSIBLE_RAND : thm
  /-- `ADMISSIBLE_LAMBDA` (define.ml 104):
      `!(<<) p s:P->A t:(A->B)->C->P->bool.
        admissible(<<) (\f (u,x). p f x) (\(u,x). s x) (\f (u,x). t f u x)
        ==> admissible(<<) p s (\f x. \u. t f u x)`.
      `REWRITE_TAC[admissible; FUN_EQ_THM; FORALL_PAIR_THM] THEN MESON_TAC[]`. -/
  ADMISSIBLE_LAMBDA : thm
  /-- `ADMISSIBLE_NEST` (define.ml 110):
      `!(<<) p s t. admissible(<<) p s t /\ (!f a. p f a ==> t f a << s a)
        ==> admissible((<<):A->A->bool) p s (\f:A->B x:P. f(t f x))`.
      `REWRITE_TAC[admissible] THEN MESON_TAC[]`. -/
  ADMISSIBLE_NEST : thm
  /-- `ADMISSIBLE_COND` (define.ml 117):
      `!(<<) p P s h k.
        admissible(<<) p s P /\
        admissible(<<) (\f x. p f x /\ P f x) s h /\
        admissible(<<) (\f x. p f x /\ ~P f x) s k
        ==> admissible(<<) p s (\f x:P. if P f x then h f x else k f x)`.
      `REPEAT GEN_TAC THEN REWRITE_TAC[admissible; AND_FORALL_THM] THEN
      REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
      DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]`. -/
  ADMISSIBLE_COND : thm
  /-- `ADMISSIBLE_MATCH` (define.ml 129):
      `!(<<) p s e c.
        admissible(<<) p s e /\ admissible(<<) p s (\f x. c f x (e f x))
        ==> admissible(<<) p s (\f x:P. _MATCH (e f x) (c f x))`.
      `REWRITE_TAC[admissible; _MATCH] THEN REPEAT STRIP_TAC THEN
      REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[]`. -/
  ADMISSIBLE_MATCH : thm
  /-- `ADMISSIBLE_SEQPATTERN` (define.ml 136):
      `!(<<) p s c1 c2 e.
        admissible(<<) p s (\f x:P. ?y. c1 f x (e f x) y) /\
        admissible(<<) (\f x. p f x /\ ?y. c1 f x (e f x) y) s
                       (\f x. c1 f x (e f x)) /\
        admissible(<<) (\f x. p f x /\ ~(?y. c1 f x (e f x) y)) s
                       (\f x. c2 f x (e f x))
        ==> admissible(<<) p s (\f x. _SEQPATTERN (c1 f x) (c2 f x) (e f x))`.
      `REWRITE_TAC[_SEQPATTERN; admissible] THEN MESON_TAC[]`. -/
  ADMISSIBLE_SEQPATTERN : thm
  /-- `ADMISSIBLE_UNGUARDED_PATTERN` (define.ml 146):
      `!(<<) p s pat e t y.
        admissible (<<) p s pat /\ admissible (<<) p s e /\
        admissible (<<) (\f x. p f x /\ pat f x = e f x) s t /\
        admissible (<<) (\f x. p f x /\ pat f x = e f x) s y
        ==> admissible(<<) p s
             (\f x:P. _UNGUARDED_PATTERN (GEQ (pat f x) (e f x))
                                         (GEQ (t f x) (y f x)))`.
      `REPEAT GEN_TAC THEN
      REWRITE_TAC[admissible; FORALL_PAIR_THM; _UNGUARDED_PATTERN] THEN
      REWRITE_TAC[GEQ_DEF] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(TAUT `(a <=> a') /\ (a /\ a' ==> (b <=> b'))
                         ==> (a /\ b <=> a' /\ b')`) THEN ASM_MESON_TAC[]`. -/
  ADMISSIBLE_UNGUARDED_PATTERN : thm
  /-- `ADMISSIBLE_GUARDED_PATTERN` (define.ml 162):
      `!(<<) p s pat q e t y.
        admissible (<<) p s pat /\ admissible (<<) p s e /\
        admissible (<<) (\f x. p f x /\ pat f x = e f x /\ q f x) s t /\
        admissible (<<) (\f x. p f x /\ pat f x = e f x) s q /\
        admissible (<<) (\f x. p f x /\ pat f x = e f x /\ q f x) s y
        ==> admissible(<<) p s
             (\f x:P. _GUARDED_PATTERN (GEQ (pat f x) (e f x)) (q f x)
                                       (GEQ (t f x) (y f x)))`.
      `REPEAT GEN_TAC THEN
      REWRITE_TAC[admissible; FORALL_PAIR_THM; _GUARDED_PATTERN] THEN
      REWRITE_TAC[GEQ_DEF] THEN REPEAT STRIP_TAC THEN
      REPEAT(MATCH_MP_TAC(TAUT `...`) THEN REPEAT STRIP_TAC) THEN
      TRY(MATCH_MP_TAC(MESON[] `x = x' /\ y = y' ==> (x = y <=> x' = y')`)) THEN
      ASM_MESON_TAC[]`. -/
  ADMISSIBLE_GUARDED_PATTERN : thm
  /-- `ADMISSIBLE_NSUM` (define.ml 182):
      `!(<<) p:(B->C)->P->bool s:P->A h a b.
        admissible(<<) (\f (k,x). a(x) <= k /\ k <= b(x) /\ p f x)
                       (\(k,x). s x) (\f (k,x). h f x k)
        ==> admissible(<<) p s (\f x. nsum(a(x)..b(x)) (h f x))`.
      `nsum` is at `:num` (iterate.ml 1288).
      `REWRITE_TAC[admissible; FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC NSUM_EQ_NUMSEG THEN ASM_MESON_TAC[]`. -/
  ADMISSIBLE_NSUM : thm
  /-- `ADMISSIBLE_SUM` (define.ml 190):
      `!(<<) p:(B->C)->P->bool s:P->A h a b.
        admissible(<<) (\f (k,x). a(x) <= k /\ k <= b(x) /\ p f x)
                       (\(k,x). s x) (\f (k,x). h f x k)
        ==> admissible(<<) p s (\f x. sum(a(x)..b(x)) (h f x))`.
      `sum` is at `:real` (iterate.ml 1984), NOT interchangeable with `nsum`.
      `REWRITE_TAC[admissible; FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_MESON_TAC[]`. -/
  ADMISSIBLE_SUM : thm
  /-- `ADMISSIBLE_MAP` (define.ml 198):
      `!(<<) p s h l.
        admissible(<<) p s l /\
        admissible (<<) (\f (y,x). p f x /\ MEM y (l f x))
                        (\(y,x). s x) (\f (y,x). h f x y)
        ==> admissible (<<) p s (\f:A->B x:P. MAP (h f x) (l f x))`.
      `REWRITE_TAC[admissible; FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(MESON[] `x = y /\ MAP f x = MAP g x ==> MAP f x = MAP g y`)
      THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN ASM_MESON_TAC[]`.  The THENL (206)
      has width 2; the trailing `THEN MATCH_MP_TAC MAP_EQ ...` applies to all
      survivors and is built OUTSIDE the branch list. -/
  ADMISSIBLE_MAP : thm
  /-- `ADMISSIBLE_MATCH_SEQPATTERN` (define.ml 211):
      `!(<<) p s c1 c2 e.
        admissible(<<) p s (\f x. ?y. c1 f x (e f x) y) /\
        admissible(<<) (\f x. p f x /\ ?y. c1 f x (e f x) y) s
                       (\f x. _MATCH (e f x) (c1 f x)) /\
        admissible(<<) (\f x. p f x /\ ~(?y. c1 f x (e f x) y)) s
                       (\f x. _MATCH (e f x) (c2 f x))
        ==> admissible(<<) p s
              (\f x:P. _MATCH (e f x) (_SEQPATTERN (c1 f x) (c2 f x)))`.
      `REWRITE_TAC[MATCH_SEQPATTERN; ADMISSIBLE_COND]` - both `MATCH_SEQPATTERN`
      (define.ml 73) and `ADMISSIBLE_COND` (this bundle) are threaded. -/
  ADMISSIBLE_MATCH_SEQPATTERN : thm
  deriving Inhabited

/-- define.ml 80-236: admissibility combinators. -/
@[nospecialize]
def setupDefineAdmissibleThms [HolBase]
    (MESON' : List thm → term → IO (Except String thm))
    (MESON_TAC ASM_MESON_TAC : List thm → tactic)
    (admissible MATCH_SEQPATTERN : thm)
    (_MATCH _SEQPATTERN _UNGUARDED_PATTERN _GUARDED_PATTERN GEQ_DEF : thm)
    (FUN_EQ_THM FORALL_PAIR_THM AND_FORALL_THM MONO_FORALL : thm)
    (NSUM_EQ_NUMSEG SUM_EQ_NUMSEG MAP_EQ ALL_MEM : thm) :
    ExceptT String IO DefineAdmissibleThms := do
  let MESON (ths : List thm) (t : term) : ExceptT String IO thm := MESON' ths t

  /- Admissibility combinators. -/

  let ADMISSIBLE_CONST ← prove
   r"!p s c. admissible(<<) p s (\f. c)"
   (REWRITE_TAC [admissible])

  let ADMISSIBLE_BASE ← prove
   r"!(<<) p s t.
        (!f a. p f a ==> t a << s a)
        ==> admissible((<<):A->A->bool) p s (\f:A->B x:P. f(t x))"
   (REWRITE_TAC [admissible] THEN MESON_TAC [])

  let ADMISSIBLE_COMB ← prove
   r"!(<<) p s:P->A g:(A->B)->P->C->D y:(A->B)->P->C.
        admissible(<<) p s g /\ admissible(<<) p s y
        ==> admissible(<<) p s (\f x. (g f x) (y f x))"
   (SIMP_TAC [admissible] THEN MESON_TAC [])

  let ADMISSIBLE_RAND ← prove
   r"!(<<) p s:P->A g:P->C->D y:(A->B)->P->C.
        admissible(<<) p s y
        ==> admissible(<<) p s (\f x. (g x) (y f x))"
   (SIMP_TAC [admissible] THEN MESON_TAC [])

  let ADMISSIBLE_LAMBDA ← prove
   r"!(<<) p s:P->A t:(A->B)->C->P->bool.
     admissible(<<) (\f (u,x). p f x) (\(u,x). s x) (\f (u,x). t f u x)
     ==> admissible(<<) p s (\f x. \u. t f u x)"
   (REWRITE_TAC [admissible, FUN_EQ_THM, FORALL_PAIR_THM] THEN MESON_TAC [])

  let ADMISSIBLE_NEST ← prove
   r"!(<<) p s t.
        admissible(<<) p s t /\
        (!f a. p f a ==> t f a << s a)
        ==> admissible((<<):A->A->bool) p s (\f:A->B x:P. f(t f x))"
   (REWRITE_TAC [admissible] THEN MESON_TAC [])

  let ADMISSIBLE_COND ← prove
   r"!(<<) p P s h k.
        admissible(<<) p s P /\
        admissible(<<) (\f x. p f x /\ P f x) s h /\
        admissible(<<) (\f x. p f x /\ ~P f x) s k
        ==> admissible(<<) p s (\f x:P. if P f x then h f x else k f x)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [admissible, AND_FORALL_THM] THEN
    REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [])

  let ADMISSIBLE_MATCH ← prove
   r"!(<<) p s e c.
        admissible(<<) p s e /\ admissible(<<) p s (\f x. c f x (e f x))
        ==> admissible(<<) p s (\f x:P. _MATCH (e f x) (c f x))"
   (REWRITE_TAC [admissible, _MATCH] THEN
    REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_MESON_TAC [])

  let ADMISSIBLE_SEQPATTERN ← prove
   r"!(<<) p s c1 c2 e.
        admissible(<<) p s (\f x:P. ?y. c1 f x (e f x) y) /\
        admissible(<<) (\f x. p f x /\ ?y. c1 f x (e f x) y) s
                       (\f x. c1 f x (e f x)) /\
        admissible(<<) (\f x. p f x /\ ~(?y. c1 f x (e f x) y)) s
                       (\f x. c2 f x (e f x))
        ==> admissible(<<) p s (\f x. _SEQPATTERN (c1 f x) (c2 f x) (e f x))"
   (REWRITE_TAC [_SEQPATTERN, admissible] THEN MESON_TAC [])

  let ADMISSIBLE_UNGUARDED_PATTERN ← prove
   r"!(<<) p s pat e t y.
      admissible (<<) p s pat /\
      admissible (<<) p s e /\
      admissible (<<) (\f x. p f x /\ pat f x = e f x) s t /\
      admissible (<<) (\f x. p f x /\ pat f x = e f x) s y
        ==> admissible(<<) p s
             (\f x:P. _UNGUARDED_PATTERN (GEQ (pat f x) (e f x))
                                         (GEQ (t f x) (y f x)))"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [admissible, FORALL_PAIR_THM, _UNGUARDED_PATTERN] THEN
    REWRITE_TAC [GEQ_DEF] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← TAUT (← q r"(a <=> a') /\ (a /\ a' ==> (b <=> b'))
                       ==> (a /\ b <=> a' /\ b')")) THEN
    ASM_MESON_TAC [])

  let ADMISSIBLE_GUARDED_PATTERN ← prove
   r"!(<<) p s pat q e t y.
      admissible (<<) p s pat /\
      admissible (<<) p s e /\
      admissible (<<) (\f x. p f x /\ pat f x = e f x /\ q f x) s t /\
      admissible (<<) (\f x. p f x /\ pat f x = e f x) s q /\
      admissible (<<) (\f x. p f x /\ pat f x = e f x /\ q f x) s y
        ==> admissible(<<) p s
             (\f x:P. _GUARDED_PATTERN (GEQ (pat f x) (e f x))
                                       (q f x)
                                       (GEQ (t f x) (y f x)))"
   (← do
     let m ← MESON [] (← q r"x = x' /\ y = y' ==> (x = y <=> x' = y')")
     let t ← TAUT (← q r"(a <=> a') /\ (a /\ a' ==> (b <=> b'))
                              ==> (a /\ b <=> a' /\ b')")
     pure (REPEAT GEN_TAC THEN
       REWRITE_TAC [admissible, FORALL_PAIR_THM, _GUARDED_PATTERN] THEN
       REWRITE_TAC [GEQ_DEF] THEN REPEAT STRIP_TAC THEN
       REPEAT (MATCH_MP_TAC t THEN
              REPEAT STRIP_TAC) THEN
       TRY (MATCH_MP_TAC m) THEN
       ASM_MESON_TAC []))

  let ADMISSIBLE_NSUM ← prove
   r"!(<<) p:(B->C)->P->bool s:P->A h a b.
        admissible(<<) (\f (k,x). a(x) <= k /\ k <= b(x) /\ p f x)
                       (\(k,x). s x) (\f (k,x). h f x k)
   ==> admissible(<<) p s (\f x. nsum(a(x)..b(x)) (h f x))"
   (REWRITE_TAC [admissible, FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC NSUM_EQ_NUMSEG THEN ASM_MESON_TAC [])

  let ADMISSIBLE_SUM ← prove
   r"!(<<) p:(B->C)->P->bool s:P->A h a b.
        admissible(<<) (\f (k,x). a(x) <= k /\ k <= b(x) /\ p f x)
                       (\(k,x). s x) (\f (k,x). h f x k)
   ==> admissible(<<) p s (\f x. sum(a(x)..b(x)) (h f x))"
   (REWRITE_TAC [admissible, FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_MESON_TAC [])

  let ADMISSIBLE_MAP ← prove
   r"!(<<) p s h l.
        admissible(<<) p s l /\
        admissible (<<) (\f (y,x). p f x /\ MEM y (l f x))
                        (\(y,x). s x) (\f (y,x). h f x y)
   ==> admissible (<<) p s (\f:A->B x:P. MAP (h f x) (l f x))"
   (REWRITE_TAC [admissible, FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← MESON [] (← q r"x = y /\ MAP f x = MAP g x ==> MAP f x = MAP g y")) THEN
    CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC [← GSYM ALL_MEM] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [FORALL_PAIR_THM] THEN ASM_MESON_TAC [])

  let ADMISSIBLE_MATCH_SEQPATTERN ← prove
   r"!(<<) p s c1 c2 e.
        admissible(<<) p s (\f x. ?y. c1 f x (e f x) y) /\
        admissible(<<) (\f x. p f x /\ ?y. c1 f x (e f x) y) s
                       (\f x. _MATCH (e f x) (c1 f x)) /\
        admissible(<<) (\f x. p f x /\ ~(?y. c1 f x (e f x) y)) s
                       (\f x. _MATCH (e f x) (c2 f x))
        ==> admissible(<<) p s
              (\f x:P. _MATCH (e f x) (_SEQPATTERN (c1 f x) (c2 f x)))"
   (REWRITE_TAC [MATCH_SEQPATTERN, ADMISSIBLE_COND])

  return {
    ADMISSIBLE_CONST, ADMISSIBLE_BASE, ADMISSIBLE_COMB, ADMISSIBLE_RAND,
    ADMISSIBLE_LAMBDA, ADMISSIBLE_NEST, ADMISSIBLE_COND, ADMISSIBLE_MATCH,
    ADMISSIBLE_SEQPATTERN, ADMISSIBLE_UNGUARDED_PATTERN,
    ADMISSIBLE_GUARDED_PATTERN, ADMISSIBLE_NSUM, ADMISSIBLE_SUM,
    ADMISSIBLE_MAP, ADMISSIBLE_MATCH_SEQPATTERN }

/-- define.ml 223-356: the seven superadmissible generalizations,
    `ADMISSIBLE_IMP_SUPERADMISSIBLE` (233) through
    `SUPERADMISSIBLE_MATCH_GUARDED_PATTERN` (330).  (The source contains
    exactly SEVEN `^let ... = prove` bindings in this range, extracted with a
    regex on `^let `; the prompt's "eight" was off by one - there is no eighth
    name.)

    Each generalizes an admissibility fact into a SUPERADMISSIBLE one: the
    tail-recursive refinement `define` actually chains.  The base step is
    `ADMISSIBLE_IMP_SUPERADMISSIBLE` (233), proved directly from the three
    definitions; the remaining six build on it or on `SUPERADMISSIBLE_COND`.

    Proof shapes in this range:
      * Two BARE one-liners: `SUPERADMISSIBLE_CONST` (244,
        `MATCH_MP_TAC ADMISSIBLE_IMP_SUPERADMISSIBLE THEN REWRITE_TAC[...]`)
        and `SUPERADMISSIBLE_MATCH_SEQPATTERN` (295, a single
        `REWRITE_TAC[MATCH_SEQPATTERN; SUPERADMISSIBLE_COND]`).
      * Three short structured proofs sharing one shape - unfold the defs,
        `REPEAT STRIP_TAC`, `MAP_EVERY EXISTS_TAC [..three..]`, close with
        `ASM_MESON_TAC[]`: `ADMISSIBLE_IMP_SUPERADMISSIBLE` (233) and
        `SUPERADMISSIBLE_TAIL` (250).
      * Two HEAVY pattern proofs, near-identical to each other -
        `SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN` (306, span 24) and
        `SUPERADMISSIBLE_MATCH_GUARDED_PATTERN` (330, span 27): unfold via the
        `pairAux` constants, a `SUBGOAL_THEN ... (fun th -> SIMP_TAC[th])`
        step split `THENL [ASM_MESON_TAC[]; ALL_TAC]`, then a three-way
        `MAP_EVERY EXISTS_TAC`, `RULE_ASSUM_TAC(REWRITE_RULE[admissible])`,
        `SIMP_TAC[]`, `ASM_MESON_TAC[]`.
      * THE HEAVIEST: `SUPERADMISSIBLE_COND` (262, span 33) - a long THEN
        chain with THREE THENL sites, two thm-tactic closures over `th`, one
        `MAP_EVERY X_GEN_TAC` over six vars, a `TAUT`-rewrite, and the range's
        ONE `o`-composition.

    THE ONE `o`-COMPOSITION (define.ml 288, in `SUPERADMISSIBLE_COND`):
    `POP_ASSUM_LIST(MP_TAC o end_itlist CONJ)`.  `o` applies its RIGHT operand
    FIRST: `end_itlist CONJ` folds the popped assumption list into a single
    right-associated conjunction, THEN `MP_TAC` moves it onto the goal.
    Rendered right-to-left as `fun ths => MP_TAC (end_itlistM B.CONJ ths)`,
    guarding the `Except` from `CONJ`.

    THENL SITES (all in `SUPERADMISSIBLE_COND`):
      * define.ml 274 `ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]` - width 2,
        2 branches.  Trailing `THEN DISCH_THEN(...)` is a further THEN.
      * define.ml 276 `ANTS_TAC THENL [ASM_MESON_TAC[]; MP_TAC th]` - width 2,
        2 branches, INSIDE the `DISCH_THEN(fun th -> ...)` closure.
      * define.ml 286 `REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THENL
        [ASM_MESON_TAC[]; POP_ASSUM_LIST(...); ALL_TAC]` - width 3,
        3 branches.  The trailing `THEN REWRITE_TAC[IMP_IMP; AND_FORALL_THM]`
        applies to ALL survivors and is a further THEN OUTSIDE the branch list:
        `let split := THENL B chain [..3..]`, then
        `THEN B split (REWRITE_TAC ...)`.

    PATTERN-MATCHING CONSTANTS.  `SUPERADMISSIBLE_MATCH_SEQPATTERN` (295),
    `SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN` (306) and
    `SUPERADMISSIBLE_MATCH_GUARDED_PATTERN` (330) use the `pair.ml` constants,
    which on our side are `HolMath.Pair.PairDefs` fields with the LEADING
    UNDERSCORES DROPPED: `pairAux.MATCH` (`_MATCH`), `pairAux.SEQPATTERN`
    (`_SEQPATTERN`), `pairAux.UNGUARDED_PATTERN` (`_UNGUARDED_PATTERN`),
    `pairAux.GUARDED_PATTERN` (`_GUARDED_PATTERN`), `pairAux.GEQ_DEF`
    (`GEQ_DEF`) - NOT bare Session accessors.  `MATCH_SEQPATTERN`
    (define.ml 73) and the three core definitions are threaded from the
    `DefineAdmissible` bundle; `ADMISSIBLE_CONST`/`ADMISSIBLE_COND` from the
    `DefineAdmissibleThms` bundle.

    These generalize the admissibility combinators
    of define.ml 79-222, so they form ONE contiguous OCaml section with one
    dependency set and live in ONE bundle. -/
structure DefineSuperadmissibleThms where
  /-- `ADMISSIBLE_IMP_SUPERADMISSIBLE` (define.ml 233):
      `!(<<) p s t:(A->B)->P->B.
        admissible(<<) p s t ==> superadmissible(<<) p s t`.
      `REWRITE_TAC[admissible; superadmissible; tailadmissible] THEN
      REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [..three..] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]`. -/
  ADMISSIBLE_IMP_SUPERADMISSIBLE : thm
  /-- `SUPERADMISSIBLE_CONST` (define.ml 244):
      `!p s c. superadmissible(<<) p s (\f. c)`.
      `REPEAT GEN_TAC THEN MATCH_MP_TAC ADMISSIBLE_IMP_SUPERADMISSIBLE THEN
      REWRITE_TAC[ADMISSIBLE_CONST]`. -/
  SUPERADMISSIBLE_CONST : thm
  /-- `SUPERADMISSIBLE_TAIL` (define.ml 250):
      `!(<<) p s t:(A->B)->P->A.
        admissible(<<) p s t /\
        (!f a. p f a ==> !y. y << t f a ==> y << s a)
        ==> superadmissible(<<) p s (\f x. f(t f x))`.
      `REWRITE_TAC[admissible; superadmissible; tailadmissible] THEN
      REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [..three..] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]`. -/
  SUPERADMISSIBLE_TAIL : thm
  /-- `SUPERADMISSIBLE_COND` (define.ml 262):
      `!(<<) p P s h k:(A->B)->P->B.
        admissible(<<) p s P /\
        superadmissible(<<) (\f x. p f x /\ P f x) s h /\
        superadmissible(<<) (\f x. p f x /\ ~P f x) s k
        ==> superadmissible(<<) p s (\f x. if P f x then h f x else k f x)`.
      The heaviest proof in the range: THREE THENL sites (274, 276, 286),
      two `DISCH_THEN(fun th -> ...)` closures, `MAP_EVERY X_GEN_TAC` over six
      variables, a `TAUT`-rewrite, and the range's ONE `o`-composition
      (288, `MP_TAC o end_itlist CONJ`). -/
  SUPERADMISSIBLE_COND : thm
  /-- `SUPERADMISSIBLE_MATCH_SEQPATTERN` (define.ml 295):
      `!(<<) p s c1 c2 e.
        admissible(<<) p s (\f x. ?y. c1 f x (e f x) y) /\
        superadmissible(<<) (\f x. p f x /\ ?y. c1 f x (e f x) y) s
                            (\f x. _MATCH (e f x) (c1 f x)) /\
        superadmissible(<<) (\f x. p f x /\ ~(?y. c1 f x (e f x) y)) s
                            (\f x. _MATCH (e f x) (c2 f x))
        ==> superadmissible(<<) p s
              (\f x:P. _MATCH (e f x) (_SEQPATTERN (c1 f x) (c2 f x)))`.
      `REWRITE_TAC[MATCH_SEQPATTERN; SUPERADMISSIBLE_COND]` - both threaded
      (`MATCH_SEQPATTERN` from `DefineAdmissible`, `SUPERADMISSIBLE_COND` above). -/
  SUPERADMISSIBLE_MATCH_SEQPATTERN : thm
  /-- `SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN` (define.ml 306):
      `!(<<) p s e:P->D pat:Q->D arg.
        (!f a t u. p f a /\ pat t = e a /\ pat u = e a ==> arg a t = arg a u) /\
        (!f a t. p f a /\ pat t = e a ==> !y. y << arg a t ==> y << s a)
        ==> superadmissible(<<) p s
             (\f:A->B x. _MATCH (e x)
                    (\u v. ?t. _UNGUARDED_PATTERN (GEQ (pat t) u)
                                                  (GEQ (f(arg x t)) v)))`.
      `REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[superadmissible] THEN
      DISCH_TAC THEN REWRITE_TAC[_UNGUARDED_PATTERN; GEQ_DEF; _MATCH] THEN
      REWRITE_TAC[tailadmissible] THEN SUBGOAL_THEN `...`
      (fun th -> SIMP_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [..three..] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[admissible]) THEN SIMP_TAC[] THEN
      ASM_MESON_TAC[]`.  ONE THENL (width 2). -/
  SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN : thm
  /-- `SUPERADMISSIBLE_MATCH_GUARDED_PATTERN` (define.ml 330):
      `!(<<) p s e:P->D pat:Q->D q arg.
        (!f a t u. p f a /\ pat t = e a /\ q a t /\ pat u = e a /\ q a u
                   ==> arg a t = arg a u) /\
        (!f a t. p f a /\ q a t /\ pat t = e a ==> !y. y << arg a t ==> y << s a)
        ==> superadmissible(<<) p s
             (\f:A->B x. _MATCH (e x)
                    (\u v. ?t. _GUARDED_PATTERN (GEQ (pat t) u)
                                                (q x t)
                                                (GEQ (f(arg x t)) v)))`.
      As UNGUARDED but with `_GUARDED_PATTERN`, the extra guard `q`, and a
      wider `SUBGOAL_THEN`.  ONE THENL (width 2). -/
  SUPERADMISSIBLE_MATCH_GUARDED_PATTERN : thm
  deriving Inhabited

/-- define.ml 238-359: superadmissible generalizations where applicable. -/
@[nospecialize]
def setupDefineSuperadmissibleThms [HolBase]
    (ASM_MESON_TAC : List thm → tactic)
    (admissible tailadmissible superadmissible MATCH_SEQPATTERN : thm)
    (ADMISSIBLE_CONST : thm)
    (_MATCH _UNGUARDED_PATTERN _GUARDED_PATTERN GEQ_DEF : thm)
    (LEFT_IMP_EXISTS_THM RIGHT_IMP_FORALL_THM IMP_IMP AND_FORALL_THM : thm)
    (MONO_AND MONO_FORALL : thm) :
    ExceptT String IO DefineSuperadmissibleThms := do

  /- Superadmissible generalizations where applicable.

     Note that we can't take the "higher type" route in the simple theorem
     ADMISSIBLE_MATCH because that isn't a context where tail recursion makes
     sense. Instead, we use specific theorems for the two _MATCH instances.
     Note that also, because of some delicacy over assessing welldefinedness
     of patterns, a special well-formedness hypothesis crops up here. (We need
     to separate it from the function f or we lose the "tail" optimization.) -/

  let ADMISSIBLE_IMP_SUPERADMISSIBLE ← prove
   r"!(<<) p s t:(A->B)->P->B.
      admissible(<<) p s t ==> superadmissible(<<) p s t"
   (REWRITE_TAC [admissible, superadmissible, tailadmissible] THEN
    REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [← q r"\f:A->B x:P. F",
      ← q r"\f:A->B. (anything:P->A)",
      ← q r"\f:A->B a:P. if p f a then t f a :B else fixed"] THEN
    ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [])

  let SUPERADMISSIBLE_CONST ← prove
   r"!p s c. superadmissible(<<) p s (\f. c)"
   (REPEAT GEN_TAC THEN
    MATCH_MP_TAC ADMISSIBLE_IMP_SUPERADMISSIBLE THEN
    REWRITE_TAC [ADMISSIBLE_CONST])

  let SUPERADMISSIBLE_TAIL ← prove
   r"!(<<) p s t:(A->B)->P->A.
      admissible(<<) p s t /\
      (!f a. p f a ==> !y. y << t f a ==> y << s a)
      ==> superadmissible(<<) p s (\f x. f(t f x))"
   (REWRITE_TAC [admissible, superadmissible, tailadmissible] THEN
    REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [← q r"\f:A->B x:P. T",
      ← q r"\f:A->B a:P. if p f a then t f a :A else s a",
      ← q r"\f:A->B. anything:P->B"] THEN
    ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [])

  let SUPERADMISSIBLE_COND ← prove
   r"!(<<) p P s h k:(A->B)->P->B.
        admissible(<<) p s P /\
        superadmissible(<<) (\f x. p f x /\ P f x) s h /\
        superadmissible(<<) (\f x. p f x /\ ~P f x) s k
        ==> superadmissible(<<) p s (\f x. if P f x then h f x else k f x)"
   (REWRITE_TAC [superadmissible, admissible] THEN REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (fun th => DISCH_TAC THEN CONJUNCTS_THEN MP_TAC th) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (fun th => ANTS_TAC THENL [ASM_MESON_TAC [], MP_TAC th]) THEN
    REWRITE_TAC [tailadmissible] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM, RIGHT_IMP_FORALL_THM] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"P1:(A->B)->P->bool", ← q r"G1:(A->B)->P->A", ← q r"H1:(A->B)->P->B",
      ← q r"P2:(A->B)->P->bool", ← q r"G2:(A->B)->P->A", ← q r"H2:(A->B)->P->B"] THEN
    REWRITE_TAC [← TAUT (← q r"(a1 /\ b1 /\ c1 ==> a2 /\ b2 /\ c2 ==> x) <=>
                      (a1 /\ a2) /\ (b1 /\ b2) /\ (c1 /\ c2) ==> x")] THEN
    DISCH_THEN (fun th => tactic_of do
     pure (MAP_EVERY EXISTS_TAC
     [← q r"\f:A->B a:P. if p f a then if P f a then P2 f a else P1 f a else F",
      ← q r"\f:A->B a:P. if p f a then if P f a then G2 f a else G1 f a else z:A",
      ← q r"\f:A->B a:P. if p f a then if P f a then H2 f a else H1 f a else w:B"] THEN
     MP_TAC th)) THEN
    REWRITE_TAC [] THEN REPEAT (MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THENL
     [ASM_MESON_TAC [],
      POP_ASSUM_LIST (fun ths => tactic_of do pure (MP_TAC (← end_itlist CONJ ths))),
      ALL_TAC] THEN
    REWRITE_TAC [IMP_IMP, AND_FORALL_THM] THEN
    REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [])

  let SUPERADMISSIBLE_MATCH_SEQPATTERN ← prove
   r"!(<<) p s c1 c2 e.
        admissible(<<) p s (\f x. ?y. c1 f x (e f x) y) /\
        superadmissible(<<) (\f x. p f x /\ ?y. c1 f x (e f x) y) s
                            (\f x. _MATCH (e f x) (c1 f x)) /\
        superadmissible(<<) (\f x. p f x /\ ~(?y. c1 f x (e f x) y)) s
                            (\f x. _MATCH (e f x) (c2 f x))
        ==> superadmissible(<<) p s
              (\f x:P. _MATCH (e f x) (_SEQPATTERN (c1 f x) (c2 f x)))"
   (REWRITE_TAC [MATCH_SEQPATTERN, SUPERADMISSIBLE_COND])

  let SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN ← prove
   r"!(<<) p s e:P->D pat:Q->D arg.
      (!f a t u. p f a /\ pat t = e a /\ pat u = e a ==> arg a t = arg a u) /\
      (!f a t. p f a /\ pat t = e a ==> !y. y << arg a t ==> y << s a)
      ==> superadmissible(<<) p s
           (\f:A->B x. _MATCH (e x)
                    (\u v. ?t. _UNGUARDED_PATTERN (GEQ (pat t) u)
                                                  (GEQ (f(arg x t)) v)))"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC [superadmissible] THEN DISCH_TAC THEN
    REWRITE_TAC [_UNGUARDED_PATTERN, GEQ_DEF, _MATCH] THEN
    REWRITE_TAC [tailadmissible] THEN
    SUBGOAL_THEN
     (← q r"!f:A->B x:P.
     p f x ==> ((?!v. ?t:Q. pat t:D = e x /\ f(arg x t) = v) <=>
                ?t. pat t = e x)")
     (fun th => SIMP_TAC [th]) THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [← q r"\(f:A->B) x:P. p f x /\ ?t:Q. pat t:D = e x",
      ← q r"\f:A->B x:P. arg x (@t. (pat:Q->D) t = e x):A",
      ← q r"\(f:A->B) x:P. (@z:B. F)"] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [admissible]) THEN SIMP_TAC [] THEN
    ASM_MESON_TAC [])

  let SUPERADMISSIBLE_MATCH_GUARDED_PATTERN ← prove
   r"!(<<) p s e:P->D pat:Q->D q arg.
      (!f a t u. p f a /\ pat t = e a /\ q a t /\ pat u = e a /\ q a u
                 ==> arg a t = arg a u) /\
      (!f a t. p f a /\ q a t /\ pat t = e a ==> !y. y << arg a t ==> y << s a)
      ==> superadmissible(<<) p s
           (\f:A->B x. _MATCH (e x)
                    (\u v. ?t. _GUARDED_PATTERN (GEQ (pat t) u)
                                                (q x t)
                                                (GEQ (f(arg x t)) v)))"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC [superadmissible] THEN DISCH_TAC THEN
    REWRITE_TAC [_GUARDED_PATTERN, GEQ_DEF, _MATCH] THEN
    REWRITE_TAC [tailadmissible] THEN
    SUBGOAL_THEN
     (← q r"!f:A->B x:P.
     p f x ==> ((?!v. ?t:Q. pat t:D = e x /\ q x t /\ f(arg x t) = v) <=>
                ?t. pat t = e x /\ q x t)")
     (fun th => SIMP_TAC [th]) THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [← q r"\(f:A->B) x:P. p f x /\ ?t:Q. pat t:D = e x /\ q x t",
      ← q r"\f:A->B x:P. arg x (@t. (pat:Q->D) t = e x /\ q x t):A",
      ← q r"\(f:A->B) x:P. (@z:B. F)"] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [admissible]) THEN SIMP_TAC [] THEN
    ASM_MESON_TAC [])

  return {
    ADMISSIBLE_IMP_SUPERADMISSIBLE, SUPERADMISSIBLE_CONST,
    SUPERADMISSIBLE_TAIL, SUPERADMISSIBLE_COND,
    SUPERADMISSIBLE_MATCH_SEQPATTERN, SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN,
    SUPERADMISSIBLE_MATCH_GUARDED_PATTERN }

structure DefineWfCasewise where
  /-- `WF_REC_TAIL_GENERAL'` (define.ml 360), PRIMED - NOT the pre-existing
      unprimed `WF_REC_TAIL_GENERAL`:
      `!P G H H'.
         WF (<<) /\
         (!f g x. (!z. z << x ==> (f z = g z))
                  ==> (P f x <=> P g x) /\
                      (G f x = G g x) /\ (H' f x = H' g x)) /\
         (!f x y. P f x /\ y << G f x ==> y << x) /\
         (!f x. H f x = if P f x then f(G f x) else H' f x)
         ==> ?f. !x. f x = H f x`.
      `REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC WF_REC_TAIL_GENERAL THEN ASM_MESON_TAC[]` - reduces to the
      UNPRIMED, pre-existing `WF_REC_TAIL_GENERAL`.  ZERO THENL. -/
  WF_REC_TAIL_GENERAL_prime : thm
  /-- `WF_REC_CASES` (define.ml 372):
      `!(<<) clauses.
        WF((<<):A->A->bool) /\
        ALL (\(s,t). ?P G H.
                     (!f a y. P f a /\ y << G f a ==> y << s a) /\
                     (!f g a. (!z. z << s(a) ==> (f z = g z))
                              ==> (P f a = P g a) /\
                                  (G f a = G g a) /\ (H f a = H g a)) /\
                     (!f a:P. t f a = if P f a then f(G f a) else H f a))
            clauses
        ==> ?f:A->B. !x. f x = CASEWISE clauses f x`.
      Uses the PRIMED `WF_REC_TAIL_GENERAL'` (the field above), then
      `FIRST_X_ASSUM(MP_TAC o check(is_binary "ALL" o concl))`, `SPEC_TAC`,
      `list_INDUCT`, `CONJ_TAC THENL [..; ALL_TAC]` (384, width 2), a nested
      `DISCH_THEN(fun th -> DISCH_THEN(...) THEN MP_TAC th)`, three
      `EXISTS_TAC`s.  ONE THENL. -/
  WF_REC_CASES : thm
  /-- `WF_REC_CASES'` (define.ml 412), PRIMED:
      `!(<<) clauses.
        WF((<<):A->A->bool) /\
        ALL (\(s,t). tailadmissible(<<) (\f a. T) s t) clauses
        ==> ?f:A->B. !x. f x = CASEWISE clauses f x`.
      `REWRITE_TAC[WF_REC_CASES; tailadmissible]`.  ZERO THENL. -/
  WF_REC_CASES_prime : thm
  /-- `RECURSION_CASEWISE` (define.ml 419) - INSTANTIATED BY THE ML SUITE:
      `!clauses.
   (?(<<). WF(<<) /\
           ALL (\(s:P->A,t). tailadmissible(<<) (\f a. T) s t) clauses) /\
   (!s t s' t' f x y. MEM (s,t) clauses /\ MEM (s',t') clauses
                      ==> (s x = s' y) ==> (t f x = t' f y))
   ==> ?f:A->B. ALL (\(s,t). !x. f (s x) = t f x) clauses`.
      `REPEAT GEN_TAC THEN REWRITE_TAC[IMP_IMP; CONJ_ASSOC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN(CHOOSE_THEN (MP_TAC o MATCH_MP WF_REC_CASES')) THEN
      MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[CASEWISE_WORKS]`.  ZERO THENL; the
      `o` at 427 (`MP_TAC o MATCH_MP WF_REC_CASES'`, right-first). -/
  RECURSION_CASEWISE : thm
  /-- `RECURSION_CASEWISE_PAIRWISE` (define.ml 432):
      `!clauses.
        (?(<<). WF (<<) /\
                ALL (\(s,t). tailadmissible(<<) (\f a. T) s t) clauses) /\
        ALL (\(s,t). !f x y. (s x = s y) ==> (t f x = t f y)) clauses /\
        PAIRWISE (\(s,t) (s',t'). !f x y. (s x = s' y) ==> (t f x = t' f y))
                 clauses
        ==> (?f. ALL (\(s,t). !x. f (s x) = t f x) clauses)`.
      Proof builds local `lemma`, `paired_lambda`, `pth = REWRITE_RULE[..]
      (ISPEC .. lemma)`, `cth = prove(lhand(concl pth), MESON_TAC[])`, then
      `REWRITE_TAC[GSYM(MATCH_MP pth cth); RIGHT_IMP_FORALL_THM] THEN
      REWRITE_TAC[RECURSION_CASEWISE]`.  ONE THENL (inside `lemma`: none;
      the lemma proof is a THEN chain with `LIST_INDUCT_TAC`). -/
  RECURSION_CASEWISE_PAIRWISE : thm
  /-- `SUPERADMISSIBLE_T` (define.ml 456):
      `superadmissible(<<) (\f x. T) s t <=> tailadmissible(<<) (\f x. T) s t`.
      `REWRITE_TAC[superadmissible; admissible]`.  ZERO THENL. -/
  SUPERADMISSIBLE_T : thm
  /-- `RECURSION_SUPERADMISSIBLE` (define.ml 460) - INSTANTIATED BY THE ML
      SUITE.  Derived, NOT a `prove`:
      `REWRITE_RULE[GSYM SUPERADMISSIBLE_T] RECURSION_CASEWISE_PAIRWISE`.
      Same statement as `RECURSION_CASEWISE_PAIRWISE` with the two
      `tailadmissible(<<) (\f a. T) s t` occurrences folded back to
      `superadmissible(<<) (\f x. T) s t`. -/
  RECURSION_SUPERADMISSIBLE : thm
  deriving Inhabited

/-- define.ml 361-466: combine the general WF/tail recursion theorem with
    casewise definitions.  `WF_REC_TAIL_GENERAL_prime` and
    `WF_REC_CASES_prime` are OCaml's `WF_REC_TAIL_GENERAL'` and
    `WF_REC_CASES'`. -/
@[nospecialize]
def setupDefineWfCasewise [HolBase]
    (MESON_TAC ASM_MESON_TAC : List thm → tactic)
    (LIST_INDUCT_TAC : tactic)
    (WF_REC_TAIL_GENERAL : thm)
    (CASEWISE CASEWISE_WORKS : thm)
    (tailadmissible superadmissible admissible : thm)
    (ALL MEM PAIRWISE ALL_MEM : thm)
    (FORALL_PAIR_THM list_INDUCT MONO_EXISTS FUN_EQ_THM : thm)
    (IMP_IMP CONJ_ASSOC LEFT_IMP_EXISTS_THM RIGHT_IMP_FORALL_THM : thm)
    (RIGHT_FORALL_IMP_THM IMP_CONJ : thm) :
    ExceptT String IO DefineWfCasewise := do

  /- Combine general WF/tail recursion theorem with casewise definitions. -/

  let WF_REC_TAIL_GENERAL_prime ← prove
   r"!P G H H'.
         WF (<<) /\
         (!f g x. (!z. z << x ==> (f z = g z))
                  ==> (P f x <=> P g x) /\
                      (G f x = G g x) /\ (H' f x = H' g x)) /\
         (!f x y. P f x /\ y << G f x ==> y << x) /\
         (!f x. H f x = if P f x then f(G f x) else H' f x)
         ==> ?f. !x. f x = H f x"
   (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC WF_REC_TAIL_GENERAL THEN ASM_MESON_TAC [])

  let WF_REC_CASES ← prove
   r"!(<<) clauses.
        WF((<<):A->A->bool) /\
        ALL (\(s,t). ?P G H.
                     (!f a y. P f a /\ y << G f a ==> y << s a) /\
                     (!f g a. (!z. z << s(a) ==> (f z = g z))
                              ==> (P f a = P g a) /\
                                  (G f a = G g a) /\ (H f a = H g a)) /\
                     (!f a:P. t f a = if P f a then f(G f a) else H f a))
            clauses
        ==> ?f:A->B. !x. f x = CASEWISE clauses f x"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC WF_REC_TAIL_GENERAL_prime THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      pure (MP_TAC (← check (fun t => is_binary "ALL" (concl t)) th))) THEN
    SPEC_TAC (← q r"clauses:((P->A)#((A->B)->P->B))list",
              ← q r"clauses:((P->A)#((A->B)->P->B))list") THEN
    ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC : thm → tactic) THEN
    MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [ALL, CASEWISE, FORALL_PAIR_THM] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC
       [← q r"\f:A->B x:A. F", ← q r"\f:A->B. anything:A->A", ← q r"\f:A->B x:A. @y:B. T"] THEN
      REWRITE_TAC [],
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC
      [← q r"s:P->A", ← q r"t:(A->B)->P->B", ← q r"clauses:((P->A)#((A->B)->P->B))list"] THEN
    DISCH_THEN (fun th => DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
                          MP_TAC th) THEN
    ASM_REWRITE_TAC [] THEN POP_ASSUM_LIST (K ALL_TAC : List thm → tactic) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN REWRITE_TAC [RIGHT_IMP_FORALL_THM] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"P1:(A->B)->A->bool", ← q r"G1:(A->B)->A->A", ← q r"H1:(A->B)->A->B",
      ← q r"P2:(A->B)->P->bool", ← q r"G2:(A->B)->P->A", ← q r"H2:(A->B)->P->B"] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    EXISTS_TAC
     (← q r"\f:A->B x:A. if ?y:P. s y = x then P2 f (@y. s y = x) else P1 f x:bool") THEN
    EXISTS_TAC (← q r"\f:A->B x:A.
     if ?y:P. s y = x then G2 f (@y. s y = x) else G1 f x:A") THEN
    EXISTS_TAC (← q r"\f:A->B x:A. if ?y:P. s y = x
                           then H2 f (@y. s y = x) else H1 f x:B") THEN
    ASM_MESON_TAC [])

  let WF_REC_CASES_prime ← prove
   r"!(<<) clauses.
        WF((<<):A->A->bool) /\
        ALL (\(s,t). tailadmissible(<<) (\f a. T) s t) clauses
        ==> ?f:A->B. !x. f x = CASEWISE clauses f x"
   (REWRITE_TAC [WF_REC_CASES, tailadmissible])

  let RECURSION_CASEWISE ← prove
   r"!clauses.
   (?(<<). WF(<<) /\
           ALL (\(s:P->A,t). tailadmissible(<<) (\f a. T) s t) clauses) /\
   (!s t s' t' f x y. MEM (s,t) clauses /\ MEM (s',t') clauses
                      ==> (s x = s' y) ==> (t f x = t' f y))
   ==> ?f:A->B. ALL (\(s,t). !x. f (s x) = t f x) clauses"
   (REPEAT GEN_TAC THEN REWRITE_TAC [IMP_IMP, CONJ_ASSOC] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN (CHOOSE_THEN (fun th => tactic_of do
      pure (MP_TAC (← MATCH_MP WF_REC_CASES_prime th)))) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [CASEWISE_WORKS])

  let RECURSION_CASEWISE_PAIRWISE ← do
    let lemma ← prove
     r"!P. (!x y. P x y ==> P y x)
         ==> !l. (!x y. MEM x l /\ MEM y l ==> P x y) <=>
                 ALL (\x. P x x) l /\ PAIRWISE P l"
     (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, ← GSYM ALL_MEM] THEN
      REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN
      REWRITE_TAC [PAIRWISE, MEM, ← GSYM ALL_MEM] THEN ASM_MESON_TAC [])
    let paired_lambda ← prove
     r"(\x. P x) = (\(a,b). P (a,b))"
     (REWRITE_TAC [FUN_EQ_THM, FORALL_PAIR_THM])
    let pth ← REWRITE_RULE [FORALL_PAIR_THM, paired_lambda] (← ISPEC
      (← q r"\(s,t) (s',t'). !c x:A y:A. (s x = s' y) ==> (t c x = t' c y)") lemma)
    let cth ← ExceptT.mk (HolCore.Tactics.prove HolBase.B (← lhand (concl pth)) (MESON_TAC []))
    prove
     r"!clauses.
        (?(<<). WF (<<) /\
                ALL (\(s,t). tailadmissible(<<) (\f a. T) s t) clauses) /\
        ALL (\(s,t). !f x y. (s x = s y) ==> (t f x = t f y)) clauses /\
        PAIRWISE (\(s,t) (s',t'). !f x y. (s x = s' y) ==> (t f x = t' f y))
                 clauses
        ==> (?f. ALL (\(s,t). !x. f (s x) = t f x) clauses)"
     (REWRITE_TAC [← GSYM (← MATCH_MP pth cth), RIGHT_IMP_FORALL_THM] THEN
      REWRITE_TAC [RECURSION_CASEWISE])

  let SUPERADMISSIBLE_T ← prove
   r"superadmissible(<<) (\f x. T) s t <=> tailadmissible(<<) (\f x. T) s t"
   (REWRITE_TAC [superadmissible, admissible])

  let RECURSION_SUPERADMISSIBLE ← REWRITE_RULE [← GSYM SUPERADMISSIBLE_T]
        RECURSION_CASEWISE_PAIRWISE

  return {
    WF_REC_TAIL_GENERAL_prime, WF_REC_CASES, WF_REC_CASES_prime,
    RECURSION_CASEWISE, RECURSION_CASEWISE_PAIRWISE, SUPERADMISSIBLE_T,
    RECURSION_SUPERADMISSIBLE }

/- ---------------------------------------------------------------------- -/
/- The main suite of functions for justifying recursion (define.ml 464-953). -/
/- ---------------------------------------------------------------------- -/

/-- define.ml 467-953 is ONE binding of three names,
      let instantiate_casewise_recursion,
          pure_prove_recursive_function_exists,
          prove_general_recursive_function_exists = ...
    whose local helpers and lemmas are built once, when the binding is
    evaluated.  `setupDefineSuite` is that evaluation; this structure holds
    the three public names, the local helpers Session also exposes, and the
    once-proved lemmas (for the tests' forcing probes). -/
structure DefineSuite where
  SIMPLIFY_WELLDEFINEDNESS_CONV : ioconv
  EXISTS_PAT_CONV : ioconv
  HACK_PROFORMA : Int → thm → IO (Except String thm)
  EACK_PROFORMA : Int → thm → IO (Except String thm)
  APPLY_PROFORMA_TAC : thm → tactic
  SIMPLIFY_MATCH_WELLDEFINED_TAC : tactic
  MAIN_ADMISS_TAC : tactic
  ADMISS_TAC : tactic
  instantiate_casewise_recursion : ioconv
  pure_prove_recursive_function_exists : ioconv
  prove_general_recursive_function_exists : ioconv
  eq_refl : thm
  elemma0 : thm
  elemma1 : thm
  smw_pth0 : thm
  smw_pth1 : thm
  epa_pth0 : thm
  epa_pth1 : thm
  pth_lexleft : thm
  pth_lexright : thm
  pth_measure : thm
  deriving Inhabited

/-- `is_pattern` (define.ml 607-610). -/
def is_pattern (p : String) (n : Nat) (tm : term) : Bool :=
  match (do
    let (f, args) := strip_comb (strip_exists (← body (← body tm))).2
    pure (is_const f && Printer.name_of f == p && args.length == n)
    : Except String Bool) with
  | .ok b => b
  | .error _ => false

/-- `headonly` (define.ml 624-628). -/
def headonly (f : term) : term → Bool
  | .Comb s t => headonly f s && headonly f t && !(t == f)
  | .Abs _ t => headonly f t
  | _ => true

/-- The recursive `EXISTS_PAT_CONV` of define.ml 539-541. -/
partial def existsPatConv [HolBase] (pushcnv basecnv : ioconv) : ioconv := fun tm =>
  ((pushcnv THENC BINDER_CONV (existsPatConv pushcnv basecnv)) ORELSEC basecnv) tm

/-- The recursive `conv` of `EXPAND_PAIRED_ALL_CONV` (define.ml 706-708). -/
partial def expandPairedAllConv [HolBase] (conv0 conv1 : ioconv) : ioconv := fun tm =>
  ExceptT.run <| tryWith (ExceptT.mk (conv0 tm)) (do
    let th ← ExceptT.mk (conv1 tm)
    CONV_RULE (RAND_CONV (RAND_CONV (expandPairedAllConv conv0 conv1))) th)

/-- `depair` of `FORALL_PAIR_CONV` (define.ml 725-728). -/
partial def forallDepair [HolBase] (rule : thm → ExceptT String IO thm) :
    List term → term → IO (Except String thm)
  | [_], t => pure (.ok (REFL t))
  | _ :: vs, t => ExceptT.run do rule (← ExceptT.mk (BINDER_CONV (forallDepair rule vs) t))
  | [], _ => pure (.error "FORALL_PAIR_CONV")

/-- `GUESS_WF_THEN` (define.ml 923-929). -/
partial def guessWfThen [HolBase] (pth_lexleft pth_lexright pth_measure : thm)
    (MEASURE MEASURE_LE FORALL_PAIR_THM : thm)
    (GUESS_MEASURE_THEN : tactic → tactic) (tac : tactic) : tactic := fun g =>
  let self := guessWfThen pth_lexleft pth_lexright pth_measure MEASURE MEASURE_LE
                FORALL_PAIR_THM GUESS_MEASURE_THEN
  ((MATCH_MP_TAC pth_lexleft THEN self (self tac)) ORELSE
   (MATCH_MP_TAC pth_lexright THEN self (self tac)) ORELSE
   (MATCH_MP_TAC pth_measure THEN
    REWRITE_TAC [MEASURE, MEASURE_LE] THEN
    REWRITE_TAC [FORALL_PAIR_THM] THEN
    GUESS_MEASURE_THEN tac)) g

/-- define.ml 467-953: evaluate the binding. -/
@[nospecialize]
def setupDefineSuite [HolBase]
    (MESON_TAC : List thm → tactic)
    (MESON : List thm → term → IO (Except String thm))
    (ARITH_RULE : term → IO (Except String thm))
    (ARITH_TAC : tactic)
    (GEN_BETA_CONV FORALL_UNWIND_CONV : ioconv)
    (basic_rectype_net : IO (HolCore.Nets.net Simp.gconv))
    (prove_recursive_functions_exist : thm → term → IO (Except String thm))
    (inductive_type_store : IO (List (String × (Int × thm × thm))))
    (mk_small_numeral : Int → Except String term)
    (DAdmT : DefineAdmissibleThms) (DSupT : DefineSuperadmissibleThms)
    (DWfC : DefineWfCasewise)
    (EQ_ADD_RCANCEL EQ_ADD_LCANCEL EQ_ADD_RCANCEL_0 EQ_ADD_LCANCEL_0 : thm)
    (EQ_MULT_RCANCEL EQ_MULT_LCANCEL EQ_REFL : thm)
    (ADD_EQ_0 MULT_EQ_0 MULT_EQ_1 ARITH_EQ : thm)
    (EVEN_MULT EVEN_ADD ARITH EVEN : thm)
    (UNGUARDED_PATTERN GUARDED_PATTERN GEQ_DEF SWAP_EXISTS_THM : thm)
    (FUN_EQ_THM FORALL_PAIR_THM EXISTS_PAIR_THM EQ_IMP : thm)
    (AND_CLAUSES OR_CLAUSES IMP_CLAUSES EQ_CLAUSES NOT_CLAUSES FORALL_SIMP : thm)
    (ALL PAIRWISE CONJ_ASSOC EXISTS_REFL LET_DEF LET_END_DEF : thm)
    (WF_LEX ETA_AX WF_MEASURE_GEN WF_MEASURE WF_FALSE : thm)
    (MEASURE MEASURE_LE MONO_EXISTS : thm) :
    ExceptT String IO DefineSuite := do

  let mkEq ← ExceptT.mk mk_eq
  let mkPair (a b : term) : ExceptT String IO term := ExceptT.mk (Pair.mk_pair (a, b))

  /- -- Make some basic simplification of conjunction of welldefinedness
     clauses (define.ml 472-527). -- -/

  let LSYM : thm → ExceptT String IO thm :=
    GEN_ALL o CONV_RULE (LAND_CONV (ONCE_DEPTH_CONV SYM_CONV)) o SPEC_ALL
  let evensimps ← prove
   r"((2 * m + 2 = 2 * n + 1) <=> F) /\
     ((2 * m + 1 = 2 * n + 2) <=> F) /\
     ((2 * m = 2 * n + 1) <=> F) /\
     ((2 * m + 1 = 2 * n) <=> F) /\
     ((2 * m = SUC(2 * n)) <=> F) /\
     ((SUC(2 * m) = 2 * n) <=> F)"
   (REWRITE_TAC [] THEN REPEAT CONJ_TAC THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q "EVEN")) THEN
    REWRITE_TAC [EVEN_MULT, EVEN_ADD, ARITH, EVEN])
  /- The list literal is evaluated last element first. -/
  let arith2 ← ExceptT.mk (ARITH_RULE
    (← q r"(1 = m + n) <=> (m = 1) /\ (n = 0) \/ (m = 0) /\ (n = 1)"))
  let arith1 ← ExceptT.mk (ARITH_RULE
    (← q r"(m + n = 1) <=> (m = 1) /\ (n = 0) \/ (m = 0) /\ (n = 1)"))
  let lMultEq1 ← LSYM MULT_EQ_1
  let lMultEq0 ← LSYM MULT_EQ_0
  let lAddEq0 ← LSYM ADD_EQ_0
  let eqRefl ← EQT_INTRO (← SPEC_ALL EQ_REFL)
  let lAddL0 ← LSYM EQ_ADD_LCANCEL_0
  let lAddR0 ← LSYM EQ_ADD_RCANCEL_0
  let allsimps ←
    [EQ_ADD_RCANCEL, EQ_ADD_LCANCEL,
     EQ_ADD_RCANCEL_0, EQ_ADD_LCANCEL_0,
     lAddR0, lAddL0,
     EQ_MULT_RCANCEL, EQ_MULT_LCANCEL,
     eqRefl,
     ADD_EQ_0, lAddEq0,
     MULT_EQ_0, lMultEq0,
     MULT_EQ_1, lMultEq1,
     arith1, arith2,
     evensimps, ARITH_EQ].foldrM
      (fun th acc => ExceptT.mk (Simp.mk_rewrites HolBase.B false th acc)) []
  let simpTaut ← TAUT (← q r"((a <=> F) /\ (b <=> b) ==> ((a ==> b) <=> T)) /\
      ((a <=> a') /\ (a' ==> (b <=> T)) ==> ((a ==> b) <=> T)) /\
      ((a <=> a') /\ (a' ==> (b <=> b')) ==> ((a ==> b) <=> (a' ==> b')))")
  let (simp1, simp2, simp3) ← match CONJUNCTS simpTaut with
    | [c1, c2, c3] => pure (MATCH_MP c1, MATCH_MP c2, MATCH_MP c3)
    | _ => throw "SIMPLIFY_WELLDEFINEDNESS_CONV"
  let false_tm ← q "F"
  let and_tm ← q r"(/\)"
  let eq_refl ← EQT_INTRO (← SPEC_ALL EQ_REFL)
  /- The OCaml builds these two nets on every call; they do not depend on
     the call, so they are built here once. -/
  let andOrConv ← GEN_REWRITE_CONV_NET DEPTH_CONV [AND_CLAUSES, OR_CLAUSES]
  let forallSimpConv ← GEN_REWRITE_CONV_NET DEPTH_CONV [FORALL_SIMP, AND_CLAUSES]
  let SIMPLIFY_WELLDEFINEDNESS_CONV : ioconv := fun tm => ExceptT.run do
    let net ← allsimps.foldrM
      (fun th n => ExceptT.mk (Simp.net_of_thm HolBase.B false th n)) (← basic_rectype_net)
    let RECTYPE_ARITH_EQ_CONV := TOP_SWEEP_CONV (REWRITES_CONV net) THENC andOrConv
    let SIMPLIFY_CASE_DISTINCTNESS_CLAUSE : ioconv := fun tm => ExceptT.run do
      let (avs, bod) := strip_forall tm
      let (ant, cons) ← liftExcept (dest_imp bod)
      let ath ← ExceptT.mk (RECTYPE_ARITH_EQ_CONV ant)
      let atm ← liftExcept (rand (concl ath))
      let cth2 ← if atm == false_tm then pure (REFL cons)
        else do DISCH atm (← ExceptT.mk (PURE_REWRITE_CONV [eq_refl, ← ASSUME atm] cons))
      let bth ← CONJ ath cth2
      let cth ← tryWith (simp1 bth) (tryWith (simp2 bth) (simp3 bth))
      avs.foldrM MK_FORALL cth
    ExceptT.mk ((DEPTH_BINOP_CONV and_tm SIMPLIFY_CASE_DISTINCTNESS_CLAUSE THENC
                 forallSimpConv) tm)

  /- -- Simplify an existential question about a pattern (define.ml 528-545). -- -/

  let ep_pth ← prove
   r"((?y. _UNGUARDED_PATTERN (GEQ s t) (GEQ z y)) <=> s = t) /\
     ((?y. _GUARDED_PATTERN (GEQ s t) g (GEQ z y)) <=> g /\ s = t)"
   (REWRITE_TAC [UNGUARDED_PATTERN, GUARDED_PATTERN, GEQ_DEF] THEN
    MESON_TAC [])
  let basecnv ← GEN_REWRITE_CONV_NET id [ep_pth]
  let pushcnv ← GEN_REWRITE_CONV_NET id [SWAP_EXISTS_THM]
  let EXISTS_PAT_CONV : ioconv := fun tm =>
    if is_exists tm then existsPatConv pushcnv basecnv tm
    else pure (.error "EXISTS_PAT_CONV")

  /- -- Hack a proforma to introduce new pairing or pattern variables
     (define.ml 546-598). -- -/

  let elemma0 ← prove
   r"((!z. GEQ (f z) (g z)) <=> (!x y. GEQ (f(x,y)) (g(x,y)))) /\
     ((\p. P p) = (\(x,y). P(x,y)))"
   (REWRITE_TAC [FUN_EQ_THM, FORALL_PAIR_THM])
  let elemma1 ← prove
   r"(!P. (!t:A->B->C#D->E. P t) <=> (!t. P (\a b (c,d). t a b d c))) /\
     (!P. (!t:B->C#D->E. P t) <=> (!t. P (\b (c,d). t b d c))) /\
     (!P. (!t:C#D->E. P t) <=> (!t. P (\(c,d). t d c)))"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [] THENL
     [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"\a b d c. (t:A->B->C#D->E) a b (c,d)")),
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"\b d c. (t:B->C#D->E) b (c,d)")),
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"\d c. (t:C#D->E) (c,d)"))] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [FUN_EQ_THM, FORALL_PAIR_THM])
  /- `conv i` of HACK_PROFORMA/EACK_PROFORMA, for variable names `x`/`t`
     and type names `_P`/`_Q`. -/
  let renameConv (vname tname : String) (i : Int) : ioconv :=
    let name := vname ++ toString i
    let cnv := Equal.ALPHA_CONV (mk_var name (mk_vartype (tname ++ toString i)))
    fun tm => pure <|
      if is_abs tm && (match bndvar tm with
                       | .ok bv => Printer.name_of bv != name | .error _ => true)
      then cnv tm else .error "conv"
  let prodTy (tname : String) (n : Int) : ExceptT String IO hol_type :=
    end_itlist (fun s t => ExceptT.mk (mk_type "prod" [s, t]))
      ((upto 1 n).map (fun i => mk_vartype (tname ++ toString i)))
  let HACK_PROFORMA (n : Int) (th : thm) : IO (Except String thm) := ExceptT.run do
    if n <= 1 then return th
    let ty ← prodTy "_P" n
    let convs := FIRST_CONV ((upto 1 n).map (renameConv "x" "_P"))
    let th1 ← INST_TYPE [(ty, ← qty "P")] th
    let th2 ← REWRITE_RULE [FORALL_PAIR_THM] th1
    let th3 ← REWRITE_RULE [elemma0, elemma1] th2
    CONV_RULE (REDEPTH_CONV convs) th3
  let EACK_PROFORMA (n : Int) (th : thm) : IO (Except String thm) := ExceptT.run do
    if n <= 1 then return th
    let ty ← prodTy "_Q" n
    let convs := FIRST_CONV ((upto 1 n).map (renameConv "t" "_Q"))
    let th1 ← INST_TYPE [(ty, ← qty "Q")] th
    let th2 ← REWRITE_RULE [EXISTS_PAIR_THM] th1
    let th3 ← REWRITE_RULE [elemma1] th2
    let th4 ← REWRITE_RULE [FORALL_PAIR_THM] th3
    CONV_RULE (REDEPTH_CONV convs) th4

  /- -- Hack and apply (define.ml 599-691). -- -/

  let APPLY_PROFORMA_TAC (th : thm) : tactic := fun gl => ExceptT.run do
    let (vs, _) ← liftExcept (do dest_gabs (← body (← rand gl.2)))
    let n : Int := 1 + (splitlist Pair.dest_pair vs).1.length
    let hth ← ExceptT.mk (HACK_PROFORMA n th)
    ExceptT.mk ((MATCH_MP_TAC hth THEN BETA_TAC) gl)
  let smw_pth0 ← ExceptT.mk (MESON []
    (← q r"(a /\ x = k ==> x = y ==> d) ==> (a /\ x = k /\ y = k ==> d)"))
  let smw_pth1 ← ExceptT.mk (MESON []
    (← q r"(a /\ b /\ c /\ x = k ==> x = y ==> d)
           ==> (a /\ x = k /\ b /\ y = k /\ c ==> d)"))
  let SIMPLIFY_MATCH_WELLDEFINED_TAC : tactic :=
    REPEAT GEN_TAC THEN
    (MATCH_MP_TAC smw_pth1 ORELSE MATCH_MP_TAC smw_pth0) THEN
    CONV_TAC (RAND_CONV SIMPLIFY_WELLDEFINEDNESS_CONV) THEN
    PURE_REWRITE_TAC
      [AND_CLAUSES, IMP_CLAUSES, OR_CLAUSES, EQ_CLAUSES, NOT_CLAUSES]
  let MAIN_ADMISS_TAC : tactic := fun gl => ExceptT.run do
    let run (t : tactic) : ExceptT String IO HolCore.Tactics.goalstate := ExceptT.mk (t gl)
    let (had, args0) := strip_comb gl.2
    if !(is_const had) then throw "ADMISS_TAC"
    let (f, fbod) ← liftExcept (do dest_abs (← last args0))
    let (_, bod) ← liftExcept (dest_gabs fbod)
    let (hop, args) := strip_comb bod
    let hadN := Printer.name_of had
    let hopN := Printer.name_of hop
    let lastArg : Except String term := last args
    /- The guards that read `last args` raise when it fails; they are only
       evaluated when the names match. -/
    let seqGuard (h : String) : ExceptT String IO Bool :=
      if hadN == h && hopN == "_MATCH" then
        liftExcept (do pure (Printer.name_of (repeat' rator (← lastArg)) == "_SEQPATTERN"))
      else pure false
    let superSeq ← seqGuard "superadmissible"
    let admSeq ← seqGuard "admissible"
    let pat (p : String) (k : Nat) : Bool :=
      match lastArg with | .ok a => is_pattern p k a | .error _ => false
    let ratorF : Bool := is_comb bod && (match rator bod with | .ok r => r == f | .error _ => false)
    let eackArm (pth : thm) : ExceptT String IO HolCore.Tactics.goalstate := do
      let n := (strip_exists (← liftExcept (do body (← body (← lastArg))))).1.length
      let th ← ExceptT.mk (EACK_PROFORMA n pth)
      run (APPLY_PROFORMA_TAC th THEN CONJ_TAC THENL
            [SIMPLIFY_MATCH_WELLDEFINED_TAC, ALL_TAC])
    if hadN == "superadmissible" && hopN == "COND" then
      run (APPLY_PROFORMA_TAC DSupT.SUPERADMISSIBLE_COND)
    else if hadN == "superadmissible" && hopN == "_MATCH" && superSeq then
      run (APPLY_PROFORMA_TAC DSupT.SUPERADMISSIBLE_MATCH_SEQPATTERN THEN
           CONV_TAC (ONCE_DEPTH_CONV EXISTS_PAT_CONV))
    else if hadN == "superadmissible" && hopN == "_MATCH" &&
            pat "_UNGUARDED_PATTERN" 2 then
      eackArm DSupT.SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN
    else if hadN == "superadmissible" && hopN == "_MATCH" &&
            pat "_GUARDED_PATTERN" 3 then
      eackArm DSupT.SUPERADMISSIBLE_MATCH_GUARDED_PATTERN
    else if hadN == "superadmissible" && ratorF then
      run (APPLY_PROFORMA_TAC DSupT.SUPERADMISSIBLE_TAIL)
    else if hadN == "admissible" && hopN == "sum" then
      run (APPLY_PROFORMA_TAC DAdmT.ADMISSIBLE_SUM)
    else if hadN == "admissible" && hopN == "nsum" then
      run (APPLY_PROFORMA_TAC DAdmT.ADMISSIBLE_NSUM)
    else if hadN == "admissible" && hopN == "MAP" then
      run (APPLY_PROFORMA_TAC DAdmT.ADMISSIBLE_MAP)
    else if hadN == "admissible" && hopN == "_MATCH" && admSeq then
      run (APPLY_PROFORMA_TAC DAdmT.ADMISSIBLE_MATCH_SEQPATTERN THEN
           CONV_TAC (ONCE_DEPTH_CONV EXISTS_PAT_CONV))
    else if hadN == "admissible" && hopN == "_MATCH" then
      run (APPLY_PROFORMA_TAC DAdmT.ADMISSIBLE_MATCH)
    else if hadN == "admissible" && hopN == "_UNGUARDED_PATTERN" then
      run (APPLY_PROFORMA_TAC DAdmT.ADMISSIBLE_UNGUARDED_PATTERN)
    else if hadN == "admissible" && hopN == "_GUARDED_PATTERN" then
      run (APPLY_PROFORMA_TAC DAdmT.ADMISSIBLE_GUARDED_PATTERN)
    else if hadN == "admissible" && is_abs bod then
      run (APPLY_PROFORMA_TAC DAdmT.ADMISSIBLE_LAMBDA)
    else if hadN == "admissible" && ratorF then do
      if free_in f (← liftExcept (rand bod)) then
        run (APPLY_PROFORMA_TAC DAdmT.ADMISSIBLE_NEST)
      else
        run (APPLY_PROFORMA_TAC DAdmT.ADMISSIBLE_BASE)
    else if hadN == "admissible" && is_comb bod && headonly f bod then
      run (APPLY_PROFORMA_TAC DAdmT.ADMISSIBLE_COMB)
    else throw "MAIN_ADMISS_TAC"
  let ADMISS_TAC : tactic :=
    CONJ_TAC ORELSE
    MATCH_ACCEPT_TAC DAdmT.ADMISSIBLE_CONST ORELSE
    MATCH_ACCEPT_TAC DSupT.SUPERADMISSIBLE_CONST ORELSE
    MAIN_ADMISS_TAC ORELSE
    MATCH_MP_TAC DSupT.ADMISSIBLE_IMP_SUPERADMISSIBLE

  /- -- Instantiate the casewise recursion theorem for existential claim
     (define.ml 692-810). -- -/

  let (epa_pth0, epa_pth1) ← CONJ_PAIR (← prove
   r"(ALL (\(s,t). P s t) [a,b] <=> P a b) /\
     (ALL (\(s,t). P s t) (CONS (a,b) l) <=>
      P a b /\ ALL (\(s,t). P s t) l)"
   (REWRITE_TAC [ALL]))
  let EXPAND_PAIRED_ALL_CONV : ioconv :=
    expandPairedAllConv (REWR_CONV epa_pth0) (REWR_CONV epa_pth1)
  let gsymFPT ← GSYM FORALL_PAIR_THM
  let rewr1 ← GEN_REWRITE_CONV_NET id [gsymFPT]
  let rewr2 ← GEN_REWRITE_CONV_NET id [FUN_EQ_THM]
  let LAMBDA_PAIR_CONV (parms : List term) : ioconv := fun tm => ExceptT.run do
    let parm ← end_itlist mkPair parms
    let (x, bod) ← liftExcept (dest_abs tm)
    let tm' ← ExceptT.mk (mk_gabs parm ((← liftExcept (vsubst [(parm, x)])) bod))
    let th1 ← liftExcept (do Equal.BETA_CONV (← mk_comb tm parm))
    let th2 ← ExceptT.mk (GEN_BETA_CONV (← liftExcept (mk_comb tm' parm)))
    let th3 ← TRANS th1 (← SYM th2)
    let th4 ← (← liftExcept (butlast parms)).foldrM
      (fun v th => do CONV_RULE rewr1 (← GEN v th))
      (← GEN (← liftExcept (last parms)) th3)
    EQ_MP (← SYM (← ExceptT.mk (rewr2 (← liftExcept (mkEq (tm, tm')))))) th4
  let rule ← GEN_REWRITE_CONV_NET RAND_CONV [gsymFPT]
  let FORALL_PAIR_CONV (parm : term) (parms : List term) : ExceptT String IO thm := do
    let p := mk_var "P" (← ExceptT.mk (mk_fun_ty (type_of parm) bool_ty))
    let tm ← liftExcept (do list_mk_forall parms (← mk_comb p parm))
    GEN p (← SYM (← ExceptT.mk (forallDepair (CONV_RULE rule) parms tm)))
  let gsymCA ← GSYM CONJ_ASSOC
  let elimRw ← PURE_REWRITE_CONV_NET [PAIRWISE, ALL, gsymCA, AND_CLAUSES]
  let ELIM_LISTOPS_CONV : ioconv := elimRw THENC TOP_DEPTH_CONV GEN_BETA_CONV
  let tuple_function_existence (tm : term) : ExceptT String IO thm := do
    let (f, def_) ← liftExcept (dest_exists tm)
    let (domtys0, ranty0) := splitlist dest_fun_ty (type_of f)
    let nargs ← liftExcept ((conjuncts (strip_forall def_).2).foldrM
      (fun cj acc => do
        pure (Nat.max (strip_comb (← lhs (strip_forall cj).2)).2.length acc)) 0)
    let (domtys, midtys) ← liftExcept (chop_list nargs domtys0)
    let ranty ← midtys.foldrM (fun s t => ExceptT.mk (mk_fun_ty s t)) ranty0
    if domtys.length <= 1 then return (← ASSUME tm)
    let dty ← end_itlist (fun s t => ExceptT.mk (mk_type "prod" [s, t])) domtys
    let f' ← liftExcept (variant (frees tm)
      (mk_var (← liftExcept (dest_var f)).1 (← ExceptT.mk (mk_fun_ty dty ranty))))
    let gvs ← domtys.mapM (fun ty => do let g ← genvar ty; pure g)
    let gpair ← end_itlist mkPair gvs
    let f'' ← liftExcept (do list_mk_abs gvs (← mk_comb f' gpair))
    let def' ← ExceptT.mk ((← ExceptT.mk (subst [(f'', f)])) def_)
    let th1 ← EXISTS (tm, f'') (← ASSUME def')
    let bth ← ExceptT.mk (BETAS_CONV (← liftExcept (list_mk_comb f'' gvs)))
    let th2 ← ExceptT.mk (GEN_REWRITE_CONV TOP_DEPTH_CONV [bth] (← liftExcept (hd (hyp th1))))
    SIMPLE_CHOOSE f' (← PROVE_HYP (← UNDISCH (← EQ_IMP_RULE th2).2) th1)
  let pinstantiate_casewise_recursion (def_ : term) : ExceptT String IO thm :=
    tryWith (PART_MATCH pure EXISTS_REFL def_) (do
      let (f, bod) ← liftExcept (dest_exists def_)
      let cjs := conjuncts bod
      let eqs := cjs.map (fun c => (strip_forall c).2)
      let (lefts, rights) := unzip (← liftExcept (eqs.mapM dest_eq))
      let arglists := lefts.map (fun l => (strip_comb l).2)
      let parms0 := freesl (unions arglists)
      let parms ← if parms0 != [] then pure parms0 else do pure [← genvar aty]
      let parm ← end_itlist mkPair parms
      let ss ← arglists.mapM (fun a => do ExceptT.mk (mk_gabs parm (← end_itlist mkPair a)))
      let ts ← rights.mapM (fun a => do liftExcept (mk_abs f (← ExceptT.mk (mk_gabs parm a))))
      let clauses ← ExceptT.mk (HolMath.Lists.mk_flist
        (← (← liftExcept (map2 (fun s t => (s, t)) ss ts)).mapM (fun (s, t) => mkPair s t)))
      let pth ← ISPEC clauses DWfC.RECURSION_SUPERADMISSIBLE
      let FIDDLE_CONV (c : ioconv) : ioconv :=
        LAND_CONV (LAND_CONV (BINDER_CONV (RAND_CONV (LAND_CONV (Pair.GABS_CONV
          (RATOR_CONV (LAND_CONV (ABS_CONV c))))))))
      let th0 ← UNDISCH (← CONV_RULE (FIDDLE_CONV (LAMBDA_PAIR_CONV parms)) pth)
      let th1 ← EQ_MP (← liftExcept (Equal.GEN_ALPHA_CONV f (concl th0))) th0
      let rewr_forall_th := REWR_CONV (← FORALL_PAIR_CONV parm parms)
      let th2 ← CONV_RULE (BINDER_CONV
                  (LAND_CONV (Pair.GABS_CONV rewr_forall_th) THENC
                   EXPAND_PAIRED_ALL_CONV)) th1
      let (_, bod2) ← liftExcept (dest_exists (concl th2))
      let ths3 ← (CONJUNCTS (← ASSUME bod2)).mapM (fun th => do
        CONV_RULE (COMB2_CONV (RAND_CONV (RAND_CONV GEN_BETA_CONV))
                    (RATOR_CONV BETA_CONV THENC GEN_BETA_CONV)) (← SPEC_ALL th))
      let ths4 ← (← liftExcept (map2 (fun th t => (th, t)) ths3 cjs)).mapM (fun (th, t) => do
        let (avs, tbod) := strip_forall t
        avs.foldrM GEN (← PART_MATCH pure th tbod))
      let th5 ← SIMPLE_EXISTS f (← end_itlist CONJ ths4)
      let th6 ← PROVE_HYP th2 (← SIMPLE_CHOOSE f th5)
      let bconv := BINDER_CONV (BINDER_CONV rewr_forall_th THENC rewr_forall_th)
      let th7 ← ExceptT.mk (
        (RAND_CONV (COMB2_CONV
            (RAND_CONV (LAND_CONV (Pair.GABS_CONV bconv)))
            (LAND_CONV (Pair.GABS_CONV (Pair.GABS_CONV bconv)))) THENC
         ELIM_LISTOPS_CONV) (← liftExcept (hd (hyp th6))))
      let th8 ← PROVE_HYP (← UNDISCH (← EQ_IMP_RULE th7).2) th6
      let (wfasm, cdasm) ← liftExcept (do dest_conj (← hd (hyp th8)))
      let th9 ← PROVE_HYP (← CONJ (← ASSUME wfasm) (← ASSUME cdasm)) th8
      let th10 ← ExceptT.mk (SIMPLIFY_WELLDEFINEDNESS_CONV cdasm)
      let th11 ← PROVE_HYP (← UNDISCH (← EQ_IMP_RULE th10).2) th9
      PROVE_HYP HolBase.B.TRUTH th11)
  let instantiate_casewise_recursion : ioconv := fun etm => ExceptT.run do
    let eth ← tuple_function_existence etm
    let dth ← pinstantiate_casewise_recursion (← liftExcept (hd (hyp eth)))
    PROVE_HYP dth eth

  /- -- Justify existence assertion and try to simplify/remove side-conditions
     (define.ml 811-853). -- -/

  let break_down_admissibility (th1 : thm) : ExceptT String IO thm := do
    if hyp th1 == [] then return th1
    let (_, bod0) ← liftExcept (dest_exists (concl th1))
    let eqs := (conjuncts bod0).map (fun c => (strip_forall c).2)
    let (lefts, _) := unzip (← liftExcept (eqs.mapM dest_eq))
    let arglists := lefts.map (fun l => (strip_comb l).2)
    let parms0 := freesl (unions arglists)
    let parms ← if parms0 != [] then pure parms0 else do pure [← genvar aty]
    let wfasm ← liftExcept (find is_exists (hyp th1))
    let (ord, bod) ← liftExcept (dest_exists wfasm)
    let SIMP_ADMISS_TAC : tactic :=
      REWRITE_TAC [LET_DEF, LET_END_DEF] THEN
      REPEAT ADMISS_TAC THEN
      TRY (fun gl => ExceptT.run do
        let v := (← liftExcept (dest_forall gl.2)).1
        ExceptT.mk ((X_GEN_TAC v THEN
          MAP_EVERY
            (fun v => TRY (GEN_REWRITE_TAC id [FORALL_PAIR_THM]) THEN X_GEN_TAC v)
            parms THEN
          CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV) THEN
          MAP_EVERY (fun v => SPEC_TAC (v, v)) (parms.reverse ++ [v])) gl)) THEN
      PURE_REWRITE_TAC [FORALL_SIMP] THEN
      (fun gl => MAP_EVERY (fun t => SPEC_TAC (t, t)) (subtract (frees gl.2) [ord]) gl) THEN
      (fun gl => ExceptT.run do ExceptT.mk (ACCEPT_TAC (← ASSUME gl.2) gl))
    let th2 ← ExceptT.mk (HolCore.Tactics.TAC_PROOF HolBase.B ([], bod) SIMP_ADMISS_TAC)
    let th3 ← SIMPLE_EXISTS ord th2
    let allasms := hyp th3
    let wfasm ← liftExcept (lhand (concl th2))
    let th4 ← ASSUME (← liftExcept (list_mk_conj (wfasm :: subtract allasms [wfasm])))
    let th5 ← SIMPLE_CHOOSE ord (← (CONJUNCTS th4).foldrM PROVE_HYP th3)
    PROVE_HYP th5 th1
  let pure_prove_recursive_function_exists : ioconv := fun dtm => ExceptT.run do
    let th ← break_down_admissibility (← ExceptT.mk (instantiate_casewise_recursion dtm))
    if concl th == dtm then pure th
    else throw "prove_general_recursive_function_exists: sanity"

  /- -- Same, but attempt to prove the wellfoundedness hyp by good guesses
     (define.ml 854-953). -- -/

  let num_ty ← qty "num"
  let prove_depth_measure_exists (tyname : String) : ExceptT String IO thm := do
    let (_, _, sth) ← liftExcept (assoc tyname (← inductive_type_store))
    let (ty, zty) ← liftExcept (do
      dest_fun_ty (type_of (← dest_exists (strip_forall (concl sth)).2).1))
    let rth ← INST_TYPE [(num_ty, zty)] sth
    let (_, bod) := strip_forall (concl rth)
    let (_, cbod) ← liftExcept (dest_exists bod)
    let process_clause (k : Int) (t : term) : ExceptT String IO term := do
      let (avs, eq) := strip_forall t
      let (l, _) ← liftExcept (dest_eq eq)
      let (fn, cargs) ← liftExcept (dest_comb l)
      let (_, args) := strip_comb cargs
      let bargs := args.filter (fun a => type_of a == ty)
      let r' ← liftExcept (list_mk_binop (← q r"(+):num->num->num")
                ((← liftExcept (mk_small_numeral k)) :: (← liftExcept (bargs.mapM (mk_comb fn)))))
      liftExcept (do list_mk_forall avs (← mkEq (l, r')))
    let cjs := conjuncts cbod
    let def_ ← (← liftExcept (map2 (fun k t => (k, t)) (upto 1 (Int.ofNat cjs.length)) cjs)).mapM
      (fun (k, t) => process_clause k t)
    ExceptT.mk (prove_recursive_functions_exist sth (← liftExcept (list_mk_conj def_)))
  let INDUCTIVE_MEASURE_THEN (tac : tactic) : tactic := fun gl => ExceptT.run do
    let (ev, _) ← liftExcept (dest_exists gl.2)
    let ty := (← liftExcept (do dest_type (← dest_fun_ty (type_of ev)).1)).1
    let th ← prove_depth_measure_exists ty
    let (ev', _) ← liftExcept (dest_exists (concl th))
    let th' ← INST_TYPE (← liftExcept (type_match (type_of ev') (type_of ev) [])) th
    ExceptT.mk ((MP_TAC th' THEN MATCH_MP_TAC MONO_EXISTS THEN
                 GEN_TAC THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN tac) gl)
  let one_tm ← q "1"
  let CONSTANT_MEASURE_THEN (tac : tactic) : tactic := fun gl => ExceptT.run do
    let (ev, _) ← liftExcept (dest_exists gl.2)
    let (ty, _) ← liftExcept (dest_fun_ty (type_of ev))
    ExceptT.mk ((EXISTS_TAC (← liftExcept (mk_abs (← genvar ty) one_tm)) THEN tac) gl)
  let GUESS_MEASURE_THEN (tac : tactic) : tactic :=
    tactic_of (do pure (EXISTS_TAC (← q r"\n. n + 1") THEN tac)) ORELSE
    INDUCTIVE_MEASURE_THEN tac ORELSE
    CONSTANT_MEASURE_THEN tac
  let pth_lexleft ← prove
   r"(?r. WF(r) /\
          ?s. WF(s) /\
              P(\(x1,y1) (x2,y2). r x1 x2 \/ (x1 = x2) /\ s y1 y2))
     ==> ?t:A#B->A#B->bool. WF(t) /\ P t"
   (REPEAT STRIP_TAC THEN EXISTS_TAC
     (← q r"\(x1:A,y1:B) (x2:A,y2:B). r x1 x2 \/ (x1 = x2) /\ s y1 y2") THEN
    ASM_SIMP_TAC [WF_LEX])
  let pth_lexright ← prove
   r"(?r. WF(r) /\
          ?s. WF(s) /\
              P(\(x1,y1) (x2,y2). r y1 y2 \/ (y1 = y2) /\ s x1 x2))
     ==> ?t:A#B->A#B->bool. WF(t) /\ P t"
   (REPEAT STRIP_TAC THEN
    EXISTS_TAC (← q r"\u:A#B v:A#B.
                  (\(x1:B,y1:A) (x2:B,y2:A). r x1 x2 \/ (x1 = x2) /\ s y1 y2)
                   ((\(a,b). b,a) u) ((\(a,b). b,a) v)") THEN
    ASM_SIMP_TAC [WF_LEX, ETA_AX,
     ← ISPECL [← q "R:A#B->A#B->bool", ← q r"\(b:B,a:A). a,b"] WF_MEASURE_GEN] THEN
    FIRST_X_ASSUM (fun th => MP_TAC th THEN
                             MATCH_MP_TAC EQ_IMP THEN
                             AP_TERM_TAC) THEN
    REWRITE_TAC [FUN_EQ_THM, FORALL_PAIR_THM])
  let pth_measure ← prove
   r"(?m:A->num. P(MEASURE m)) ==> ?r:A->A->bool. WF(r) /\ P r"
   (MESON_TAC [WF_MEASURE])
  let GUESS_WF_THEN := guessWfThen pth_lexleft pth_lexright pth_measure
    MEASURE MEASURE_LE FORALL_PAIR_THM GUESS_MEASURE_THEN
  let PRE_GUESS_TAC : tactic :=
    CONV_TAC (BINDER_CONV (DEPTH_BINOP_CONV (← q r"(/\)")
     (TRY_CONV SIMPLIFY_WELLDEFINEDNESS_CONV THENC
      TRY_CONV FORALL_UNWIND_CONV)))
  let gfalse_tm ← q r"\x:A y:A. F"
  let GUESS_ORDERING_TAC : tactic :=
    (fun gl => ExceptT.run do
      let ty := (← liftExcept (do dest_fun_ty (type_of (← dest_exists gl.2).1))).1
      ExceptT.mk ((EXISTS_TAC (inst [(ty, aty)] gfalse_tm) THEN
                   REWRITE_TAC [WF_FALSE] THEN HolCore.Tactics.NO_TAC) gl)) ORELSE
    GUESS_WF_THEN (REWRITE_TAC [FORALL_PAIR_THM] THEN ARITH_TAC)
  let prove_general_recursive_function_exists : ioconv := fun etm => ExceptT.run do
    let th ← ExceptT.mk (pure_prove_recursive_function_exists etm)
    tryWith (do
      let wtm ← liftExcept (find is_exists (hyp th))
      let wth ← ExceptT.mk (HolCore.Tactics.prove HolBase.B wtm
                              (PRE_GUESS_TAC THEN GUESS_ORDERING_TAC))
      PROVE_HYP wth th)
      (pure th)

  return {
    SIMPLIFY_WELLDEFINEDNESS_CONV := SIMPLIFY_WELLDEFINEDNESS_CONV,
    EXISTS_PAT_CONV := EXISTS_PAT_CONV,
    HACK_PROFORMA := HACK_PROFORMA,
    EACK_PROFORMA := EACK_PROFORMA,
    APPLY_PROFORMA_TAC := APPLY_PROFORMA_TAC,
    SIMPLIFY_MATCH_WELLDEFINED_TAC := SIMPLIFY_MATCH_WELLDEFINED_TAC,
    MAIN_ADMISS_TAC := MAIN_ADMISS_TAC,
    ADMISS_TAC := ADMISS_TAC,
    instantiate_casewise_recursion := instantiate_casewise_recursion,
    pure_prove_recursive_function_exists := pure_prove_recursive_function_exists,
    prove_general_recursive_function_exists := prove_general_recursive_function_exists,
    eq_refl := eq_refl, elemma0 := elemma0, elemma1 := elemma1,
    smw_pth0 := smw_pth0, smw_pth1 := smw_pth1,
    epa_pth0 := epa_pth0, epa_pth1 := epa_pth1,
    pth_lexleft := pth_lexleft, pth_lexright := pth_lexright,
    pth_measure := pth_measure }

/- ---------------------------------------------------------------------- -/
/- Simple "define" function (define.ml 954-1028).                          -/
/- ---------------------------------------------------------------------- -/

/-- `define tm`.  The OCaml's last act, `the_definitions := th3 ::
    !the_definitions`, is left to Session: this takes the current list and
    returns the entry to prepend (`none` for a benign redefinition, which
    the OCaml does not record). -/
def define [HolBase]
    (prove_general_recursive_function_exists : ioconv)
    (new_specification : List String → thm → IO (Except String thm))
    (mk_mconst : String → hol_type → IO (Except String term))
    (the_definitions : List thm)
    (tm : term) : IO (Except String (thm × Option thm)) := ExceptT.run do
  let headOf (t : term) : Except String term := do
    pure (repeat' rator (← lhs (strip_forall t).2))
  let close_definition_clauses (tm : term) : ExceptT String IO (term × thm) := do
    let (avs, bod) := strip_forall tm
    let cjs := conjuncts bod
    let fs ← match cjs.mapM headOf with
      | .ok r => pure r
      | .error _ => throw "close_definition_clauses: non-equation"
    if (setify fs).length != 1 then
      throw "close_definition_clauses: defining multiple functions"
    let f ← liftExcept (hd fs)
    if mem f avs then throw "close_definition_clauses: fn quantified"
    let do_clause (t : term) : ExceptT String IO thm := do
      let (lvs, bod) := strip_forall t
      let fvs := subtract (frees (← liftExcept (lhs bod))) (f :: lvs)
      SPECL fvs (← ASSUME (← liftExcept (list_mk_forall fvs t)))
    let ths ← cjs.mapM do_clause
    let ajs ← liftExcept (ths.mapM (fun th => hd (hyp th)))
    let th ← ASSUME (← liftExcept (list_mk_conj ajs))
    pure (f, ← avs.foldrM GEN (← (CONJUNCTS th).foldrM PROVE_HYP (← end_itlist CONJ ths)))
  let type_instantiate_defining_const (t : term) : ExceptT String IO term := do
    let cjs := conjuncts t
    let fs ← liftExcept (cjs.mapM headOf)
    let f ← liftExcept (hd fs)
    if !(is_const f) then return t
    let fname := Printer.name_of f
    let f_occurs := find_terms
      (fun t' => is_const t' && Printer.name_of t' == fname && t' != f) t
    f_occurs.foldrM (fun f' t_updated => do
      liftExcept (Drule.instantiate (← term_match [] f' f) t_updated)) t
  let tm0 := (strip_forall tm).2
  tryWith (do
      let tm' ← type_instantiate_defining_const tm0
      let rec tryfindDef : List thm → ExceptT String IO (thm × thm)
        | [] => throw "tryfind"
        | th :: rest => tryWith (do pure (th, ← PART_MATCH pure th tm')) (tryfindDef rest)
      let (th, th') ← tryfindDef the_definitions
      if (← tryWith (do let _ ← PART_MATCH pure th' (concl th); pure true) (pure false)) then
        warn true "Benign redefinition"
        pure (th', none)
      else throw "")
    (do
      let (f, th) ← close_definition_clauses tm
      if !(is_var f) then
        let s ← Printer.string_of_term f
        throw s!"define: '{s}' is already defined"
      let etm ← liftExcept (do HolCore.Bool.mk_exists f (← hd (hyp th)))
      let th1 ← ExceptT.mk (prove_general_recursive_function_exists etm)
      let (fname, fty) ← liftExcept (dest_var f)
      let th2 ← ExceptT.mk (new_specification [fname] th1)
      let g ← ExceptT.mk (mk_mconst fname fty)
      let th3 ← PROVE_HYP th2 (← INST [(g, f)] th)
      pure (th3, some th3))

end

end HolMath.Define
