/- File: HolTest/IterateTest.lean
Tests for HolMath/Iterate.lean (iterate.ml).

Like `HolTest/SetsTest.lean` section (0), this file's forcing section is a
REGRESSION GUARD for the latent-defect trap: a bundle that is never FORCED is
never built, so a panic inside it (which degenerates every field of the bundle
to the `Inhabited` default `|-  = `) is INVISIBLE to the build - the
masked-failure detector reads its expected count and the build stays green.
That nearly hid real defects earlier in this project (SetsMisc/SetsCross, and a
deferred int.ml failure).

So this file FORCES every iterate.ml bundle translated so far, IN FILE ORDER,
through `Session.ensureIterate`, and then PRINTS a theorem that REALLY BELONGS
to each bundle, emitting the literal token MISMATCH if it is degenerate.
`IO.mkRef (concl th)` SUCCEEDS on a degenerate theorem, so we PRINT the theorem
and test for `|-  = `.  `make verify` greps for MISMATCH and counts `|-  = `.

RANGES LANDED: iterate.ml 18-165 (IterateSegments), 176-178 (NumsegConvPths),
196-277 (IterateSortSeg), 281-354 (IterateGeneric), 364-539 (IterateKey1),
546-703 (IterateKey2), 713-887 (IterateKey3), 896-1184 (IterateOrdered),
1188-1282 (IterateSpecial), 1288-1461 (IterateNsum1), 1462-1745 (IterateNsum2),
1746-1917 (IterateNsum3), 1920-1978 (IterateNsumCard, incl. EXPAND_NSUM_CONV),
1984-2211 (IterateSum1, under prioritize_real at 1982), 2219-2598 (IterateSum2),
2599-2778 (IterateSum3), 2779-2854 (IterateSum4, incl. EXPAND_SUM_CONV),
2855-3108 (IterateSum5, real polynomial functions).
-/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ====================================================================== -/
/- (0) FORCING GUARD: every iterate.ml bundle must build, in a bare        -/
/-     process, and its probe theorem must be NON-DEGENERATE.              -/
/- ====================================================================== -/

private def sqi (s : String) : String := (s.replace "\n" "").replace " " ""

/-- Force a theorem, PRINT it (so it lands in the build log), and reject the
    `Inhabited` default `|-  = ` a panicked `setupX` yields. -/
private unsafe def forceOk (lbl : String) (th : thm) : IO Unit := do
  let s ← HolCore.Printer.string_of_thm th
  if sqi s == "|-" || sqi s == "|-=" then
    IO.println s!"Iterate force {lbl} -> MISMATCH degenerate (setup panicked): {s}"
  else
    IO.println s!"Iterate force {lbl} -> OK {s}"

/- Enter through `Session.ensureIterate`, which forces every iterate.ml bundle
   IN FILE ORDER (after `ensureSets`), reproducing HOL Light's eager
   top-to-bottom load. -/
#eval Session.ensureIterate

-- IterateSegments (iterate.ml 18-165): the segment definition and a real
-- cardinality result.  `numseg` is the sole new_definition of the range.
#eval forceOk "IterateSegments/numseg" Session.numseg
#eval forceOk "IterateSegments/CARD_NUMSEG" Session.CARD_NUMSEG
-- NumsegConvPths (iterate.ml 176-178): the three MESON lemmas.
#eval forceOk "NumsegConvPths/pth_0" Session.NUMSEG_CONV_pth_0
#eval forceOk "NumsegConvPths/pth_2" Session.NUMSEG_CONV_pth_2
-- IterateSortSeg (iterate.ml 196-277): the two structured proofs.
#eval forceOk "IterateSortSeg/TOPOLOGICAL_SORT" Session.TOPOLOGICAL_SORT
#eval forceOk "IterateSortSeg/FINITE_INT_SEG" Session.FINITE_INT_SEG
-- IterateGeneric (iterate.ml 281-354): the four core definitions and their
-- theorems.  Probe each definition plus derived theorems of the bundle.
#eval forceOk "IterateGeneric/neutral" Session.neutral
#eval forceOk "IterateGeneric/monoidal" Session.monoidal
#eval forceOk "IterateGeneric/support" Session.support
#eval forceOk "IterateGeneric/iterate" Session.iterate
#eval forceOk "IterateGeneric/MONOIDAL_AC" Session.MONOIDAL_AC
#eval forceOk "IterateGeneric/IN_SUPPORT" Session.IN_SUPPORT
#eval forceOk "IterateGeneric/SUPPORT_SUPPORT" Session.SUPPORT_SUPPORT
#eval forceOk "IterateGeneric/SUPPORT_CLAUSES" Session.SUPPORT_CLAUSES
#eval forceOk "IterateGeneric/SUPPORT_DELTA" Session.SUPPORT_DELTA
#eval forceOk "IterateGeneric/FINITE_SUPPORT_DELTA" Session.FINITE_SUPPORT_DELTA
-- IterateKey1 (iterate.ml 364-539): the structural key lemmas.  Probe several
-- theorems that REALLY belong to this bundle (confirmed by grep against
-- iterate.ml 364-539), including the recursion clauses and inclusion-exclusion.
#eval forceOk "IterateKey1/ITERATE_SUPPORT" Session.ITERATE_SUPPORT
#eval forceOk "IterateKey1/ITERATE_CLAUSES_GEN" Session.ITERATE_CLAUSES_GEN
#eval forceOk "IterateKey1/ITERATE_CLAUSES" Session.ITERATE_CLAUSES
#eval forceOk "IterateKey1/ITERATE_UNION" Session.ITERATE_UNION
#eval forceOk "IterateKey1/ITERATE_INCL_EXCL" Session.ITERATE_INCL_EXCL
#eval forceOk "IterateKey1/ITERATE_CLOSED" Session.ITERATE_CLOSED
#eval forceOk "IterateKey1/ITERATE_DELETE" Session.ITERATE_DELETE
-- IterateKey2 (iterate.ml 546-703): the mapping/congruence key lemmas.
#eval forceOk "IterateKey2/ITERATE_DELTA" Session.ITERATE_DELTA
#eval forceOk "IterateKey2/ITERATE_IMAGE" Session.ITERATE_IMAGE
#eval forceOk "IterateKey2/ITERATE_BIJECTION" Session.ITERATE_BIJECTION
#eval forceOk "IterateKey2/ITERATE_ITERATE_PRODUCT" Session.ITERATE_ITERATE_PRODUCT
#eval forceOk "IterateKey2/ITERATE_EQ" Session.ITERATE_EQ
#eval forceOk "IterateKey2/ITERATE_EQ_GENERAL" Session.ITERATE_EQ_GENERAL
#eval forceOk "IterateKey2/ITERATE_OP" Session.ITERATE_OP
-- IterateKey3 (iterate.ml 713-887): superset/swap/image/cases + numseg clauses.
#eval forceOk "IterateKey3/ITERATE_SUPERSET" Session.ITERATE_SUPERSET
#eval forceOk "IterateKey3/ITERATE_SWAP" Session.ITERATE_SWAP
#eval forceOk "IterateKey3/ITERATE_IMAGE_NONZERO" Session.ITERATE_IMAGE_NONZERO
#eval forceOk "IterateKey3/ITERATE_IMAGE_GEN" Session.ITERATE_IMAGE_GEN
#eval forceOk "IterateKey3/ITERATE_CASES" Session.ITERATE_CASES
#eval forceOk "IterateKey3/ITERATE_OP_GEN" Session.ITERATE_OP_GEN
#eval forceOk "IterateKey3/ITERATE_CLAUSES_NUMSEG" Session.ITERATE_CLAUSES_NUMSEG
#eval forceOk "IterateKey3/ITERATE_PAIR" Session.ITERATE_PAIR
#eval forceOk "IterateKey3/ITERATE_REFLECT" Session.ITERATE_REFLECT
-- IterateOrdered (iterate.ml 896-1184): the ordered/non-commutative
-- generalisation `iterato` (introduced by new_specification) and its lemmas.
-- Each probe prints a theorem confirmed by grep to belong to iterate.ml
-- 896-1184; a degenerate `|-  = ` (from a panicked setup) emits MISMATCH.
#eval forceOk "IterateOrdered/iterato" Session.iterato
#eval forceOk "IterateOrdered/ITERATO_SUPPORT" Session.ITERATO_SUPPORT
#eval forceOk "IterateOrdered/ITERATO_EXPAND_CASES" Session.ITERATO_EXPAND_CASES
#eval forceOk "IterateOrdered/ITERATO_CLAUSES_GEN" Session.ITERATO_CLAUSES_GEN
#eval forceOk "IterateOrdered/ITERATO_CLAUSES" Session.ITERATO_CLAUSES
#eval forceOk "IterateOrdered/ITERATO_CLAUSES_EXISTS" Session.ITERATO_CLAUSES_EXISTS
#eval forceOk "IterateOrdered/ITERATO_EQ" Session.ITERATO_EQ
#eval forceOk "IterateOrdered/ITERATO_INDUCT" Session.ITERATO_INDUCT
#eval forceOk "IterateOrdered/ITERATO_CLOSED" Session.ITERATO_CLOSED
#eval forceOk "IterateOrdered/ITERATO_ITERATE" Session.ITERATO_ITERATE
#eval forceOk "IterateOrdered/ITERATO_CLAUSES_NUMSEG_LEFT" Session.ITERATO_CLAUSES_NUMSEG_LEFT

-- IterateSpecial (iterate.ml 1188-1282): the four iterated operations at three
-- types.  Probe each definition plus its recursion clauses (the `*_CLAUSES`
-- theorems each BELONG to this bundle - grep-confirmed in Iterate.lean).
#eval forceOk "IterateSpecial/nproduct" Session.nproduct
#eval forceOk "IterateSpecial/NPRODUCT_CLAUSES" Session.NPRODUCT_CLAUSES
#eval forceOk "IterateSpecial/iproduct" Session.iproduct
#eval forceOk "IterateSpecial/IPRODUCT_CLAUSES" Session.IPRODUCT_CLAUSES
#eval forceOk "IterateSpecial/product" Session.product
#eval forceOk "IterateSpecial/PRODUCT_CLAUSES" Session.PRODUCT_CLAUSES
#eval forceOk "IterateSpecial/isum" Session.isum
#eval forceOk "IterateSpecial/ISUM_CLAUSES" Session.ISUM_CLAUSES

/- ====================================================================== -/
/- (1) VERBATIM STATEMENT CHECKS: assert the four core definitions and a    -/
/-     representative theorem print exactly the iterate.ml statement.       -/
/- ====================================================================== -/

/-- Print `t`, reject degenerate `|-  = `, and compare (whitespace-squashed)
    against the expected iterate.ml statement. -/
private unsafe def thmIs (lbl expected : String) (t : thm) : IO Unit := do
  let s ← HolCore.Printer.string_of_thm t
  if sqi s == "|-" || sqi s == "|-=" then
    IO.println s!"{lbl} -> MISMATCH degenerate: {s}"
  else if sqi s == sqi expected then
    IO.println s!"{lbl} -> OK {s}"
  else
    IO.println s!"{lbl} -> MISMATCH got={sqi s} want={sqi expected}"

-- neutral (281): the SELECT-term definition.
#eval thmIs "(1) neutral"
  "|- forall op. neutral op = (@x. forall y. op x y = y /\\ op y x = y)" Session.neutral
-- monoidal (284).
#eval thmIs "(1) monoidal"
  ("|- forall op. monoidal op <=> (forall x y. op x y = op y x) /\\ " ++
   "(forall x y z. op x (op y z) = op (op x y) z) /\\ (forall x. op (neutral op) x = x)")
  Session.monoidal
-- support (298).
#eval thmIs "(1) support"
  "|- forall s f op. support op f s = {x | x IN s /\\ ~(f x = neutral op)}"
  Session.support
-- IN_SUPPORT (307): a derived membership theorem of the generic bundle.
#eval thmIs "(1) IN_SUPPORT"
  "|- forall op f x s. x IN support op f s <=> x IN s /\\ ~(f x = neutral op)"
  Session.IN_SUPPORT

/- ====================================================================== -/
/- (2) RUNTIME TYPE DISCIPLINE (iterate.ml 1188-1282): the four iterated      -/
/-     operations live at THREE types.  Under prioritize_num() a bare numeral -/
/-     is :num, so each :int/:real definition takes its type from the         -/
/-     explicit operator annotation.  Confirm the LHS constant's TYPE at      -/
/-     runtime; emit MISMATCH on the wrong type (defect class #5).            -/
/- ====================================================================== -/

/-- Print, and check, the type of the LHS constant of a `NAME = iterate ...`
    definition theorem.  `concl` is `const = rhs`; extract `const` and print
    its type, comparing (whitespace-squashed) to the expected type string. -/
private unsafe def defTypeIs (lbl expected : String) (t : thm) : IO Unit := do
  let c := HolCore.Kernel.concl t
  match c with
  | .Comb (.Comb _ l) _ => do
      let ts ← HolCore.Printer.string_of_type (HolCore.Kernel.type_of l)
      if sqi ts == sqi expected then
        IO.println s!"(2) TYPE {lbl} -> OK {ts}"
      else
        IO.println s!"(2) TYPE {lbl} -> MISMATCH got={sqi ts} want={sqi expected}"
  | _ => IO.println s!"(2) TYPE {lbl} -> MISMATCH unexpected-shape"

-- nproduct over :num, iproduct/isum over :int, product over :real.
#eval defTypeIs "nproduct" "(A->bool)->(A->num)->num" Session.nproduct
#eval defTypeIs "iproduct" "(A->bool)->(A->int)->int" Session.iproduct
#eval defTypeIs "product"  "(A->bool)->(A->real)->real" Session.product
#eval defTypeIs "isum"     "(A->bool)->(A->int)->int" Session.isum

/- ====================================================================== -/
/- (3) FORCING GUARD for the nsum half (iterate.ml 1288-1978).             -/
/-     Force each nsum bundle through `ensureIterate` (already run above)   -/
/-     and PRINT a theorem that REALLY BELONGS to it (grep-confirmed        -/
/-     against iterate.ml), emitting MISMATCH on the degenerate `|-  = `.   -/
/- ====================================================================== -/

-- IterateNsum1 (iterate.ml 1288-1461): nsum, the clauses, and structured
-- proofs (NSUM_LMUL 1361, NSUM_SWAP 1454) that really belong to this bundle.
#eval forceOk "IterateNsum1/nsum" Session.nsum
#eval forceOk "IterateNsum1/NEUTRAL_ADD" Session.NEUTRAL_ADD
#eval forceOk "IterateNsum1/MONOIDAL_ADD" Session.MONOIDAL_ADD
#eval forceOk "IterateNsum1/NSUM_CLAUSES" Session.NSUM_CLAUSES
#eval forceOk "IterateNsum1/NSUM_LMUL" Session.NSUM_LMUL
#eval forceOk "IterateNsum1/NSUM_LT" Session.NSUM_LT
#eval forceOk "IterateNsum1/NSUM_CONST" Session.NSUM_CONST
#eval forceOk "IterateNsum1/NSUM_SWAP" Session.NSUM_SWAP
-- IterateNsum2 (iterate.ml 1462-1745): the image/counting/subset lemmas and
-- the heaviest structured proofs (grep-confirmed in iterate.ml 1462-1745).
#eval forceOk "IterateNsum2/NSUM_IMAGE" Session.NSUM_IMAGE
#eval forceOk "IterateNsum2/NSUM_MULTICOUNT_GEN" Session.NSUM_MULTICOUNT_GEN
#eval forceOk "IterateNsum2/NSUM_GROUP_RELATION" Session.NSUM_GROUP_RELATION
#eval forceOk "IterateNsum2/NSUM_SUBSET" Session.NSUM_SUBSET
#eval forceOk "IterateNsum2/NSUM_LE_GEN" Session.NSUM_LE_GEN
#eval forceOk "IterateNsum2/NSUM_UNIONS_NONZERO" Session.NSUM_UNIONS_NONZERO
#eval forceOk "IterateNsum2/NSUM_CASES" Session.NSUM_CASES
-- IterateNsum3 (iterate.ml 1746-1917): closure/relation induction, numseg
-- theorems, modular arithmetic, and the congruence bundle.
#eval forceOk "IterateNsum3/NSUM_CLOSED" Session.NSUM_CLOSED
#eval forceOk "IterateNsum3/NSUM_RELATED" Session.NSUM_RELATED
#eval forceOk "IterateNsum3/NSUM_CLAUSES_NUMSEG" Session.NSUM_CLAUSES_NUMSEG
#eval forceOk "IterateNsum3/NSUM_REFLECT" Session.NSUM_REFLECT
#eval forceOk "IterateNsum3/MOD_NSUM_MOD" Session.MOD_NSUM_MOD
#eval forceOk "IterateNsum3/CONG_NSUM" Session.CONG_NSUM
#eval forceOk "IterateNsum3/NSUM_CONG" Session.NSUM_CONG
-- IterateNsumCard (iterate.ml 1920-1978): the two cardinality theorems and
-- EXPAND_NSUM_CONV's three proformas (the conversion itself is tested in (5)).
#eval forceOk "IterateNsumCard/CARD_UNIONS_IMAGE" Session.CARD_UNIONS_IMAGE
#eval forceOk "IterateNsumCard/CARD_UNIONS" Session.CARD_UNIONS
#eval forceOk "IterateNsumCard/EXPAND_NSUM_CONV_pth_0" Session.EXPAND_NSUM_CONV_pth_0
#eval forceOk "IterateNsumCard/EXPAND_NSUM_CONV_pth_1" Session.EXPAND_NSUM_CONV_pth_1
#eval forceOk "IterateNsumCard/EXPAND_NSUM_CONV_pth_2" Session.EXPAND_NSUM_CONV_pth_2

/- ====================================================================== -/
/- (4) nsum RUNTIME TYPE + NEUTRAL.  iterate.ml 1286 is prioritize_num(),   -/
/-     so `nsum` must type as `(A->bool)->(A->num)->num`, and its CLAUSES    -/
/-     theorem's neutral (the `{}` case) must be `0` (defect class #5).      -/
/- ====================================================================== -/

#eval defTypeIs "nsum" "(A->bool)->(A->num)->num" Session.nsum

-- NSUM_CLAUSES's first conjunct is `nsum {} f = 0`; confirm the neutral `0`.
#eval (do
  let s ← HolCore.Printer.string_of_thm Session.NSUM_CLAUSES
  let parts := (sqi s).splitOn "nsum{}f=0"
  if parts.length == 2 then
    IO.println s!"(4) NSUM_CLAUSES neutral -> OK 0  {s}"
  else
    IO.println s!"(4) NSUM_CLAUSES neutral -> MISMATCH no empty-set neutral 0: {s}" : IO Unit)

-- NEUTRAL_ADD states `neutral (+) = 0`, the neutral witness itself.
#eval thmIs "(4) NEUTRAL_ADD" "|- neutral (+) = 0" Session.NEUTRAL_ADD

/- ====================================================================== -/
/- (5) BEHAVIOURAL TEST of EXPAND_NSUM_CONV (iterate.ml 1951-1978).  A      -/
/-     forcing probe CANNOT reach a conversion (it is an `ioconv`, not a     -/
/-     `thm`), so drive it on a real term.  Task-mandated case: expanding    -/
/-     `nsum(1..4) f` for a SYMBOLIC `f:num->num` must peel all four         -/
/-     endpoints via `pth_2` and terminate at `pth_1`, giving RHS            -/
/-     `f 1 + f 2 + f 3 + f 4` (squashed `f1+f2+f3+f4`).  A conversion that   -/
/-     silently returned REFL, failed, or stopped early (residual `nsum` on   -/
/-     the RHS, or the degenerate `|-  = `) would differ and emit MISMATCH.  -/
/-     Precedent: sets.ml's HAS_SIZE_CONV was only ever exercised because a  -/
/-     theorem proof happened to call it - so this conversion gets its own   -/
/-     explicit behavioural driver here.                                     -/
/- ====================================================================== -/

#eval (do
  match ← HolCore.Parser.parse_term "nsum(1..4) (f:num->num)" with
  | .error e => IO.println s!"(5) EXPAND_NSUM_CONV -> MISMATCH parse: {e}"
  | .ok tm =>
    match ← Session.EXPAND_NSUM_CONV tm with
    | .error e => IO.println s!"(5) EXPAND_NSUM_CONV -> MISMATCH conv failed: {e}"
    | .ok th =>
      let s ← HolCore.Printer.string_of_thm th
      let sq := sqi s
      -- The conversion returns `|- nsum(1..4) f = f 1 + f 2 + f 3 + f 4`: the
      -- RHS is fully peeled to each endpoint (four `pth_2` steps closing on
      -- `pth_1`, terminal `0` absorbed).  The squashed theorem must end in the
      -- symbolic sum `=f1+f2+f3+f4`.  A degenerate, failed, or early-stopped
      -- result (residual `nsum(..)` on the RHS, or `|-  = `) would differ.
      if sq == "|-" || sq == "|-=" then
        IO.println s!"(5) EXPAND_NSUM_CONV -> MISMATCH degenerate: {s}"
      else if (sq.splitOn "=f1+f2+f3+f4").length == 2 then
        IO.println s!"(5) EXPAND_NSUM_CONV -> OK {s}"
      else
        IO.println s!"(5) EXPAND_NSUM_CONV -> MISMATCH unexpected RHS: {s}" : IO Unit)

/- ====================================================================== -/
/- (6) FORCING GUARD for the real sum bundles (iterate.ml 1984-2598).       -/
/-     `ensureIterate` (run above) forces `ensureIterateSumPrioritizeReal`   -/
/-     (iterate.ml 1982) then IterateSum1/IterateSum2 IN FILE ORDER.  PRINT  -/
/-     a theorem that REALLY BELONGS to each bundle (grep-confirmed against   -/
/-     iterate.ml), emitting MISMATCH on the degenerate `|-  = `.            -/
/- ====================================================================== -/

-- IterateSum1 (iterate.ml 1984-2211): sum, the clauses, and the structured
-- proofs SUM_LMUL (2052), SUM_LT (2086), SUM_POS_LE (2149),
-- SUM_ZERO_EXISTS (2177), SUM_SWAP (2211) that really belong to this bundle.
#eval forceOk "IterateSum1/sum" Session.sum
#eval forceOk "IterateSum1/NEUTRAL_REAL_ADD" Session.NEUTRAL_REAL_ADD
#eval forceOk "IterateSum1/MONOIDAL_REAL_ADD" Session.MONOIDAL_REAL_ADD
#eval forceOk "IterateSum1/SUM_CLAUSES" Session.SUM_CLAUSES
#eval forceOk "IterateSum1/SUM_LMUL" Session.SUM_LMUL
#eval forceOk "IterateSum1/SUM_LT" Session.SUM_LT
#eval forceOk "IterateSum1/SUM_POS_LE" Session.SUM_POS_LE
#eval forceOk "IterateSum1/SUM_ZERO_EXISTS" Session.SUM_ZERO_EXISTS
#eval forceOk "IterateSum1/SUM_SWAP" Session.SUM_SWAP
-- IterateSum2 (iterate.ml 2219-2598): the image/count/group/subset/general
-- lemmas and the heaviest structured proofs (grep-confirmed in 2219-2598).
#eval forceOk "IterateSum2/SUM_IMAGE" Session.SUM_IMAGE
#eval forceOk "IterateSum2/SUM_MULTICOUNT_GEN" Session.SUM_MULTICOUNT_GEN
#eval forceOk "IterateSum2/SUM_SUBSET" Session.SUM_SUBSET
#eval forceOk "IterateSum2/SUM_UNIONS_NONZERO" Session.SUM_UNIONS_NONZERO
#eval forceOk "IterateSum2/SUM_LE_INCLUDED" Session.SUM_LE_INCLUDED
#eval forceOk "IterateSum2/SUM_RELATED" Session.SUM_RELATED
#eval forceOk "IterateSum2/REAL_OF_NUM_SUM_GEN" Session.REAL_OF_NUM_SUM_GEN

/- ====================================================================== -/
/- (7) *** RUNTIME EVIDENCE THAT prioritize_real() TOOK EFFECT. ***         -/
/-     iterate.ml 1982 is prioritize_real(), THE FILE'S DEFINING HAZARD, so  -/
/-     from `sum` (1984) on a BARE NUMERAL parses `:real`, not `:num`.  Do   -/
/-     NOT assume - PROVE at runtime:                                        -/
/-       (a) `sum` types as (A->bool)->(A->real)->real (defect class #5:     -/
/-           under :num priority it would collide with `nsum`);              -/
/-       (b) SUM_CLAUSES's `{}` case prints the neutral `&0` (real), NOT `0`  -/
/-           (num) - if prioritize_real had NOT fired, `sum` would be `nsum`  -/
/-           and the neutral would print `0`;                                -/
/-       (c) a BARE numeral parsed AFTER the guard (post-`ensureIterate`)     -/
/-           comes out `:real` - the direct parser-state witness.            -/
/- ====================================================================== -/

-- (a) sum's LHS constant type must be (A->bool)->(A->real)->real.
#eval defTypeIs "sum" "(A->bool)->(A->real)->real" Session.sum

-- (b) SUM_CLAUSES's first conjunct is `sum {} f = &0`; confirm the neutral
-- prints `&0` (real) and NOT `0` (num).
#eval (do
  let s ← HolCore.Printer.string_of_thm Session.SUM_CLAUSES
  let sq := sqi s
  let hasReal := (sq.splitOn "sum{}f=&0").length == 2
  let hasNum := (sq.splitOn "sum{}f=0").length == 2
  if hasReal && !hasNum then
    IO.println s!"(7b) SUM_CLAUSES neutral -> OK &0 (real)  {s}"
  else
    IO.println s!"(7b) SUM_CLAUSES neutral -> MISMATCH expected &0 not 0: {s}" : IO Unit)

-- (b') NEUTRAL_REAL_ADD is the neutral witness itself: `neutral (+) = &0`.
#eval thmIs "(7b') NEUTRAL_REAL_ADD" "|- neutral (+) = &0" Session.NEUTRAL_REAL_ADD

-- (c) DIRECT parser-state witness.  `prioritize_real` (iterate.ml 1982)
-- re-maps OVERLOADED symbols (`+`, `<=`, ...) to `:real`; it is exactly what
-- makes `sum = iterate (+)` resolve `(+)` at `:real` rather than colliding
-- with `nsum`'s `(+):num->num->num`.  A bare *numeral* alone carries `:num`
-- inherently (nothing to prioritize), so the true witness is an OVERLOADED
-- operator with otherwise-unconstrained operands.  `#eval` runs each
-- elaboration in a fresh global parser state, so re-invoke the SAME side
-- effect the guard performs and confirm `+` then resolves at `:real`.
#eval (do
  let tyOf (s : String) : IO String := do
    match ← HolCore.Parser.parse_term s with
    | .ok tm => HolCore.Printer.string_of_type (HolCore.Kernel.type_of tm)
    | .error e => pure s!"parse-error:{e}"
  let before ← tyOf "x + y"
  Session.prioritize_real
  let after ← tyOf "x + y"
  if sqi after == "real" then
    IO.println s!"(7c) overloaded `x + y` type -> OK real after prioritize_real (was {before} before)"
  else
    IO.println s!"(7c) overloaded `x + y` type -> MISMATCH got={after} want=real (before={before})" : IO Unit)

/- ====================================================================== -/
/- (8) FORCING GUARD for IterateSum3 (iterate.ml 2599-2778): numseg          -/
/-     intervals and partial summation.  PRINT a theorem that REALLY BELONGS  -/
/-     to the bundle (grep-confirmed), MISMATCH on the degenerate `|-  = `.   -/
/- ====================================================================== -/

#eval forceOk "IterateSum3/SUM_ADD_NUMSEG" Session.SUM_ADD_NUMSEG
#eval forceOk "IterateSum3/SUM_CLAUSES_NUMSEG" Session.SUM_CLAUSES_NUMSEG
#eval forceOk "IterateSum3/SUM_SWAP_NUMSEG" Session.SUM_SWAP_NUMSEG
#eval forceOk "IterateSum3/SUM_CLAUSES_LEFT" Session.SUM_CLAUSES_LEFT
#eval forceOk "IterateSum3/SUM_REFLECT" Session.SUM_REFLECT
#eval forceOk "IterateSum3/SUM_PARTIAL_SUC" Session.SUM_PARTIAL_SUC
#eval forceOk "IterateSum3/SUM_PARTIAL_PRE" Session.SUM_PARTIAL_PRE
#eval forceOk "IterateSum3/SUM_DIFFS" Session.SUM_DIFFS
#eval forceOk "IterateSum3/SUM_COMBINE_L" Session.SUM_COMBINE_L

/- ---------------------------------------------------------------------- -/
/- (8b) MIXED-TYPE RUNTIME EVIDENCE for IterateSum3.  Every theorem in     -/
/-      iterate.ml 2599-2778 sums a `:real` summand over a `m..n` interval  -/
/-      whose INDICES are `:num` (from `numseg`).  Under prioritize_real    -/
/-      (iterate.ml 1982) this split is invisible to the compiler (defect   -/
/-      class #5), so PROVE it at runtime: parse a numseg sum with an       -/
/-      explicit real summand, confirm the whole `sum(..)` term types as    -/
/-      `:real`, and confirm the `m..n` interval subterm types as the set   -/
/-      `(num)->bool` (indices `:num`).  Emit MISMATCH on either deviation.  -/
/- ---------------------------------------------------------------------- -/

#eval (do
  match ← HolCore.Parser.parse_term "sum(m..n) (\\i. (f:num->real) i)" with
  | .error e => IO.println s!"(8b) IS3 mixed-type -> MISMATCH parse: {e}"
  | .ok tm => do
    -- Whole term: sum(m..n)(\i. f i) : real.
    let sumTy ← HolCore.Printer.string_of_type (HolCore.Kernel.type_of tm)
    -- tm = Comb (Comb sum (m..n)) (\i. f i); dig out the `m..n` interval.
    match tm with
    | .Comb (.Comb _ seg) _ => do
        let segTy ← HolCore.Printer.string_of_type (HolCore.Kernel.type_of seg)
        if sqi sumTy == "real" && sqi segTy == "num->bool" then
          IO.println s!"(8b) IS3 mixed-type -> OK sum:{sumTy} interval(m..n):{segTy}"
        else
          IO.println s!"(8b) IS3 mixed-type -> MISMATCH sum={sqi sumTy} (want real) interval={sqi segTy} (want num->bool)"
    | _ => IO.println s!"(8b) IS3 mixed-type -> MISMATCH unexpected-shape sum={sqi sumTy}" : IO Unit)

/- ====================================================================== -/
/- (9) FORCING GUARD for IterateSum4 (iterate.ml 2779-2854) and            -/
/-     IterateSum5 (iterate.ml 2855-3108).  PRINT a theorem that REALLY     -/
/-     BELONGS to each bundle (grep-confirmed), MISMATCH on `|-  = `.       -/
/- ====================================================================== -/

-- IterateSum4: the congruence SUM_CONG (registered via extend_basic_congs),
-- the EXPAND_SUM_CONV proformas, and the REAL_SUB_POW* rearrangements.
#eval forceOk "IterateSum4/SUM_CONG" Session.SUM_CONG
#eval forceOk "IterateSum4/EXPAND_SUM_CONV_pth_2" Session.EXPAND_SUM_CONV_pth_2
#eval forceOk "IterateSum4/REAL_SUB_POW" Session.REAL_SUB_POW
#eval forceOk "IterateSum4/REAL_SUB_POW_R1" Session.REAL_SUB_POW_R1
#eval forceOk "IterateSum4/REAL_SUB_POW_L1" Session.REAL_SUB_POW_L1
-- IterateSum5: the polynomial-difference/root-bound theorems, the definition,
-- and the closure properties (heaviest: REAL_POLYFUN_ROOTBOUND 2893,
-- POLYNOMIAL_FUNCTION_MUL 3023).
#eval forceOk "IterateSum5/REAL_SUB_POLYFUN" Session.REAL_SUB_POLYFUN
#eval forceOk "IterateSum5/REAL_SUB_POLYFUN_ALT" Session.REAL_SUB_POLYFUN_ALT
#eval forceOk "IterateSum5/REAL_POLYFUN_ROOTBOUND" Session.REAL_POLYFUN_ROOTBOUND
#eval forceOk "IterateSum5/REAL_POLYFUN_FINITE_ROOTS" Session.REAL_POLYFUN_FINITE_ROOTS
#eval forceOk "IterateSum5/REAL_POLYFUN_EQ_0" Session.REAL_POLYFUN_EQ_0
#eval forceOk "IterateSum5/REAL_POLYFUN_EQ_CONST" Session.REAL_POLYFUN_EQ_CONST
#eval forceOk "IterateSum5/polynomial_function" Session.polynomial_function
#eval forceOk "IterateSum5/POLYNOMIAL_FUNCTION_MUL" Session.POLYNOMIAL_FUNCTION_MUL
#eval forceOk "IterateSum5/POLYNOMIAL_FUNCTION_INDUCT" Session.POLYNOMIAL_FUNCTION_INDUCT
#eval forceOk "IterateSum5/POLYNOMIAL_FUNCTION_o" Session.POLYNOMIAL_FUNCTION_o
#eval forceOk "IterateSum5/POLYNOMIAL_FUNCTION_FINITE_ROOTS" Session.POLYNOMIAL_FUNCTION_FINITE_ROOTS

/- ====================================================================== -/
/- (10) BEHAVIOURAL TEST of EXPAND_SUM_CONV (iterate.ml 2799-2826), the     -/
/-      real mirror of the EXPAND_NSUM_CONV test (5).  A forcing probe       -/
/-      cannot reach a conversion, so drive it on a real term: expanding     -/
/-      `sum(1..4) (f:num->real)` must peel all four endpoints via `pth_2`   -/
/-      and terminate at `pth_1`, giving RHS `f 1 + f 2 + f 3 + f 4`         -/
/-      (squashed `f1+f2+f3+f4`).  A conversion that returned REFL, failed,   -/
/-      stopped early (residual `sum` on the RHS), or degenerated (`|-  = `)  -/
/-      would differ and emit MISMATCH.                                      -/
/- ====================================================================== -/

#eval (do
  match ← HolCore.Parser.parse_term "sum(1..4) (f:num->real)" with
  | .error e => IO.println s!"(10) EXPAND_SUM_CONV -> MISMATCH parse: {e}"
  | .ok tm =>
    match ← Session.EXPAND_SUM_CONV tm with
    | .error e => IO.println s!"(10) EXPAND_SUM_CONV -> MISMATCH conv failed: {e}"
    | .ok th =>
      let s ← HolCore.Printer.string_of_thm th
      let sq := sqi s
      if sq == "|-" || sq == "|-=" then
        IO.println s!"(10) EXPAND_SUM_CONV -> MISMATCH degenerate: {s}"
      else if (sq.splitOn "=f1+f2+f3+f4").length == 2 then
        IO.println s!"(10) EXPAND_SUM_CONV -> OK {s}"
      else
        IO.println s!"(10) EXPAND_SUM_CONV -> MISMATCH unexpected RHS: {s}" : IO Unit)

/- ====================================================================== -/
/- (11) THE PRIORITIZATION PAIR - iterate.ml 1982 and 3112.               -/
/- ====================================================================== -/
/- This is iterate.ml's DEFINING HAZARD and the first time in this
   development that prioritization changes PART WAY THROUGH a file:
       iterate.ml 1982  prioritize_real()   -- before `sum`  (1984)
       iterate.ml 3112  prioritize_num()    -- RESTORES :num
   Between them a bare numeral parses `:real`; after 3112 it parses `:num`
   again.  The 3112 call is HALF OF A PAIR (defect class #4): dropping it
   would silently mistype every LATER FILE, and NO compile error would say
   so.  It also needs its OWN once-only flag and its OWN direct call to
   `prioritize_num` - delegating to `ensurePrioritizeNum` (int.ml 2765)
   would be a NO-OP, because that flag was set during the int/sets chain
   (defect classes #3 and #4 combined).
   So we assert BOTH directions:
     (a) the real half kept its `:real` parse - `sum`'s neutral is `&0`,
         not the `0` that `nsum` has;
     (b) after `ensureIterate` (which ends with the 3112 restore) a bare
         numeral parses `:num`.
   Either one failing emits MISMATCH. -/
#eval (do
  Session.ensureIterate
  -- (a) the real half kept :real: sum's neutral must print `&0`, not `0`.
  let s ← HolCore.Printer.string_of_thm Session.SUM_CLAUSES
  if ((sqi s).splitOn "sum{}f=&0").length == 2 then
    IO.println s!"(11a) sum neutral is &0 (:real half intact) -> OK {s}"
  else
    IO.println s!"(11a) -> MISMATCH sum neutral not &0: {s}"
  -- (b) after the 3112 restore a bare numeral must parse :num.
  match ← HolCore.Parser.parse_term "1 + 1" with
  | .error e => IO.println s!"(11b) -> MISMATCH parse failed: {e}"
  | .ok tm =>
    let ty ← HolCore.Printer.string_of_type (HolCore.Kernel.type_of tm)
    if ty == "num" then
      IO.println s!"(11b) after 3112 restore `1 + 1` : {ty} -> OK"
    else
      IO.println s!"(11b) -> MISMATCH expected num after restore, got {ty}" : IO Unit)

/- ====================================================================== -/
/- (12) BEHAVIOURAL TEST of NUMSEG_CONV (iterate.ml 175-190).  It is the    -/
/-      FIRST of the file's three conversions and, like the other two, is    -/
/-      an `ioconv`, NOT a `thm` - a forcing probe (section 0 only forces    -/
/-      its three MESON pths) proves NOTHING about its behaviour: a          -/
/-      conversion that silently returned REFL or failed would pass every    -/
/-      forcing gate.  So drive it on a concrete `2..5` and assert it        -/
/-      evaluates to the EXPLICIT enumeration `{2, 3, 4, 5}` (squashed        -/
/-      `{2,3,4,5}`).  A REFL, a failure, an early stop (residual `..` on    -/
/-      the RHS), or the degenerate `|-  = ` would differ and emit MISMATCH.  -/
/- ====================================================================== -/

#eval (do
  match ← HolCore.Parser.parse_term "2..5" with
  | .error e => IO.println s!"(12) NUMSEG_CONV -> MISMATCH parse: {e}"
  | .ok tm =>
    match ← Session.NUMSEG_CONV tm with
    | .error e => IO.println s!"(12) NUMSEG_CONV -> MISMATCH conv failed: {e}"
    | .ok th =>
      let s ← HolCore.Printer.string_of_thm th
      let sq := sqi s
      if sq == "|-" || sq == "|-=" then
        IO.println s!"(12) NUMSEG_CONV -> MISMATCH degenerate: {s}"
      else if (sq.splitOn "=").length == 2 && (sq.splitOn "{2,3,4,5}").length == 2 then
        IO.println s!"(12) NUMSEG_CONV `2..5` -> OK {s}"
      else
        IO.println s!"(12) NUMSEG_CONV -> MISMATCH unexpected RHS: {s}" : IO Unit)

/- ====================================================================== -/
/- (13) `.hlp` DOCUMENTATION-EXAMPLE CHECKS.  Only three iterate.ml         -/
/-      bindings carry Help/ entries - NUMSEG_CONV.hlp, EXPAND_NSUM_CONV.hlp, -/
/-      EXPAND_SUM_CONV.hlp - and each documents a WORKED EXAMPLE.  Reproduce  -/
/-      each documented example against OUR implementation and assert the      -/
/-      documented result.  (The other candidate names - nsum, sum, iterate,   -/
/-      support, neutral, monoidal, numseg, nproduct, product, isum, iproduct,  -/
/-      polynomial_function, iterato, TOPOLOGICAL_SORT - have NO Help/ entry,   -/
/-      so there is nothing to reproduce for them.)  HOL Light docs have been   -/
/-      wrong repeatedly in this project; if an example fails to reproduce,     -/
/-      that is a documentation FINDING, not necessarily our bug.               -/
/- ====================================================================== -/

-- (13a) NUMSEG_CONV.hlp EXAMPLE 1: `NUMSEG_CONV `7..11`` = `|- 7..11 = {7,8,9,10,11}`.
#eval (do
  match ← HolCore.Parser.parse_term "7..11" with
  | .error e => IO.println s!"(13a) NUMSEG_CONV.hlp 7..11 -> MISMATCH parse: {e}"
  | .ok tm =>
    match ← Session.NUMSEG_CONV tm with
    | .error e => IO.println s!"(13a) NUMSEG_CONV.hlp 7..11 -> MISMATCH conv: {e}"
    | .ok th =>
      let sq := sqi (← HolCore.Printer.string_of_thm th)
      if (sq.splitOn "7..11={7,8,9,10,11}").length == 2 then
        IO.println s!"(13a) NUMSEG_CONV.hlp `7..11` -> OK reproduced {sq}"
      else
        IO.println ("(13a) NUMSEG_CONV.hlp `7..11` -> MISMATCH got=" ++ sq ++ " want=7..11={7,8,9,10,11}") : IO Unit)

-- (13b) NUMSEG_CONV.hlp EXAMPLE 2: `NUMSEG_CONV `24..7`` = `|- 24..7 = {}` (empty, n<m).
#eval (do
  match ← HolCore.Parser.parse_term "24..7" with
  | .error e => IO.println s!"(13b) NUMSEG_CONV.hlp 24..7 -> MISMATCH parse: {e}"
  | .ok tm =>
    match ← Session.NUMSEG_CONV tm with
    | .error e => IO.println s!"(13b) NUMSEG_CONV.hlp 24..7 -> MISMATCH conv: {e}"
    | .ok th =>
      let sq := sqi (← HolCore.Printer.string_of_thm th)
      if (sq.splitOn "24..7={}").length == 2 then
        IO.println s!"(13b) NUMSEG_CONV.hlp `24..7` -> OK reproduced {sq}"
      else
        IO.println ("(13b) NUMSEG_CONV.hlp `24..7` -> MISMATCH got=" ++ sq ++ " want=24..7={}") : IO Unit)

-- (13c) EXPAND_NSUM_CONV.hlp EXAMPLE: `EXPAND_NSUM_CONV `nsum (1..5) (\n. n * n)``
--       = `|- nsum(1..5)(\n. n*n) = 1*1 + 2*2 + 3*3 + 4*4 + 5*5`.
#eval (do
  match ← HolCore.Parser.parse_term "nsum (1..5) (\\n. n * n)" with
  | .error e => IO.println s!"(13c) EXPAND_NSUM_CONV.hlp -> MISMATCH parse: {e}"
  | .ok tm =>
    match ← Session.EXPAND_NSUM_CONV tm with
    | .error e => IO.println s!"(13c) EXPAND_NSUM_CONV.hlp -> MISMATCH conv: {e}"
    | .ok th =>
      let sq := sqi (← HolCore.Printer.string_of_thm th)
      if (sq.splitOn "=1*1+2*2+3*3+4*4+5*5").length == 2 then
        IO.println s!"(13c) EXPAND_NSUM_CONV.hlp `nsum(1..5)(\\n. n*n)` -> OK reproduced {sq}"
      else
        IO.println s!"(13c) EXPAND_NSUM_CONV.hlp -> MISMATCH got={sq} want RHS=1*1+2*2+3*3+4*4+5*5" : IO Unit)

-- (13d) EXPAND_SUM_CONV.hlp EXAMPLE: `EXPAND_SUM_CONV `sum(1..8) f``
--       = `|- sum(1..8) f = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8`.
#eval (do
  match ← HolCore.Parser.parse_term "sum(1..8) (f:num->real)" with
  | .error e => IO.println s!"(13d) EXPAND_SUM_CONV.hlp -> MISMATCH parse: {e}"
  | .ok tm =>
    match ← Session.EXPAND_SUM_CONV tm with
    | .error e => IO.println s!"(13d) EXPAND_SUM_CONV.hlp -> MISMATCH conv: {e}"
    | .ok th =>
      let sq := sqi (← HolCore.Printer.string_of_thm th)
      if (sq.splitOn "=f1+f2+f3+f4+f5+f6+f7+f8").length == 2 then
        IO.println s!"(13d) EXPAND_SUM_CONV.hlp `sum(1..8) f` -> OK reproduced {sq}"
      else
        IO.println s!"(13d) EXPAND_SUM_CONV.hlp -> MISMATCH got={sq} want RHS=f1+..+f8" : IO Unit)

/- ====================================================================== -/
/- (14) REAL BEHAVIOURAL CHECKS ON THE MATHEMATICS.  Forcing probes prove   -/
/-      only that a bundle built; these prove the theory actually COMPUTES   -/
/-      and PROVES.                                                          -/
/- ====================================================================== -/

-- (14a) A concrete `nsum` evaluated to a NUMERAL.  `EXPAND_NSUM_CONV` peels
-- `nsum(1..4)(\i. i)` to `1 + 2 + 3 + 4`; `NUM_REDUCE_CONV` then reduces that
-- to the single numeral `10`.  Chained via `thencIO`, the composite proves
-- `|- nsum(1..4)(\i. i) = 10` end-to-end - the num half really computes.
#eval (do
  match ← HolCore.Parser.parse_term "nsum(1..4) (\\i. i)" with
  | .error e => IO.println s!"(14a) nsum compute -> MISMATCH parse: {e}"
  | .ok tm =>
    match ← (HolCore.Simp.thencIO Session.EXPAND_NSUM_CONV Session.NUM_REDUCE_CONV) tm with
    | .error e => IO.println s!"(14a) nsum compute -> MISMATCH conv: {e}"
    | .ok th =>
      let sq := sqi (← HolCore.Printer.string_of_thm th)
      if (sq.splitOn "=10").length == 2 then
        IO.println s!"(14a) nsum(1..4)(\\i. i) = 10 -> OK {sq}"
      else
        IO.println s!"(14a) nsum compute -> MISMATCH got={sq} want RHS=10" : IO Unit)

-- (14b) A concrete `sum` evaluated to a REAL NUMERAL.  `EXPAND_SUM_CONV` peels
-- `sum(1..4)(\i. &i)` to `&1 + &2 + &3 + &4`; `REAL_RAT_REDUCE_CONV` reduces
-- that to `&10`.  Proves `|- sum(1..4)(\i. &i) = &10` - the real half computes.
#eval (do
  match ← HolCore.Parser.parse_term "sum(1..4) (\\i. &i)" with
  | .error e => IO.println s!"(14b) sum compute -> MISMATCH parse: {e}"
  | .ok tm =>
    match ← (HolCore.Simp.thencIO Session.EXPAND_SUM_CONV Session.REAL_RAT_REDUCE_CONV) tm with
    | .error e => IO.println s!"(14b) sum compute -> MISMATCH conv: {e}"
    | .ok th =>
      let sq := sqi (← HolCore.Printer.string_of_thm th)
      if (sq.splitOn "=&10").length == 2 then
        IO.println s!"(14b) sum(1..4)(\\i. &i) = &10 -> OK {sq}"
      else
        IO.println s!"(14b) sum compute -> MISMATCH got={sq} want RHS=&10" : IO Unit)

-- (14c) `iterate` INSTANTIATED at a monoidal operation, exercising the `<<=`
-- order of `iterato`.  ITERATO_ITERATE (iterate.ml 1127) states
-- `|- !op (<<=). monoidal op ==> iterato (:A) (neutral op) op (<<=) = iterate op`:
-- it names `iterate`, `iterato`, `monoidal`, AND the order `<<=` in one
-- theorem.  Assert the statement is non-degenerate and mentions all four.
#eval (do
  let s ← HolCore.Printer.string_of_thm Session.ITERATO_ITERATE
  let sq := sqi s
  if sq == "|-" || sq == "|-=" then
    IO.println s!"(14c) ITERATO_ITERATE -> MISMATCH degenerate: {s}"
  else if (sq.splitOn "monoidalop").length == 2 && (sq.splitOn "<<=").length != 1
          && (sq.splitOn "iterateop").length == 2 && (sq.splitOn "iterato").length != 1 then
    IO.println s!"(14c) ITERATO_ITERATE (iterate at monoidal op, <<= order) -> OK {s}"
  else
    IO.println s!"(14c) ITERATO_ITERATE -> MISMATCH missing monoidal/iterate/iterato/<<=: {sq}" : IO Unit)

-- (14d) A `polynomial_function` FACT: POLYNOMIAL_FUNCTION_ADD (iterate.ml 2985)
-- `|- !p q. polynomial_function p /\ polynomial_function q
--           ==> polynomial_function (\x. p x + q x)` - closure under addition.
#eval thmIs "(14d) POLYNOMIAL_FUNCTION_ADD"
  ("|- forall p q. polynomial_function p /\\ polynomial_function q " ++
   "==> polynomial_function (\\x. p x + q x)")
  Session.POLYNOMIAL_FUNCTION_ADD

-- (14e) TYPES STAYED DISTINCT across the prioritize_real/prioritize_num pair:
-- one theorem from the NUM half (NSUM_CLAUSES, neutral `0`) and one from the
-- REAL half (SUM_CLAUSES, neutral `&0`).  The num theorem must NOT carry `&0`
-- and the real theorem MUST - if the types had collided (defect class #5),
-- both would print the same neutral.
#eval (do
  let n := sqi (← HolCore.Printer.string_of_thm Session.NSUM_CLAUSES)
  let r := sqi (← HolCore.Printer.string_of_thm Session.SUM_CLAUSES)
  let numOk := (n.splitOn "nsum{}f=0").length == 2 && (n.splitOn "&0").length == 1
  let realOk := (r.splitOn "sum{}f=&0").length == 2
  if numOk && realOk then
    IO.println s!"(14e) num/real distinct -> OK nsum neutral=0, sum neutral=&0"
  else
    IO.println s!"(14e) num/real distinct -> MISMATCH nsum={n} (want 0, no &0) sum={r} (want &0)" : IO Unit)

/- ====================================================================== -/
/- (15) THE DEGENERATE `n < m` BRANCH OF BOTH EXPAND CONVERSIONS.          -/
/- ====================================================================== -/
/- Closing the only two MINOR findings of the five iterate.ml audits: the
   peeling branch (pth_2) and the terminating branch (pth_1) of both
   EXPAND_NSUM_CONV and EXPAND_SUM_CONV were behaviourally tested, but the
   EMPTY-SEGMENT branch `pth_0` (`n < m ==> ... = neutral`) was not - it was
   only FORCED, and forcing a proforma theorem says nothing about whether the
   conversion actually dispatches to it.  NUMSEG_CONV already had its
   degenerate case covered (`24..7 = {}`), so these two restore parity.
   Note the neutrals DIFFER BY TYPE and that is the point of the pair:
   `nsum` yields `0` at `:num` while `sum` yields `&0` at `:real`. -/

#eval (do
  match ← HolCore.Parser.parse_term "nsum(5..2) (f:num->num)" with
  | .error e => IO.println s!"(15a) EXPAND_NSUM_CONV n<m -> MISMATCH parse: {e}"
  | .ok tm =>
    match ← Session.EXPAND_NSUM_CONV tm with
    | .error e => IO.println s!"(15a) EXPAND_NSUM_CONV n<m -> MISMATCH conv failed: {e}"
    | .ok th =>
      let s ← HolCore.Printer.string_of_thm th
      let sq := sqi s
      if sq == "|-" || sq == "|-=" then
        IO.println s!"(15a) EXPAND_NSUM_CONV n<m -> MISMATCH degenerate: {s}"
      else if ((sq.splitOn "=0").length == 2) then
        IO.println s!"(15a) EXPAND_NSUM_CONV n<m (pth_0, num neutral 0) -> OK {s}"
      else
        IO.println s!"(15a) EXPAND_NSUM_CONV n<m -> MISMATCH unexpected RHS: {s}" : IO Unit)

#eval (do
  match ← HolCore.Parser.parse_term "sum(5..2) (f:num->real)" with
  | .error e => IO.println s!"(15b) EXPAND_SUM_CONV n<m -> MISMATCH parse: {e}"
  | .ok tm =>
    match ← Session.EXPAND_SUM_CONV tm with
    | .error e => IO.println s!"(15b) EXPAND_SUM_CONV n<m -> MISMATCH conv failed: {e}"
    | .ok th =>
      let s ← HolCore.Printer.string_of_thm th
      let sq := sqi s
      if sq == "|-" || sq == "|-=" then
        IO.println s!"(15b) EXPAND_SUM_CONV n<m -> MISMATCH degenerate: {s}"
      else if ((sq.splitOn "=&0").length == 2) then
        IO.println s!"(15b) EXPAND_SUM_CONV n<m (pth_0, real neutral &0) -> OK {s}"
      else
        IO.println s!"(15b) EXPAND_SUM_CONV n<m -> MISMATCH unexpected RHS: {s}" : IO Unit)
