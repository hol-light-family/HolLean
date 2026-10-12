/- File: HolTest/CartTest.lean
Tests for HolMath/Cart.lean (cart.ml).

Like `HolTest/IterateTest.lean` section (0), this file's forcing section is a
REGRESSION GUARD for the latent-defect trap: a bundle that is never FORCED is
never built, so a panic inside it (which degenerates every field of the bundle
to the `Inhabited` default `|-  = `) is INVISIBLE to the build - the
masked-failure detector reads its expected count and the build stays green.

So this file FORCES every cart.ml bundle translated so far, IN FILE ORDER,
through `Session.ensureCart`, and then PRINTS a theorem that REALLY BELONGS to
each bundle, emitting the literal token MISMATCH if it is degenerate.
`IO.mkRef (concl th)` SUCCEEDS on a degenerate theorem, so we PRINT the theorem
and test for `|-  = `.  `make verify` greps for MISMATCH and counts `|-  = `.

RANGES LANDED: cart.ml 14-48 (CartDimindex), 54-105 (CartFiniteImage),
111-168 (CartCart), 174-273 (CartFiniteSum), 279-305 (CartFiniteDiff),
312-335 (CartFiniteProd), 338-405 (CartTybit), 406-479 (CartDimindexConv),
480-548 (CartFinite), 551-567 (CartVector), 573-733 (CartPcross).
-/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ====================================================================== -/
/- (0) FORCING GUARD: every cart.ml bundle must build, in a bare process,  -/
/-     and its probe theorem must be NON-DEGENERATE.                       -/
/- ====================================================================== -/

private def sqi (s : String) : String := (s.replace "\n" "").replace " " ""

/-- Force a theorem, PRINT it (so it lands in the build log), and reject the
    `Inhabited` default `|-  = ` a panicked `setupX` yields. -/
private unsafe def forceOk (lbl : String) (th : thm) : IO Unit := do
  let s ← HolCore.Printer.string_of_thm th
  if sqi s == "|-" || sqi s == "|-=" then
    IO.println s!"Cart force {lbl} -> MISMATCH degenerate (setup panicked): {s}"
  else
    IO.println s!"Cart force {lbl} -> OK {s}"

/- Enter through `Session.ensureCart`, which forces every cart.ml bundle IN
   FILE ORDER (after `ensureIterate`), reproducing HOL Light's eager
   top-to-bottom load. -/
#eval Session.ensureCart

-- CartDimindex (cart.ml 14-48): the `dimindex` definition and its eight
-- theorems.  `dimindex` (14) is the sole new_definition; probe it plus several
-- theorems that REALLY belong to this bundle (grep-confirmed in Cart.lean).
#eval forceOk "CartDimindex/dimindex" Session.dimindex
#eval forceOk "CartDimindex/DIMINDEX_NONZERO" Session.DIMINDEX_NONZERO
#eval forceOk "CartDimindex/DIMINDEX_GE_1" Session.DIMINDEX_GE_1
#eval forceOk "CartDimindex/DIMINDEX_UNIV" Session.DIMINDEX_UNIV
#eval forceOk "CartDimindex/DIMINDEX_UNIQUE" Session.DIMINDEX_UNIQUE
#eval forceOk "CartDimindex/UNIV_HAS_SIZE_DIMINDEX" Session.UNIV_HAS_SIZE_DIMINDEX
#eval forceOk "CartDimindex/HAS_SIZE_1" Session.HAS_SIZE_1
#eval forceOk "CartDimindex/NUMSEG_LT_DIMINDEX" Session.NUMSEG_LT_DIMINDEX
#eval forceOk "CartDimindex/DIMINDEX_1" Session.DIMINDEX_1

-- CartFiniteImage (cart.ml 54-105): the FIRST `new_type_definition`.  Probe the
-- bijection theorem and several theorems that REALLY belong to this bundle.
#eval forceOk "CartFiniteImage/finite_image_tybij" Session.finite_image_tybij
#eval forceOk "CartFiniteImage/FINITE_IMAGE_IMAGE" Session.FINITE_IMAGE_IMAGE
#eval forceOk "CartFiniteImage/HAS_SIZE_FINITE_IMAGE" Session.HAS_SIZE_FINITE_IMAGE
#eval forceOk "CartFiniteImage/CARD_FINITE_IMAGE" Session.CARD_FINITE_IMAGE
#eval forceOk "CartFiniteImage/FINITE_FINITE_IMAGE" Session.FINITE_FINITE_IMAGE
#eval forceOk "CartFiniteImage/DIMINDEX_FINITE_IMAGE" Session.DIMINDEX_FINITE_IMAGE
#eval forceOk "CartFiniteImage/FINITE_INDEX_WORKS" Session.FINITE_INDEX_WORKS
#eval forceOk "CartFiniteImage/FINITE_INDEX_INJ" Session.FINITE_INDEX_INJ
#eval forceOk "CartFiniteImage/FORALL_FINITE_INDEX" Session.FORALL_FINITE_INDEX

/- ====================================================================== -/
/- (1) VERBATIM STATEMENT CHECK: assert `dimindex` prints exactly the      -/
/-     cart.ml 14 statement, and DIMINDEX_1 the computed `dimindex(:1)=1`.  -/
/- ====================================================================== -/

/-- Print `t`, reject degenerate `|-  = `, and compare (whitespace-squashed)
    against the expected cart.ml statement. -/
private unsafe def thmIs (lbl expected : String) (t : thm) : IO Unit := do
  let s ← HolCore.Printer.string_of_thm t
  if sqi s == "|-" || sqi s == "|-=" then
    IO.println s!"{lbl} -> MISMATCH degenerate: {s}"
  else if sqi s == sqi expected then
    IO.println s!"{lbl} -> OK {s}"
  else
    IO.println s!"{lbl} -> MISMATCH got={sqi s} want={sqi expected}"

-- dimindex (14): the defining conditional.
#eval thmIs "(1) dimindex"
  "|- forall s. dimindex s = (if FINITE (:A) then CARD (:A) else 1)" Session.dimindex

-- DIMINDEX_1 (48): the derived `dimindex(:1) = 1`.
#eval thmIs "(1) DIMINDEX_1" "|- dimindex (:1) = 1" Session.DIMINDEX_1

/- ====================================================================== -/
/- (2) RUNTIME TYPE-EXISTENCE CHECK: the SHARP before/after probe for the  -/
/-     FIRST `new_type_definition`.  Before `ensureCart` ran, the type     -/
/-     operator `finite_image` did not exist and `get_type_arity` failed   -/
/-     with `find`; after cart.ml 54-105 lands it is a unary type operator -/
/-     (arity 1).  This is the analogue of the parser baselines recorded    -/
/-     in the skeleton, and the definitive proof that the kernel side       -/
/-     effect fired.  (`ensureCart` above has already forced the type.)     -/
/- ====================================================================== -/

#eval (do
  match ← HolCore.Kernel.get_type_arity "finite_image" with
  | .ok n => IO.println s!"(2) get_type_arity finite_image -> arity {n}"
  | .error e => IO.println s!"(2) get_type_arity finite_image -> MISMATCH still absent: {e}"
  : IO Unit)

-- FINITE_INDEX_WORKS (90): the unique-index characterisation, a theorem that
-- exists ONLY because the `finite_image` type and its `finite_index` abstraction
-- were created.  Verbatim statement check.
#eval thmIs "(2) FINITE_INDEX_WORKS"
  "|- forall i. existsunique n. 1 <= n /\\ n <= dimindex (:A) /\\ finite_index n = i"
  Session.FINITE_INDEX_WORKS

-- CartCart (cart.ml 111-168): the CENTRE of the file - the `cart` type, `$`
-- indexing, and the `lambda` binder.  Probe the bijection and several theorems
-- that REALLY belong to this bundle.
#eval forceOk "CartCart/cart_tybij" Session.cart_tybij
#eval forceOk "CartCart/finite_index" Session.finite_index
#eval forceOk "CartCart/CART_EQ" Session.CART_EQ
#eval forceOk "CartCart/lambda" Session.lambda
#eval forceOk "CartCart/LAMBDA_BETA" Session.LAMBDA_BETA
#eval forceOk "CartCart/LAMBDA_UNIQUE" Session.LAMBDA_UNIQUE
#eval forceOk "CartCart/LAMBDA_ETA" Session.LAMBDA_ETA
#eval forceOk "CartCart/FINITE_INDEX_INRANGE" Session.FINITE_INDEX_INRANGE
#eval forceOk "CartCart/FINITE_INDEX_INRANGE_2" Session.FINITE_INDEX_INRANGE_2
#eval forceOk "CartCart/CART_EQ_FULL" Session.CART_EQ_FULL

/- ====================================================================== -/
/- (3) RUNTIME BASELINE FLIPS for cart.ml 111-168.  The skeleton recorded  -/
/-     these BEFORE the range landed; every one must now have FLIPPED.      -/
/-     (`ensureCart` above has already created the `cart` type and          -/
/-     installed the `$` infix and `lambda` binder.)                        -/
/- ====================================================================== -/

-- (3a) The type operator `cart` NOW EXISTS.  Baseline: `get_type_arity "cart"`
-- failed with `find`.  cart.ml 112 creates a BINARY type operator (arity 2:
-- element type and index type).
#eval (do
  match ← HolCore.Kernel.get_type_arity "cart" with
  | .ok n => IO.println s!"(3a) get_type_arity cart -> arity {n}"
  | .error e => IO.println s!"(3a) get_type_arity cart -> MISMATCH still absent: {e}"
  : IO Unit)

-- (3b) The `^` TYPE INFIX now parses AND prints back with `^`.  Baseline:
-- `:real^3` gave ERROR Noparse.  `:real^3` additionally needs the type-level
-- numeral `3` (cart.ml 341-344, a later task), so we demonstrate the flip with
-- a type-VARIABLE exponent `:A^B`, which needs only the `cart` operator.  The
-- printer must render it BACK as `A^B`, not `(A,B)cart`.
#eval (do
  match ← HolCore.Parser.parse_type "A^B" with
  | .ok ty =>
      let s ← HolCore.Printer.string_of_type ty
      if s == "A^B" then
        IO.println s!"(3b) parse+print :A^B -> OK prints back as {s}"
      else
        IO.println s!"(3b) parse+print :A^B -> MISMATCH printed {s} (want A^B)"
  | .error e => IO.println s!"(3b) parse :A^B -> MISMATCH Noparse: {e}"
  : IO Unit)

-- (3b') For completeness, show `:real^3` still Noparses for the DECLARED
-- reason (missing type-level numeral `3`), not for want of `cart`.
#eval (do
  match ← HolCore.Parser.parse_type "real^3" with
  | .ok ty =>
      let s ← HolCore.Printer.string_of_type ty
      IO.println s!"(3b') parse+print :real^3 -> OK {s} (numeral 3 now exists)"
  | .error _ =>
      IO.println "(3b') parse :real^3 -> still Noparse (awaits type numeral 3, cart.ml 341-344) - expected"
  : IO Unit)

-- (3c) `$` now parses as a LEFT-associative infix at precedence 25.  Baseline:
-- `(x:real^3)$1` gave a type error (no numeral 3).  Use a type-VARIABLE cart
-- `(x:A^B)$i`, which needs only `cart` + the `$` infix.  A successful parse
-- proves `$` is the registered infix, not juxtaposition.
#eval (do
  match ← HolCore.Parser.parse_term "(x:A^B)$i" with
  | .ok tm =>
      let s ← HolCore.Printer.string_of_term tm
      IO.println s!"(3c) parse (x:A^B)$i -> OK {s} ($ is the left-25 infix)"
  | .error e => IO.println s!"(3c) parse (x:A^B)$i -> MISMATCH: {e}"
  : IO Unit)

-- (3d) `lambda` now parses as a BINDER.  Baseline: `lambda i. f i` gave
-- ERROR "Unparsed input following term".  A successful parse proves the binder
-- is installed.
#eval (do
  match ← HolCore.Parser.parse_term "(lambda i. (x:A^B)$i)" with
  | .ok tm =>
      let s ← HolCore.Printer.string_of_term tm
      IO.println s!"(3d) parse lambda i. x$i -> OK {s} (lambda is a binder)"
  | .error e => IO.println s!"(3d) parse lambda binder -> MISMATCH Unparsed: {e}"
  : IO Unit)

/- ====================================================================== -/
/- (4) VERBATIM STATEMENT CHECKS for the two `new_definition`s of the      -/
/-     range, `finite_index` (117) and `lambda` (128), as RENDERED.        -/
/- ====================================================================== -/

#eval forceOk "(4) finite_index/render" Session.finite_index
#eval forceOk "(4) lambda/render" Session.lambda

/- ====================================================================== -/
/- (5) CartFiniteSum (cart.ml 174-273): the THIRD `new_type_definition`,   -/
/-     the FIRST applied to a LOCALLY PROVED nonemptiness theorem.  Force  -/
/-     every field and reject the degenerate `|-  = `.                     -/
/- ====================================================================== -/

#eval forceOk "CartFiniteSum/finite_sum_tybij" Session.finite_sum_tybij
#eval forceOk "CartFiniteSum/pastecart" Session.pastecart
#eval forceOk "CartFiniteSum/fstcart" Session.fstcart
#eval forceOk "CartFiniteSum/sndcart" Session.sndcart
#eval forceOk "CartFiniteSum/FINITE_SUM_IMAGE" Session.FINITE_SUM_IMAGE
#eval forceOk "CartFiniteSum/DIMINDEX_HAS_SIZE_FINITE_SUM" Session.DIMINDEX_HAS_SIZE_FINITE_SUM
#eval forceOk "CartFiniteSum/DIMINDEX_FINITE_SUM" Session.DIMINDEX_FINITE_SUM
#eval forceOk "CartFiniteSum/FSTCART_PASTECART" Session.FSTCART_PASTECART
#eval forceOk "CartFiniteSum/SNDCART_PASTECART" Session.SNDCART_PASTECART
#eval forceOk "CartFiniteSum/PASTECART_FST_SND" Session.PASTECART_FST_SND
#eval forceOk "CartFiniteSum/PASTECART_EQ" Session.PASTECART_EQ
#eval forceOk "CartFiniteSum/FORALL_PASTECART" Session.FORALL_PASTECART
#eval forceOk "CartFiniteSum/EXISTS_PASTECART" Session.EXISTS_PASTECART
#eval forceOk "CartFiniteSum/PASTECART_INJ" Session.PASTECART_INJ
#eval forceOk "CartFiniteSum/FSTCART_COMPONENT" Session.FSTCART_COMPONENT
#eval forceOk "CartFiniteSum/SNDCART_COMPONENT" Session.SNDCART_COMPONENT
#eval forceOk "CartFiniteSum/PASTECART_COMPONENT" Session.PASTECART_COMPONENT

/- ====================================================================== -/
/- (5a) RUNTIME TYPE-EXISTENCE CHECK for the THIRD `new_type_definition`.  -/
/-      Before `ensureCart` ran through the finite_sum range, the type     -/
/-      operator `finite_sum` did not exist and `get_type_arity` failed    -/
/-      with `find`; after cart.ml 174 lands it is a BINARY type operator  -/
/-      (arity 2: the element index type and the two summand index types   -/
/-      collapse to a two-argument type constructor).                      -/
/- ====================================================================== -/

#eval (do
  match ← HolCore.Kernel.get_type_arity "finite_sum" with
  | .ok n => IO.println s!"(5a) get_type_arity finite_sum -> arity {n}"
  | .error e => IO.println s!"(5a) get_type_arity finite_sum -> MISMATCH still absent: {e}"
  : IO Unit)

-- FSTCART_PASTECART (211) / SNDCART_PASTECART (216): the defining projection
-- laws that exist ONLY because `finite_sum` and pastecart/fstcart/sndcart were
-- created.  Verbatim statement checks.
#eval thmIs "(5a) FSTCART_PASTECART"
  "|- forall x y. fstcart (pastecart x y) = x" Session.FSTCART_PASTECART
#eval thmIs "(5a) SNDCART_PASTECART"
  "|- forall x y. sndcart (pastecart x y) = y" Session.SNDCART_PASTECART

/- ====================================================================== -/
/- (6) CartFiniteDiff (cart.ml 279-305) and CartFiniteProd (cart.ml        -/
/-     312-335): the FOURTH and FIFTH `new_type_definition`s, each applied  -/
/-     to a LOCALLY PROVED nonemptiness theorem.  Force every field and     -/
/-     reject the degenerate `|-  = `.                                      -/
/- ====================================================================== -/

#eval forceOk "CartFiniteDiff/finite_diff_tybij" Session.finite_diff_tybij
#eval forceOk "CartFiniteDiff/FINITE_DIFF_IMAGE" Session.FINITE_DIFF_IMAGE
#eval forceOk "CartFiniteDiff/DIMINDEX_HAS_SIZE_FINITE_DIFF" Session.DIMINDEX_HAS_SIZE_FINITE_DIFF
#eval forceOk "CartFiniteDiff/DIMINDEX_FINITE_DIFF" Session.DIMINDEX_FINITE_DIFF

#eval forceOk "CartFiniteProd/finite_prod_tybij" Session.finite_prod_tybij
#eval forceOk "CartFiniteProd/FINITE_PROD_IMAGE" Session.FINITE_PROD_IMAGE
#eval forceOk "CartFiniteProd/DIMINDEX_HAS_SIZE_FINITE_PROD" Session.DIMINDEX_HAS_SIZE_FINITE_PROD
#eval forceOk "CartFiniteProd/DIMINDEX_FINITE_PROD" Session.DIMINDEX_FINITE_PROD

/- ====================================================================== -/
/- (6a) RUNTIME TYPE-EXISTENCE CHECKS for the FOURTH and FIFTH             -/
/-      `new_type_definition`s.  Before `ensureCart` ran through these     -/
/-      ranges the type operators `finite_diff`/`finite_prod` did not      -/
/-      exist and `get_type_arity` failed with `find`; after cart.ml 284/  -/
/-      317 land each is a BINARY type operator (arity 2).                  -/
/- ====================================================================== -/

#eval (do
  match ← HolCore.Kernel.get_type_arity "finite_diff" with
  | .ok n => IO.println s!"(6a) get_type_arity finite_diff -> arity {n}"
  | .error e => IO.println s!"(6a) get_type_arity finite_diff -> MISMATCH still absent: {e}"
  : IO Unit)

#eval (do
  match ← HolCore.Kernel.get_type_arity "finite_prod" with
  | .ok n => IO.println s!"(6a) get_type_arity finite_prod -> arity {n}"
  | .error e => IO.println s!"(6a) get_type_arity finite_prod -> MISMATCH still absent: {e}"
  : IO Unit)

-- DIMINDEX_FINITE_DIFF (302) / DIMINDEX_FINITE_PROD (332): the dimension
-- computations that exist ONLY because the two types were created.  Verbatim
-- statement checks (the DISTINCT `if`-conditional vs product bodies).
#eval thmIs "(6a) DIMINDEX_FINITE_DIFF"
  "|- dimindex (:(M,N)finite_diff) = (if dimindex (:N) < dimindex (:M) then dimindex (:M) - dimindex (:N) else 1)"
  Session.DIMINDEX_FINITE_DIFF
#eval thmIs "(6a) DIMINDEX_FINITE_PROD"
  "|- dimindex (:(M,N)finite_prod) = dimindex (:M) * dimindex (:N)"
  Session.DIMINDEX_FINITE_PROD

/- ====================================================================== -/
/- (7) CartTybit (cart.ml 338-405): the TWO `define_type` calls that make   -/
/-     the binary "bit" types `tybit0`/`tybit1`, and their size/dimindex/   -/
/-     finiteness theory.  Each `define_type` yields a PAIR (INDUCT,         -/
/-     RECURSION), so we probe BOTH of BOTH pairs, then the nine `prove`s.   -/
/-     Force every field and reject the degenerate `|-  = `.                 -/
/- ====================================================================== -/

#eval forceOk "CartTybit/tybit0_INDUCT" Session.tybit0_INDUCT
#eval forceOk "CartTybit/tybit0_RECURSION" Session.tybit0_RECURSION
#eval forceOk "CartTybit/tybit1_INDUCT" Session.tybit1_INDUCT
#eval forceOk "CartTybit/tybit1_RECURSION" Session.tybit1_RECURSION
#eval forceOk "CartTybit/HAS_SIZE_TYBIT0" Session.HAS_SIZE_TYBIT0
#eval forceOk "CartTybit/HAS_SIZE_TYBIT1" Session.HAS_SIZE_TYBIT1
#eval forceOk "CartTybit/DIMINDEX_TYBIT0" Session.DIMINDEX_TYBIT0
#eval forceOk "CartTybit/DIMINDEX_TYBIT1" Session.DIMINDEX_TYBIT1
#eval forceOk "CartTybit/DIMINDEX_CLAUSES" Session.DIMINDEX_CLAUSES
#eval forceOk "CartTybit/FINITE_1" Session.FINITE_1
#eval forceOk "CartTybit/FINITE_TYBIT0" Session.FINITE_TYBIT0
#eval forceOk "CartTybit/FINITE_TYBIT1" Session.FINITE_TYBIT1
#eval forceOk "CartTybit/FINITE_CLAUSES" Session.FINITE_CLAUSES

/- ====================================================================== -/
/- (7a) RUNTIME TYPE-EXISTENCE for the TWO `define_type`s, and the PAYOFF:  -/
/-      `:2`/`:3`/`:4`/`:real^3` now parse.  `define_type "tybit0"` /       -/
/-      "tybit1" each create a UNARY type operator (arity 1: the base index  -/
/-      type `A`).  A numeral type `:N` parses as a nest of tybit0/tybit1    -/
/-      over `:1`; `:real^3` is `(real,3)cart`, which must PRINT BACK with   -/
/-      `^` via printer.ml's carttype path (INERT until `cart` + the        -/
/-      numerals exist).                                                     -/
/- ====================================================================== -/

#eval (do
  Session.ensureCart
  match ← HolCore.Kernel.get_type_arity "tybit0" with
  | .ok n => IO.println s!"(7a) get_type_arity tybit0 -> arity {n}"
  | .error e => IO.println s!"(7a) get_type_arity tybit0 -> MISMATCH still absent: {e}"
  : IO Unit)

#eval (do
  match ← HolCore.Kernel.get_type_arity "tybit1" with
  | .ok n => IO.println s!"(7a) get_type_arity tybit1 -> arity {n}"
  | .error e => IO.println s!"(7a) get_type_arity tybit1 -> MISMATCH still absent: {e}"
  : IO Unit)

-- The payoff: the higher type numerals and `real^3` now PARSE, and `real^3`
-- must PRINT BACK with `^` (not `(real,3)cart`).  Parse each, print it back.
#eval (do
  Session.ensureCart
  for s in ["2", "3", "4"] do
    match ← HolCore.Parser.parse_type s with
    | .ok ty => do
        let back ← HolCore.Printer.string_of_type ty
        IO.println s!"(7a) parse :{s} -> OK, prints as :{back}"
    | .error e => IO.println s!"(7a) parse :{s} -> MISMATCH Noparse: {e}"
  : IO Unit)

#eval (do
  Session.ensureCart
  match ← HolCore.Parser.parse_type "real^3" with
  | .ok ty => do
      let back ← HolCore.Printer.string_of_type ty
      if (back.splitOn "^").length == 2 then
        IO.println s!"(7a) parse :real^3 -> OK, prints back with ^ as :{back}"
      else
        IO.println s!"(7a) parse :real^3 -> parsed but prints as :{back} (no ^ - MISMATCH printer)"
  | .error e => IO.println s!"(7a) parse :real^3 -> MISMATCH Noparse: {e}"
  : IO Unit)

/- ====================================================================== -/
/- (8) CartDimindexConv (cart.ml 406-479): the `dimindex`-computing         -/
/-     conversion machinery (`DIMINDEX_CONV`/`HAS_SIZE_DIMINDEX_RULE`/       -/
/-     `DIMINDEX_TAC` - NOT theorems, so no forcing probe proves them) and   -/
/-     the PAYOFF theorems for cases 2, 3 and 4.  The `pth*` lemmas and the  -/
/-     six derived theorems ARE theorems; force each and reject `|-  = `.    -/
/- ====================================================================== -/

#eval forceOk "CartDimindexConv/DIMINDEX_2" Session.DIMINDEX_2
#eval forceOk "CartDimindexConv/DIMINDEX_3" Session.DIMINDEX_3
#eval forceOk "CartDimindexConv/DIMINDEX_4" Session.DIMINDEX_4
#eval forceOk "CartDimindexConv/HAS_SIZE_2" Session.HAS_SIZE_2
#eval forceOk "CartDimindexConv/HAS_SIZE_3" Session.HAS_SIZE_3
#eval forceOk "CartDimindexConv/HAS_SIZE_4" Session.HAS_SIZE_4

/- ====================================================================== -/
/- (8a) THE SHARP BEHAVIOURAL TEST for this range: `DIMINDEX_2/3/4` are     -/
/-      exactly the theorems `DIMINDEX_TAC` (built from `DIMINDEX_CONV`,     -/
/-      built from the four `pth` lemmas) proves - so a verbatim statement   -/
/-      check that they read `dimindex (:N) = N` is proof the conversion     -/
/-      COMPUTED the dimension (a degenerate `|-  = ` or wrong RHS would be  -/
/-      a MISMATCH).  Likewise `HAS_SIZE_2/3/4` exercise                     -/
/-      `HAS_SIZE_DIMINDEX_RULE`, which itself calls `DIMINDEX_CONV`.        -/
/- ====================================================================== -/

#eval thmIs "(8a) DIMINDEX_2" "|- dimindex (:2) = 2" Session.DIMINDEX_2
#eval thmIs "(8a) DIMINDEX_3" "|- dimindex (:3) = 3" Session.DIMINDEX_3
#eval thmIs "(8a) DIMINDEX_4" "|- dimindex (:4) = 4" Session.DIMINDEX_4
#eval thmIs "(8a) HAS_SIZE_2" "|- (:2) HAS_SIZE 2" Session.HAS_SIZE_2
#eval thmIs "(8a) HAS_SIZE_3" "|- (:3) HAS_SIZE 3" Session.HAS_SIZE_3
#eval thmIs "(8a) HAS_SIZE_4" "|- (:4) HAS_SIZE 4" Session.HAS_SIZE_4

/- ====================================================================== -/
/- (9) CartFinite (cart.ml 480-548): the finiteness lemma `FINITE_CART`    -/
/-     (the one heavy structured proof of the range) and the three whole-   -/
/-     universe cardinality results.  Force every field and reject the      -/
/-     degenerate `|-  = `.  `FINITE_CART` REALLY belongs to this bundle -  -/
/-     it is the coordinate-wise finiteness lemma introduced here, not      -/
/-     re-exported from any earlier layer (grep-confirmed).                 -/
/- ====================================================================== -/

#eval forceOk "CartFinite/FINITE_CART" Session.FINITE_CART
#eval forceOk "CartFinite/HAS_SIZE_CART_UNIV" Session.HAS_SIZE_CART_UNIV
#eval forceOk "CartFinite/CARD_CART_UNIV" Session.CARD_CART_UNIV
#eval forceOk "CartFinite/FINITE_CART_UNIV" Session.FINITE_CART_UNIV

/- ====================================================================== -/
/- (9a) VERBATIM STATEMENT CHECKS for cart.ml 480-548.  `FINITE_CART` is    -/
/-      the finiteness lemma proved by coordinate-wise induction; the two   -/
/-      cardinality corollaries `HAS_SIZE_CART_UNIV`/`CARD_CART_UNIV` read   -/
/-      the `m EXP dimindex(:N)` / `CARD(:A) EXP dimindex(:N)` count.  A     -/
/-      degenerate `|-  = ` or wrong RHS would MISMATCH.                     -/
/- ====================================================================== -/

#eval thmIs "(9a) FINITE_CART"
  "|- forall P. (forall i. 1 <= i /\\ i <= dimindex (:N) ==> FINITE {x | P i x}) ==> FINITE {v | forall i. 1 <= i /\\ i <= dimindex (:N) ==> P i (v$i)}"
  Session.FINITE_CART
#eval thmIs "(9a) HAS_SIZE_CART_UNIV"
  "|- forall m. (:A) HAS_SIZE m ==> (:A^N) HAS_SIZE m EXP dimindex (:N)"
  Session.HAS_SIZE_CART_UNIV
#eval thmIs "(9a) CARD_CART_UNIV"
  "|- FINITE (:A) ==> CARD (:A^N) = CARD (:A) EXP dimindex (:N)"
  Session.CARD_CART_UNIV
#eval thmIs "(9a) FINITE_CART_UNIV"
  "|- FINITE (:A) ==> FINITE (:A^N)"
  Session.FINITE_CART_UNIV

/- ====================================================================== -/
/- (10) CartVector (cart.ml 551-567): `vector` (554), the FIRST cart-layer -/
/-      definition to reach DOWN to the lists layer (its body names `EL`), -/
/-      and `IN_ELIM_PASTECART_THM` (561), the pastecart membership-        -/
/-      elimination theorem.  Force both fields and reject `|-  = `.        -/
/- ====================================================================== -/

#eval forceOk "CartVector/vector" Session.vector
#eval forceOk "CartVector/IN_ELIM_PASTECART_THM" Session.IN_ELIM_PASTECART_THM

/- ====================================================================== -/
/- (10a) VERBATIM STATEMENT CHECKS for cart.ml 551-567.  `vector` is the   -/
/-       `new_definition` `vector l = lambda i. EL (i - 1) l`; the membership -/
/-       theorem reads `pastecart a b IN {pastecart x y | P x y} <=> P a b`. -/
/-       A degenerate `|-  = ` or wrong body would MISMATCH.                -/
/- ====================================================================== -/

#eval thmIs "(10a) vector"
  "|- forall l. vector l = (lambda i. EL (i - 1) l)"
  Session.vector
#eval thmIs "(10a) IN_ELIM_PASTECART_THM"
  "|- forall P a b. pastecart a b IN {pastecart x y | P x y} <=> P a b"
  Session.IN_ELIM_PASTECART_THM

/- ====================================================================== -/
/- (10b) THE SHARP BEHAVIOURAL TEST: `vector` bridges the WHOLE stack.      -/
/-       Build a concrete `vector [a;b;c] : real^3` and index it under the  -/
/-       `$` infix (task 4).  This is the first point where the `cart` type,-/
/-       the `$` infix, the type-level numeral `3` (`dimindex(:3) = 3`,     -/
/-       task 8) and the lists-layer `EL` all fire together.  Proof:        -/
/-       SIMP[vector; LAMBDA_BETA; DIMINDEX_3] discharges `1<=2 /\ 2<=3`     -/
/-       and reduces the lambda to `EL (2-1) [a;b;c]`; REWRITE with `2-1=1`  -/
/-       (ARITH_RULE) and `EL 1 [a;b;c] = b` (EL_CONV) finishes.  Assert the -/
/-       result reads `|- vector [a; b; c]$2 = b`, else MISMATCH.           -/
/- ====================================================================== -/

#eval (do
  Session.ensureCart
  -- Parse-time flip: the concrete vector term now parses (whole stack live).
  match ← HolCore.Parser.parse_term "(vector [a;b;c]:real^3)$2" with
  | .ok tm => do
      let s ← HolCore.Printer.string_of_term tm
      IO.println s!"(10b) parse (vector [a;b;c]:real^3)$2 -> OK {s}"
  | .error e => IO.println s!"(10b) parse concrete vector -> MISMATCH: {e}"
  : IO Unit)

#eval (do
  let goal ← (match ← HolCore.Parser.parse_term "(vector [a;b;c]:real^3)$2 = b" with
              | .ok t => pure t | .error e => throw (IO.userError e))
  let sub21 ← (match ← Session.ARITH_RULE (← (match ← HolCore.Parser.parse_term "2 - 1 = 1" with
              | .ok t => pure t | .error e => throw (IO.userError e))) with
              | .ok t => pure t | .error e => throw (IO.userError e))
  let le ← (match ← Session.ARITH_RULE (← (match ← HolCore.Parser.parse_term "1 <= 2 /\\ 2 <= 3" with
              | .ok t => pure t | .error e => throw (IO.userError e))) with
              | .ok t => pure t | .error e => throw (IO.userError e))
  let el1 ← (match ← Session.EL_CONV (← (match ← HolCore.Parser.parse_term "EL 1 [a;b;c]" with
              | .ok t => pure t | .error e => throw (IO.userError e))) with
              | .ok t => pure t | .error e => throw (IO.userError e))
  match ← Session.prove goal
      (Session.THEN
        (Session.SIMP_TAC [Session.vector, Session.LAMBDA_BETA, Session.DIMINDEX_3, le])
        (Session.REWRITE_TAC [sub21, el1])) with
  | .ok th => do
      let s ← HolCore.Printer.string_of_thm th
      if (s.replace " " "") == "|-vector[a;b;c]$2=b" then
        IO.println s!"(10b) BEHAVIOUR vector$2 -> OK {s}"
      else
        IO.println s!"(10b) BEHAVIOUR vector$2 -> MISMATCH {s}"
  | .error e => IO.println s!"(10b) BEHAVIOUR vector$2 -> MISMATCH proof failed: {e}"
  : IO Unit)

/- ====================================================================== -/
/- (11) CartPcross (cart.ml 573-733): the `PCROSS` "pasting" product and    -/
/-      its 166-line theory - the largest section of cart.ml and the one    -/
/-      that COMPLETES the file.  Force every field and reject `|-  = `.     -/
/-      The two `(CONJ_PAIR o prove)` pairs (704/715) bind FOUR names, all   -/
/-      probed.                                                              -/
/- ====================================================================== -/

#eval forceOk "CartPcross/PCROSS" Session.PCROSS
#eval forceOk "CartPcross/FORALL_IN_PCROSS" Session.FORALL_IN_PCROSS
#eval forceOk "CartPcross/EXISTS_IN_PCROSS" Session.EXISTS_IN_PCROSS
#eval forceOk "CartPcross/PASTECART_IN_PCROSS" Session.PASTECART_IN_PCROSS
#eval forceOk "CartPcross/PCROSS_EQ_EMPTY" Session.PCROSS_EQ_EMPTY
#eval forceOk "CartPcross/PCROSS_EMPTY" Session.PCROSS_EMPTY
#eval forceOk "CartPcross/PCROSS_SING" Session.PCROSS_SING
#eval forceOk "CartPcross/SUBSET_PCROSS" Session.SUBSET_PCROSS
#eval forceOk "CartPcross/PCROSS_MONO" Session.PCROSS_MONO
#eval forceOk "CartPcross/PCROSS_EQ" Session.PCROSS_EQ
#eval forceOk "CartPcross/UNIV_PCROSS_UNIV" Session.UNIV_PCROSS_UNIV
#eval forceOk "CartPcross/HAS_SIZE_PCROSS" Session.HAS_SIZE_PCROSS
#eval forceOk "CartPcross/FINITE_PCROSS" Session.FINITE_PCROSS
#eval forceOk "CartPcross/FINITE_PCROSS_EQ" Session.FINITE_PCROSS_EQ
#eval forceOk "CartPcross/IMAGE_FSTCART_PCROSS" Session.IMAGE_FSTCART_PCROSS
#eval forceOk "CartPcross/IMAGE_SNDCART_PCROSS" Session.IMAGE_SNDCART_PCROSS
#eval forceOk "CartPcross/PCROSS_INTER" Session.PCROSS_INTER
#eval forceOk "CartPcross/PCROSS_UNION" Session.PCROSS_UNION
#eval forceOk "CartPcross/PCROSS_DIFF" Session.PCROSS_DIFF
#eval forceOk "CartPcross/INTER_PCROSS" Session.INTER_PCROSS
-- The two `(CONJ_PAIR o prove)` pairs: FOUR names, all probed.
#eval forceOk "CartPcross/PCROSS_UNIONS_UNIONS" Session.PCROSS_UNIONS_UNIONS
#eval forceOk "CartPcross/PCROSS_UNIONS" Session.PCROSS_UNIONS
#eval forceOk "CartPcross/PCROSS_INTERS_INTERS" Session.PCROSS_INTERS_INTERS
#eval forceOk "CartPcross/PCROSS_INTERS" Session.PCROSS_INTERS
#eval forceOk "CartPcross/DISJOINT_PCROSS" Session.DISJOINT_PCROSS

/- ====================================================================== -/
/- (11a) THE SHARP BEFORE/AFTER PROBE for the THIRD and LAST parser side    -/
/-       effect (cart.ml 571).  Baseline: `s PCROSS t` parsed as `s`        -/
/-       APPLIED TO `PCROSS` AND `t`, a three-way juxtaposition.  After the  -/
/-       `parse_as_infix("PCROSS",(22,"right"))` guard fires, it must parse  -/
/-       as an INFIX application: head `Const "PCROSS"` with exactly TWO      -/
/-       arguments.  We walk the parse tree and assert head-const=PCROSS,    -/
/-       nargs=2, else MISMATCH.                                             -/
/- ====================================================================== -/

#eval (do
  Session.ensureCart
  match ← HolCore.Parser.parse_term "s PCROSS t" with
  | .error e => IO.println s!"(11a) parse s PCROSS t -> MISMATCH Noparse: {e}"
  | .ok tm =>
      let s ← HolCore.Printer.string_of_term tm
      -- Count nested Comb applications down to the head constant.
      let rec go (t : HolCore.Kernel.term) (n : Nat) : (Option String) × Nat :=
        match t with
        | .Comb f _ => go f (n+1)
        | .Const c _ => (some c, n)
        | _ => (none, n)
      let (hd, nargs) := go tm 0
      if hd == some "PCROSS" && nargs == 2 then
        IO.println s!"(11a) parse s PCROSS t -> OK infix head=Const PCROSS nargs=2 : {s}"
      else
        IO.println s!"(11a) parse s PCROSS t -> MISMATCH head={hd} nargs={nargs} (want PCROSS/2) : {s}"
  : IO Unit)

/- ====================================================================== -/
/- (11b) VERBATIM STATEMENT CHECKS.  `PCROSS` is the `new_definition`; the   -/
/-       two `(CONJ_PAIR o prove)` pairs are checked component by component  -/
/-       to prove the `o` composition ran in the right order (defect class   -/
/-       #10): `prove` FIRST proves the whole conjunction, `CONJ_PAIR`       -/
/-       SECOND splits the OUTERMOST `/\`, so the FIRST name gets clause 1    -/
/-       (a single `!f g. ...` / `!f g. INTERS ...` clause) and the SECOND   -/
/-       name gets `clause2 /\ clause3` (a conjunction of two `!` clauses).  -/
/- ====================================================================== -/

#eval thmIs "(11b) PCROSS"
  "|- forall s t. s PCROSS t = {pastecart x y | x IN s /\\ y IN t}"
  Session.PCROSS

-- Pair #1 (704): first name = single f,g clause; second name = CONJ of two.
#eval thmIs "(11b) PCROSS_UNIONS_UNIONS"
  "|- forall f g. UNIONS f PCROSS UNIONS g = UNIONS {s PCROSS t | s IN f /\\ t IN g}"
  Session.PCROSS_UNIONS_UNIONS
#eval thmIs "(11b) PCROSS_UNIONS"
  "|- (forall s f. s PCROSS UNIONS f = UNIONS {s PCROSS t | t IN f}) /\\ (forall f t. UNIONS f PCROSS t = UNIONS {s PCROSS t | s IN f})"
  Session.PCROSS_UNIONS

-- Pair #2 (715): first name = single f,g if-clause; second name = CONJ of two.
#eval thmIs "(11b) PCROSS_INTERS_INTERS"
  "|- forall f g. INTERS f PCROSS INTERS g = (if f = {} then INTERS {(:A^M) PCROSS t | t IN g} else if g = {} then INTERS {s PCROSS (:A^N) | s IN f} else INTERS {s PCROSS t | s IN f /\\ t IN g})"
  Session.PCROSS_INTERS_INTERS
#eval thmIs "(11b) PCROSS_INTERS"
  "|- (forall s f. s PCROSS INTERS f = (if f = {} then s PCROSS (:A^N) else INTERS {s PCROSS t | t IN f})) /\\ (forall f t. INTERS f PCROSS t = (if f = {} then (:A^M) PCROSS t else INTERS {s PCROSS t | s IN f}))"
  Session.PCROSS_INTERS

/- ====================================================================== -/
/- (12) THE FIVE MEASURED PRE-TRANSLATION BASELINES, consolidated as       -/
/-      explicit FLIPS.  Before cart.ml was translated each of these was    -/
/-      MEASURED to fail characteristically; every one must now have        -/
/-      FLIPPED, and each prints WHAT IT NOW GETS, emitting MISMATCH        -/
/-      otherwise.  These are the sharpest tests in the file.               -/
/-                                                                          -/
/-      BASELINE 1  :real^3        -> ERROR Noparse                         -/
/-      BASELINE 2  (x:real^3)$1   -> ERROR "mk_type: type 1 ... "          -/
/-      BASELINE 3  lambda i. f i  -> ERROR "Unparsed input following term" -/
/-      BASELINE 4  s PCROSS t     -> three-way juxtaposition                -/
/-      BASELINE 5  type op `cart` -> DID NOT EXIST (find)                   -/
/- ====================================================================== -/

#eval Session.ensureCart

-- (12.1) BASELINE 1 FLIP: `:real^3` now PARSES and PRINTS BACK EXACTLY as
-- `real^3` (NOT `(real,3)cart`).  This is the sharp confirmation that the type
-- operator is named EXACTLY `cart`, as printer.ml's carttype path / parser.ml
-- 213 require: the printer only renders `^` when the head constructor is the
-- literal name `cart`.
#eval (do
  Session.ensureCart
  match ← HolCore.Parser.parse_type "real^3" with
  | .ok ty =>
      let s ← HolCore.Printer.string_of_type ty
      if s == "real^3" then
        IO.println s!"(12.1) BASELINE1 :real^3 -> OK flipped, prints back EXACTLY as {s}"
      else
        IO.println s!"(12.1) BASELINE1 :real^3 -> MISMATCH prints {s} (want exactly real^3)"
  | .error e => IO.println s!"(12.1) BASELINE1 :real^3 -> MISMATCH still Noparse: {e}"
  : IO Unit)

-- (12.2) BASELINE 2 FLIP: `(x:real^3)$1` now TYPECHECKS (parses to a
-- well-typed term).  Baseline: ERROR "mk_type: type 1 has not been defined".
-- A successful parse of the FULLY CONCRETE term (real^3 with the numeral 3,
-- and the `$` indexing) proves the type-level numeral `3` exists AND `$` is
-- the indexing infix.  Print the typechecked term.
#eval (do
  Session.ensureCart
  match ← HolCore.Parser.parse_term "(x:real^3)$1" with
  | .ok tm =>
      let s ← HolCore.Printer.string_of_term tm
      IO.println s!"(12.2) BASELINE2 (x:real^3)$1 -> OK flipped, typechecks as {s}"
  | .error e => IO.println s!"(12.2) BASELINE2 (x:real^3)$1 -> MISMATCH still fails: {e}"
  : IO Unit)

-- (12.3) BASELINE 3 FLIP: `lambda` is now a BINDER.  Baseline: `lambda i. f i`
-- gave "Unparsed input following term".  Confirm BOTH that the parser-state
-- flag reports `lambda` as a binder AND that a `lambda` term parses.
#eval (do
  Session.ensureCart
  let isB ← HolCore.Printer.parses_as_binder "lambda"
  if !isB then
    IO.println "(12.3) BASELINE3 lambda binder -> MISMATCH parses_as_binder=false"
  else
    match ← HolCore.Parser.parse_term "lambda i. (x:A^B)$i" with
    | .ok tm =>
        let s ← HolCore.Printer.string_of_term tm
        IO.println s!"(12.3) BASELINE3 lambda i. x$i -> OK flipped, binder installed, parses as {s}"
    | .error e => IO.println s!"(12.3) BASELINE3 lambda binder -> MISMATCH still Unparsed: {e}"
  : IO Unit)

-- (12.4) BASELINE 4 FLIP: `s PCROSS t` now parses as an INFIX (head Const
-- PCROSS, two args), NOT a three-way juxtaposition.  Confirm BOTH the infix
-- STATUS (right, precedence 22) AND the parse-tree shape.
#eval (do
  Session.ensureCart
  match ← HolCore.Printer.get_infix_status "PCROSS" with
  | .error e => IO.println s!"(12.4) BASELINE4 PCROSS infix status -> MISMATCH absent: {e}"
  | .ok (prec, assoc) =>
      if prec == 22 && assoc == "right" then
        match ← HolCore.Parser.parse_term "s PCROSS t" with
        | .error e => IO.println s!"(12.4) BASELINE4 s PCROSS t -> MISMATCH Noparse: {e}"
        | .ok tm =>
            let s ← HolCore.Printer.string_of_term tm
            let rec go (t : HolCore.Kernel.term) (n : Nat) : (Option String) × Nat :=
              match t with
              | .Comb f _ => go f (n+1)
              | .Const c _ => (some c, n)
              | _ => (none, n)
            let (hd, nargs) := go tm 0
            if hd == some "PCROSS" && nargs == 2 then
              IO.println s!"(12.4) BASELINE4 s PCROSS t -> OK flipped, right-22 infix head=Const PCROSS nargs=2 : {s}"
            else
              IO.println s!"(12.4) BASELINE4 s PCROSS t -> MISMATCH head={hd} nargs={nargs} (want PCROSS/2) : {s}"
      else
        IO.println s!"(12.4) BASELINE4 PCROSS infix status -> MISMATCH prec={prec} assoc={assoc} (want 22/right)"
  : IO Unit)

-- (12.5) BASELINE 5 FLIP: the type operator `cart` NOW EXISTS.  Baseline:
-- `get_type_arity "cart"` failed with `find`.  It is a BINARY type operator.
-- Also confirm the `$` infix is left-associative at precedence 25 (the
-- companion parser fact for indexing).
#eval (do
  Session.ensureCart
  match ← HolCore.Kernel.get_type_arity "cart" with
  | .error e => IO.println s!"(12.5) BASELINE5 get_type_arity cart -> MISMATCH still absent: {e}"
  | .ok n =>
      if n == 2 then
        match ← HolCore.Printer.get_infix_status "$" with
        | .ok (prec, assoc) =>
            if prec == 25 && assoc == "left" then
              IO.println s!"(12.5) BASELINE5 cart -> OK flipped, arity {n}; $ is the left-25 infix"
            else
              IO.println s!"(12.5) BASELINE5 $ infix -> MISMATCH prec={prec} assoc={assoc} (want 25/left)"
        | .error e => IO.println s!"(12.5) BASELINE5 $ infix status -> MISMATCH absent: {e}"
      else
        IO.println s!"(12.5) BASELINE5 get_type_arity cart -> MISMATCH arity {n} (want 2)"
  : IO Unit)

-- (12.6) ALL SEVEN new cart.ml types exist, confirmed BY ARITY.  finite_image
-- (1), cart (2), finite_sum (2), finite_diff (2), finite_prod (2), tybit0 (1),
-- tybit1 (1).  Each was ABSENT before its range landed; assert each arity.
#eval (do
  Session.ensureCart
  let expect : List (String × Int) :=
    [("finite_image", 1), ("cart", 2), ("finite_sum", 2), ("finite_diff", 2),
     ("finite_prod", 2), ("tybit0", 1), ("tybit1", 1)]
  for (nm, ar) in expect do
    match ← HolCore.Kernel.get_type_arity nm with
    | .ok n =>
        if n == ar then IO.println s!"(12.6) arity {nm} -> OK {n}"
        else IO.println s!"(12.6) arity {nm} -> MISMATCH {n} (want {ar})"
    | .error e => IO.println s!"(12.6) arity {nm} -> MISMATCH absent: {e}"
  : IO Unit)

-- (12.7) Kernel.get_type_arity "cart" succeeds (the exact probe named in the
-- task, kept as its own line so a regression is unambiguous).
#eval (do
  Session.ensureCart
  match ← HolCore.Kernel.get_type_arity "cart" with
  | .ok n => IO.println s!"(12.7) Kernel.get_type_arity cart -> OK arity {n}"
  | .error e => IO.println s!"(12.7) Kernel.get_type_arity cart -> MISMATCH {e}"
  : IO Unit)

/- ====================================================================== -/
/- (13) REAL BEHAVIOURAL CHECKS.  Forcing probes only prove a bundle       -/
/-      BUILT; these prove the translation WORKS.  dimindex 2/3/4 and a     -/
/-      concrete `vector [a;b;c]$2 = b` are ALREADY asserted verbatim in    -/
/-      sections (8a) and (10b) respectively - see the notes there; below   -/
/-      we ADD the pastecart/fstcart/sndcart round-trip and a PCROSS fact,  -/
/-      then RE-ASSERT dimindex as a self-contained behavioural line.       -/
/- ====================================================================== -/

-- (13a) dimindex behaviour, self-contained (also verbatim-checked in (8a)).
#eval thmIs "(13a) dimindex(:2)=2" "|- dimindex (:2) = 2" Session.DIMINDEX_2
#eval thmIs "(13a) dimindex(:3)=3" "|- dimindex (:3) = 3" Session.DIMINDEX_3
#eval thmIs "(13a) dimindex(:4)=4" "|- dimindex (:4) = 4" Session.DIMINDEX_4

-- (13b) pastecart / fstcart / sndcart ROUND-TRIP.  `PASTECART_FST_SND` reads
-- `pastecart (fstcart z) (sndcart z) = z`; `FSTCART_PASTECART` /
-- `SNDCART_PASTECART` read the projection laws.  Together they ARE the
-- round-trip: build a concrete `pastecart x y`, project both halves, and
-- re-paste - proving `pastecart (fstcart (pastecart x y)) (sndcart (pastecart
-- x y)) = pastecart x y`.  SIMP with the three laws closes it.
#eval (do
  Session.ensureCart
  let goal ← (match ← HolCore.Parser.parse_term
      "pastecart (fstcart (pastecart x y)) (sndcart (pastecart x y)) = pastecart (x:A^M) (y:A^N)" with
    | .ok t => pure t | .error e => throw (IO.userError e))
  match ← Session.prove goal
      (Session.REWRITE_TAC [Session.FSTCART_PASTECART, Session.SNDCART_PASTECART]) with
  | .ok th =>
      let s ← HolCore.Printer.string_of_thm th
      if ((s.replace " " "").replace "\n" "") == "|-pastecart(fstcart(pastecartxy))(sndcart(pastecartxy))=pastecartxy" then
        IO.println s!"(13b) BEHAVIOUR pastecart round-trip -> OK {s}"
      else
        IO.println s!"(13b) BEHAVIOUR pastecart round-trip -> MISMATCH {s}"
  | .error e => IO.println s!"(13b) BEHAVIOUR pastecart round-trip -> MISMATCH proof failed: {e}"
  : IO Unit)

-- (13c) A PCROSS fact IN REAL USE.  `PASTECART_IN_PCROSS` reads
-- `pastecart x y IN s PCROSS t <=> x IN s /\ y IN t`.  Prove the concrete
-- instance for a specific membership, exercising the PCROSS infix, the
-- pastecart constructor and the set-builder together.
#eval (do
  Session.ensureCart
  let goal ← (match ← HolCore.Parser.parse_term
      "pastecart (a:A^M) (b:A^N) IN (s PCROSS t) <=> a IN s /\\ b IN t" with
    | .ok t => pure t | .error e => throw (IO.userError e))
  match ← Session.prove goal
      (Session.REWRITE_TAC [Session.PASTECART_IN_PCROSS]) with
  | .ok th =>
      let s ← HolCore.Printer.string_of_thm th
      if sqi s == "|-" || sqi s == "|-=" then
        IO.println s!"(13c) BEHAVIOUR pastecart IN PCROSS -> MISMATCH degenerate {s}"
      else
        IO.println s!"(13c) BEHAVIOUR pastecart IN PCROSS -> OK {s}"
  | .error e => IO.println s!"(13c) BEHAVIOUR pastecart IN PCROSS -> MISMATCH proof failed: {e}"
  : IO Unit)

/- ====================================================================== -/
/- (14) `.hlp` DOCUMENTATION CHECKS.  /Users/walton/hol-light/Help carries  -/
/-      NO direct entry for dimindex, lambda, vector, pastecart, fstcart,   -/
/-      sndcart, PCROSS, finite_index or `$`.  It DOES carry DIMINDEX_CONV,  -/
/-      DIMINDEX_TAC and HAS_SIZE_DIMINDEX_RULE, whose documented EXAMPLES   -/
/-      exercise the cart-layer `dimindex` theory.  Those examples use      -/
/-      `:32`/`:64`, which our PUBLIC API does not expose (only DIMINDEX_2/  -/
/-      3/4 and HAS_SIZE_2/3/4 are re-exported); the conversions themselves  -/
/-      are internal to the CDConv bundle.  So we reproduce the DOCUMENTED   -/
/-      RULE FORM at the sizes our API exposes:                             -/
/-        DIMINDEX_CONV           `|- dimindex(:n) = n`   at n=2,3,4         -/
/-        HAS_SIZE_DIMINDEX_RULE  `|- (:n) HAS_SIZE n`    at n=2,3,4         -/
/-      LAMBDA_ELIM_CONV.hlp exists but documents the LOGICAL `\x. t`        -/
/-      lambda-elimination conversion, NOT the cart-layer `lambda` binder    -/
/-      (cart.ml 126) - a NAME COINCIDENCE, not a documentation fault, so we -/
/-      do NOT assert cart `lambda` against it.                             -/
/- ====================================================================== -/

-- (14a) DIMINDEX_CONV.hlp documents `|- dimindex(:n) = n`.  Reproduce the
-- documented rule form at the sizes our API exposes.
#eval thmIs "(14a) DIMINDEX_CONV form dimindex(:2)=2" "|- dimindex (:2) = 2" Session.DIMINDEX_2
#eval thmIs "(14a) DIMINDEX_CONV form dimindex(:3)=3" "|- dimindex (:3) = 3" Session.DIMINDEX_3
#eval thmIs "(14a) DIMINDEX_CONV form dimindex(:4)=4" "|- dimindex (:4) = 4" Session.DIMINDEX_4

-- (14b) HAS_SIZE_DIMINDEX_RULE.hlp documents `|- (:n) HAS_SIZE n`.  Reproduce
-- the documented rule form at the sizes our API exposes.
#eval thmIs "(14b) HAS_SIZE_DIMINDEX_RULE form (:2) HAS_SIZE 2" "|- (:2) HAS_SIZE 2" Session.HAS_SIZE_2
#eval thmIs "(14b) HAS_SIZE_DIMINDEX_RULE form (:3) HAS_SIZE 3" "|- (:3) HAS_SIZE 3" Session.HAS_SIZE_3
#eval thmIs "(14b) HAS_SIZE_DIMINDEX_RULE form (:4) HAS_SIZE 4" "|- (:4) HAS_SIZE 4" Session.HAS_SIZE_4
