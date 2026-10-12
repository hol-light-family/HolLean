/- File: HolTest/NormRealCheck.lean
Self-checking tests for normalizer.ml, calc_num.ml, real.ml, calc_rat.ml,
realarith.ml: theorem statements checked against the OCaml source, and
documented examples from hol-light/Help.
Lean4 translation by Chris Walton 2026 -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

namespace HolTest.NormRealCheck

/- ---------------------------------------------------------------------- -/
/- Local helpers (NOT in CommonTest): compare a conversion's RHS to an     -/
/- expected term up to alpha-conversion.  A conversion applied to `t`      -/
/- returns `|- t = t'`; `convRhsOK` checks the whole equation exactly the  -/
/- way `ruleOK` would, i.e. `t = expectedRhs` parsed and aconv-compared.   -/
/- We keep the printing-independent aconv check (never string compare).    -/
/- ---------------------------------------------------------------------- -/

/-- Apply `conv` to the term parsed from `input`, then require the resulting
    theorem to be hypothesis-free and alpha-equal to `input = expectedRhs`
    (or the boolean form when the printer uses `<=>`; we always build the
    equation as `(input) = (expectedRhs)` which `parse_term` reads as the
    appropriate equality for the operand type). -/
unsafe def convRhsOK (lbl input expectedRhs : String)
    (conv : term → IO (Except String thm)) : IO Unit := do
  match ← HolCore.Parser.parse_term input with
  | .error e => IO.println s!"{lbl} -> MISMATCH input parse ERR {e}"
  | .ok tm => ruleOK lbl (conv tm) s!"({input}) = ({expectedRhs})"

/-- Boolean-valued conversion: build the expected as `(input) <=> (expectedRhs)`. -/
unsafe def convIffOK (lbl input expectedRhs : String)
    (conv : term → IO (Except String thm)) : IO Unit := do
  match ← HolCore.Parser.parse_term input with
  | .error e => IO.println s!"{lbl} -> MISMATCH input parse ERR {e}"
  | .ok tm => ruleOK lbl (conv tm) s!"({input}) <=> ({expectedRhs})"

/-- Force the natural-number arithmetic layer (so `+`,`*`,`<`,`EXP`,`MOD`
    parse as constants, not free variables). -/
unsafe def forceNum : IO Unit := do
  let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))

/-- Force the real layer. -/
unsafe def forceReal : IO Unit := do
  let _ ← (IO.mkRef (concl Session.REAL_ADD_SYM) : IO (IO.Ref term))

/- ====================================================================== -/
/- 1. calc_num.ml : num_CONV / NUM_REDUCE_CONV / EXPAND_CASES_CONV.        -/
/- ====================================================================== -/

/- num_CONV.hlp: `num_CONV `3`` = `|- 3 = SUC 2`. -/
#eval (do
  forceNum
  convRhsOK "num_CONV.hlp 3=SUC 2" "3" "SUC 2" Session.num_CONV)

/- num_CONV.hlp FAILURE: fails on `0` and on a non-numeral. -/
#eval (do
  forceNum
  match ← HolCore.Parser.parse_term "0" with
  | .error e => IO.println s!"num_CONV rej 0 -> MISMATCH parse ERR {e}"
  | .ok tm => failsOK "num_CONV.hlp reject 0" (Session.num_CONV tm))

#eval (do
  forceNum
  match ← HolCore.Parser.parse_term "x:num" with
  | .error e => IO.println s!"num_CONV rej var -> MISMATCH parse ERR {e}"
  | .ok tm => failsOK "num_CONV.hlp reject non-numeral" (Session.num_CONV tm))

/- NUM_REDUCE_CONV: plain numeral reductions (DEPTH_CONV NUM_RED_CONV). -/
#eval (do
  forceNum
  convRhsOK "NUM_REDUCE 2+3" "2 + 3" "5" Session.NUM_REDUCE_CONV)
#eval (do
  forceNum
  convRhsOK "NUM_REDUCE 12*12" "12 * 12" "144" Session.NUM_REDUCE_CONV)
#eval (do
  forceNum
  convRhsOK "NUM_REDUCE 2 EXP 10" "2 EXP 10" "1024" Session.NUM_REDUCE_CONV)
#eval (do
  forceNum
  convRhsOK "NUM_REDUCE 100 DIV 7" "100 DIV 7" "14" Session.NUM_REDUCE_CONV)
#eval (do
  forceNum
  convRhsOK "NUM_REDUCE 100 MOD 7" "100 MOD 7" "2" Session.NUM_REDUCE_CONV)
#eval (do
  forceNum
  convRhsOK "NUM_REDUCE FACT 6" "FACT 6" "720" Session.NUM_REDUCE_CONV)
/- A larger factorial to exercise the multiplication recursion / Toom-3. -/
#eval (do
  forceNum
  convRhsOK "NUM_REDUCE FACT 25"
    "FACT 25" "15511210043330985984000000" Session.NUM_REDUCE_CONV)
/- Relational reductions collapse to T / F (verbose printer: use <=>). -/
#eval (do
  forceNum
  convIffOK "NUM_REDUCE 3 < 5" "3 < 5" "T" Session.NUM_REDUCE_CONV)
#eval (do
  forceNum
  convIffOK "NUM_REDUCE 5 <= 4" "5 <= 4" "F" Session.NUM_REDUCE_CONV)
#eval (do
  forceNum
  convIffOK "NUM_REDUCE 7 = 7" "7 = 7" "T" Session.NUM_REDUCE_CONV)

/- NUM_SUB_CONV: cutoff subtraction of numerals. -/
#eval (do
  forceNum
  convRhsOK "NUM_SUB 10-3" "10 - 3" "7" Session.NUM_SUB_CONV)
#eval (do
  forceNum
  convRhsOK "NUM_SUB 3-10 (cutoff)" "3 - 10" "0" Session.NUM_SUB_CONV)

/- num_CONV boundary examples (documented shape `n = SUC (n-1)`). -/
#eval (do
  forceNum
  convRhsOK "num_CONV 1=SUC 0" "1" "SUC 0" Session.num_CONV)
#eval (do
  forceNum
  convRhsOK "num_CONV 100=SUC 99" "100" "SUC 99" Session.num_CONV)

/- EXPAND_CASES_CONV.hlp VERBATIM example (implication body). -/
#eval (do
  forceNum
  convIffOK "EXPAND_CASES_CONV.hlp"
    "!n. n < 5 ==> ~(n = 0) ==> 12 MOD n = 0"
    ("(~(1 = 0) ==> 12 MOD 1 = 0) /\\ (~(2 = 0) ==> 12 MOD 2 = 0) /\\ " ++
     "(~(3 = 0) ==> 12 MOD 3 = 0) /\\ (~(4 = 0) ==> 12 MOD 4 = 0)")
    Session.EXPAND_CASES_CONV)

/- EXPAND_CASES_CONV.hlp second example: composition with NUM_REDUCE_CONV
   reduces the whole thing to T.  Run EXPAND_CASES_CONV then NUM_REDUCE_CONV
   on the RHS and check that RHS is T. -/
#eval (do
  forceNum
  match ← HolCore.Parser.parse_term "!n. n < 5 ==> ~(n = 0) ==> 12 MOD n = 0" with
  | .error e => IO.println s!"EXPAND;REDUCE -> MISMATCH parse ERR {e}"
  | .ok tm =>
    match ← Session.EXPAND_CASES_CONV tm with
    | .error e => IO.println s!"EXPAND;REDUCE -> MISMATCH expand ERR {e}"
    | .ok th1 =>
      match HolCore.Equal.rhs (concl th1) with
      | .error e => IO.println s!"EXPAND;REDUCE -> MISMATCH rhs ERR {e}"
      | .ok r1 => do
          let r1s ← HolCore.Printer.string_of_term r1
          convIffOK "EXPAND_CASES;NUM_REDUCE.hlp" r1s "T" Session.NUM_REDUCE_CONV)

/- ====================================================================== -/
/- 2. normalizer.ml : NUM_NORMALIZE_CONV and the POLYNOMIAL_* pieces.      -/
/- ====================================================================== -/

/- NUM_NORMALIZE_CONV.hlp VERBATIM example. -/
#eval (do
  forceNum
  convRhsOK "NUM_NORMALIZE_CONV.hlp"
    "1 + (1 + x + x EXP 2) * (x + (x * x) EXP 2)"
    "x EXP 6 + x EXP 5 + x EXP 4 + x EXP 3 + x EXP 2 + x + 1"
    Session.NUM_NORMALIZE_CONV)

/- NUM_NORMALIZE_CONV .hlp FAILURE clause: "should never fail"; on an atom it
   returns a reflexive theorem |- x = x. -/
#eval (do
  forceNum
  convRhsOK "NUM_NORMALIZE refl var" "x" "x" Session.NUM_NORMALIZE_CONV)
#eval (do
  forceNum
  convRhsOK "NUM_NORMALIZE refl numeral" "7" "7" Session.NUM_NORMALIZE_CONV)

/- NUM_NORMALIZE ordering: variables reorder into canonical order. -/
#eval (do
  forceNum
  convRhsOK "NUM_NORMALIZE y+x" "y + x" "x + y" Session.NUM_NORMALIZE_CONV)
#eval (do
  forceNum
  convRhsOK "NUM_NORMALIZE (x+1)*(x+1)"
    "(x + 1) * (x + 1)" "x EXP 2 + 2 * x + 1" Session.NUM_NORMALIZE_CONV)

/- Individual POLYNOMIAL_* conversions (exposed as NORM_POLYNOMIAL_*_CONV).
   These require already-canonical polynomial inputs. -/
#eval (do
  forceNum
  convRhsOK "NORM_POLYNOMIAL_ADD_CONV 2*x+3*x"
    "2 * x + 3 * x" "5 * x" Session.NORM_POLYNOMIAL_ADD_CONV)
#eval (do
  forceNum
  convRhsOK "NORM_POLYNOMIAL_MUL_CONV (x+1)*(x+1)"
    "(x + 1) * (x + 1)" "x EXP 2 + 2 * x + 1" Session.NORM_POLYNOMIAL_MUL_CONV)
#eval (do
  forceNum
  convRhsOK "NORM_POLYNOMIAL_POW_CONV (x*y) EXP 2"
    "(x * y) EXP 2" "x EXP 2 * y EXP 2" Session.NORM_POLYNOMIAL_POW_CONV)

/- POLYNOMIAL_NEG_CONV / POLYNOMIAL_SUB_CONV are DEAD in the naturals
   instance (neg_tm/sub_tm are dummies); a real negation/subtraction must
   be rejected rather than mangled. -/
#eval (do
  forceNum
  match ← HolCore.Parser.parse_term "x - y" with
  | .error e => IO.println s!"NORM_POLY_SUB reject -> MISMATCH parse ERR {e}"
  | .ok tm => (failsOK "NORM_POLYNOMIAL_SUB_CONV rejects num subtraction" (Session.NORM_POLYNOMIAL_SUB_CONV tm)))

/- ====================================================================== -/
/- 3. real.ml : theorem statements (early, middle, late) via stmtOK.       -/
/- ====================================================================== -/

/- Early (real.ml 17-56): number-embedding clauses. -/
#eval (do let th := Session.REAL_OF_NUM_GE
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          forceNum
          stmtOK "REAL_OF_NUM_GE (real.ml 21)" th "!m n. &m >= &n <=> m >= n")
#eval (do let th := Session.REAL_OF_NUM_MAX
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          forceNum
          stmtOK "REAL_OF_NUM_MAX (real.ml 29)" th "!m n. max (&m) (&n) = &(MAX m n)")
#eval (do let th := Session.REAL_OF_NUM_SUC
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          forceNum
          stmtOK "REAL_OF_NUM_SUC (real.ml 37)" th "!n. &n + &1 = &(SUC n)")
#eval (do let th := Session.REAL_OF_NUM_SUB
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          forceNum
          stmtOK "REAL_OF_NUM_SUB (real.ml 41)" th "!m n. m <= n ==> (&n - &m = &(n - m))")
#eval (do let th := Session.REAL_OF_NUM_SUB_CASES
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          forceNum
          stmtOK "REAL_OF_NUM_SUB_CASES (real.ml 50)" th
            "!m n. &m - &n = if n <= m then &(m - n) else -- &(n - m)")

/- Middle (real.ml 76-95): AC/distrib and a THENL-heavy linear lemma. -/
#eval (do let th := Session.REAL_MUL_AC
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "REAL_MUL_AC (real.ml 76)" th
            "(m * n = n * m) /\\ ((m * n) * p = m * (n * p)) /\\ (m * (n * p) = n * (m * p))")
#eval (do let th := Session.REAL_ADD_RDISTRIB
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "REAL_ADD_RDISTRIB (real.ml 83)" th "!x y z. (x + y) * z = x * z + y * z")
#eval (do let th := Session.REAL_LT_LADD_IMP
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "REAL_LT_LADD_IMP (real.ml 87)" th "!x y z. y < z ==> x + y < x + z")
#eval (do let th := Session.REAL_LT_MUL
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "REAL_LT_MUL (real.ml 95)" th "!x y. &0 < x /\\ &0 < y ==> &0 < x * y")

/- Middle-late (real.ml 610-795): abs / power / inverse, THENL-heavy proofs. -/
#eval (do let th := Session.REAL_ABS_MUL
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "REAL_ABS_MUL (real.ml 610)" th "!x y. abs(x * y) = abs(x) * abs(y)")
#eval (do let th := Session.REAL_POW_LE
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          forceNum
          stmtOK "REAL_POW_LE (real.ml 627)" th "!x n. &0 <= x ==> &0 <= x pow n")
#eval (do let th := Session.REAL_ABS_POW
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          forceNum
          stmtOK "REAL_ABS_POW (real.ml 639)" th "!x n. abs(x pow n) = abs(x) pow n")
#eval (do let th := Session.REAL_INV_INV
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "REAL_INV_INV (real.ml 688)" th "!x. inv(inv x) = x")
#eval (do let th := Session.REAL_LT_INV
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "REAL_LT_INV (real.ml 705)" th "!x. &0 < x ==> &0 < inv(x)")
#eval (do let th := Session.REAL_MUL_RINV
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "REAL_MUL_RINV (real.ml 742)" th "!x. ~(x = &0) ==> (x * inv(x) = &1)")
#eval (do let th := Session.REAL_INV_1
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "REAL_INV_1 (real.ml 747)" th "inv(&1) = &1")
#eval (do let th := Session.REAL_INV_MUL
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "REAL_INV_MUL (real.ml 795)" th "!x y. inv(x * y) = inv(x) * inv(y)")

/- Late (real.ml 1677-1685): sqrt definitional theorems. -/
#eval (do let th := Session.POW_2_SQRT
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          forceNum
          stmtOK "POW_2_SQRT (real.ml 1677)" th "!x. &0 <= x ==> sqrt(x pow 2) = x")
#eval (do let th := Session.SQRT_0
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "SQRT_0 (real.ml 1681)" th "sqrt(&0) = &0")
#eval (do let th := Session.SQRT_1
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "SQRT_1 (real.ml 1685)" th "sqrt(&1) = &1")

/- ====================================================================== -/
/- 4. realarith.ml : driving lemmas (stmtOK) + REAL_ARITH decision proc.   -/
/- ====================================================================== -/

#eval (do let th := Session.REAL_LTE_TOTAL
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "REAL_LTE_TOTAL (realarith.ml 14)" th "!x y. x < y \\/ y <= x")
#eval (do let th := Session.REAL_LT_IMP_LE
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "REAL_LT_IMP_LE (realarith.ml 24)" th "!x y. x < y ==> x <= y")
#eval (do let th := Session.REAL_LE_ADD
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "REAL_LE_ADD (realarith.ml 40)" th "!x y. &0 <= x /\\ &0 <= y ==> &0 <= x + y")
#eval (do let th := Session.REAL_LE_SQUARE
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "REAL_LE_SQUARE (realarith.ml)" th "!x. &0 <= x * x")
#eval (do let th := Session.REAL_SUB_0
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "REAL_SUB_0 (realarith.ml)" th "!x y. (x - y = &0) <=> (x = y)")

/- REAL_ARITH (the final REAL_ARITH3) proves valid linear/algebraic goals. -/
#eval (do
  forceReal
  match ← HolCore.Parser.parse_term "!x y:real. x + y = y + x" with
  | .error e => IO.println s!"REAL_ARITH add-comm -> MISMATCH parse ERR {e}"
  | .ok tm => (ruleOK "REAL_ARITH add-comm" (Session.REAL_ARITH3 tm) "!x y:real. x + y = y + x"))

#eval (do
  forceReal
  match ← HolCore.Parser.parse_term
    "!x y:real. x <= y /\\ y <= x ==> x = y" with
  | .error e => IO.println s!"REAL_ARITH antisym -> MISMATCH parse ERR {e}"
  | .ok tm => (ruleOK "REAL_ARITH le-antisym" (Session.REAL_ARITH3 tm) "!x y:real. x <= y /\\ y <= x ==> x = y"))

#eval (do
  forceReal
  match ← HolCore.Parser.parse_term
    "!x:real. abs(x) >= &0" with
  | .error e => IO.println s!"REAL_ARITH abs>=0 -> MISMATCH parse ERR {e}"
  | .ok tm => (ruleOK "REAL_ARITH abs>=0" (Session.REAL_ARITH3 tm) "!x:real. abs(x) >= &0"))

#eval (do
  forceReal
  match ← HolCore.Parser.parse_term
    "!x y z:real. x <= y /\\ y <= z ==> x <= z" with
  | .error e => IO.println s!"REAL_ARITH le-trans -> MISMATCH parse ERR {e}"
  | .ok tm => (ruleOK "REAL_ARITH le-trans" (Session.REAL_ARITH3 tm) "!x y z:real. x <= y /\\ y <= z ==> x <= z"))

/- REAL_ARITH FAILURE: an invalid goal must fail. -/
#eval (do
  forceReal
  match ← HolCore.Parser.parse_term "!x y:real. x < y" with
  | .error e => IO.println s!"REAL_ARITH bogus -> MISMATCH parse ERR {e}"
  | .ok tm => failsOK "REAL_ARITH rejects false goal (x<y)" (Session.REAL_ARITH3 tm))

#eval (do
  forceReal
  match ← HolCore.Parser.parse_term "!x:real. x < x" with
  | .error e => IO.println s!"REAL_ARITH x<x -> MISMATCH parse ERR {e}"
  | .ok tm => failsOK "REAL_ARITH rejects x<x" (Session.REAL_ARITH3 tm))

/- ====================================================================== -/
/- 5. calc_rat.ml : REAL_RAT_* conversions, REAL_POLY_CONV, REAL_RING,     -/
/-    REAL_FIELD, real_ideal_cofactors, ASM_REAL_ARITH_TAC.                -/
/- ====================================================================== -/

/- DECIMAL definition statement (calc_rat.ml). -/
#eval (do let th := Session.DECIMAL
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "DECIMAL (calc_rat.ml 16)" th "!x y. DECIMAL x y = &x / &y")

/- REAL_RAT_* conversions (worked examples). -/
#eval (do
  forceReal
  convIffOK "REAL_RAT_LE_CONV &22 / &7 <= &314 / &100 (false)"
    "&22 / &7 <= &314 / &100" "F" Session.REAL_RAT_LE_CONV)
#eval (do
  forceReal
  convIffOK "REAL_RAT_EQ_CONV &2 / &4 = &1 / &2"
    "&2 / &4 = &1 / &2" "T" Session.REAL_RAT_EQ_CONV)
#eval (do
  forceReal
  convRhsOK "REAL_RAT_ADD_CONV &1/&2 + &1/&3"
    "&1 / &2 + &1 / &3" "&5 / &6" Session.REAL_RAT_ADD_CONV)
#eval (do
  forceReal
  convRhsOK "REAL_RAT_MUL_CONV &2/&3 * &3/&4"
    "&2 / &3 * &3 / &4" "&1 / &2" Session.REAL_RAT_MUL_CONV)
#eval (do
  forceReal
  convRhsOK "REAL_RAT_NEG_CONV.hlp -- (-- &3 / &2)"
    "-- (-- &3 / &2)" "&3 / &2" Session.REAL_RAT_NEG_CONV)

/- REAL_POLY_CONV.hlp example 1: multiplying out. -/
#eval (do
  forceReal
  convRhsOK "REAL_POLY_CONV.hlp multiply-out"
    "(x + &1) * (x pow 2 + &1) * (x pow 4 + &1)"
    "x pow 7 + x pow 6 + x pow 5 + x pow 4 + x pow 3 + x pow 2 + x + &1"
    Session.REAL_POLY_CONV)

/- REAL_POLY_CONV.hlp example 2: Liouville identity collapses to &0. -/
#eval (do
  forceReal
  convRhsOK "REAL_POLY_CONV.hlp Liouville -> &0"
    ("((x1 + x2) pow 4 + (x1 + x3) pow 4 + (x1 + x4) pow 4 + " ++
     "(x2 + x3) pow 4 + (x2 + x4) pow 4 + (x3 + x4) pow 4) / &6 + " ++
     "((x1 - x2) pow 4 + (x1 - x3) pow 4 + (x1 - x4) pow 4 + " ++
     "(x2 - x3) pow 4 + (x2 - x4) pow 4 + (x3 - x4) pow 4) / &6 - " ++
     "(x1 pow 2 + x2 pow 2 + x3 pow 2 + x4 pow 2) pow 2")
    "&0"
    Session.REAL_POLY_CONV)

/- REAL_RING.hlp example: homographic inversion. -/
#eval (do
  forceReal
  match ← HolCore.Parser.parse_term
    "y * (c * x + d) = a * x + b ==> x * (c * y - a) = b - d * y" with
  | .error e => IO.println s!"REAL_RING.hlp -> MISMATCH parse ERR {e}"
  | .ok tm => (ruleOK "REAL_RING.hlp homographic" (Session.REAL_RING tm) "y * (c * x + d) = a * x + b ==> x * (c * y - a) = b - d * y"))

/- REAL_RING.hlp negative: the real-specific fact is NOT a ring identity. -/
#eval (do
  forceReal
  match ← HolCore.Parser.parse_term "x pow 4 + &1 = &0 ==> F" with
  | .error e => IO.println s!"REAL_RING.hlp neg -> MISMATCH parse ERR {e}"
  | .ok tm => failsOK "REAL_RING.hlp rejects x^4+1=0==>F" (Session.REAL_RING tm))

/- REAL_FIELD.hlp example: algebraic simplification with a nonzero side condition. -/
#eval (do
  forceReal
  match ← HolCore.Parser.parse_term
    "!x. &0 < x ==> &1 / x - &1 / (x + &1) = &1 / (x * (x + &1))" with
  | .error e => IO.println s!"REAL_FIELD.hlp -> MISMATCH parse ERR {e}"
  | .ok tm => (ruleOK "REAL_FIELD.hlp" (Session.REAL_FIELD tm) "!x. &0 < x ==> &1 / x - &1 / (x + &1) = &1 / (x * (x + &1))"))

/- real_ideal_cofactors.hlp VERBATIM example: assert the cofactor list, then
   confirm the reconstructed identity via REAL_RING. -/
#eval (do
  forceReal
  match ← HolCore.Parser.parse_term "y1 * y3 + x1 * x3" with
  | .error e => IO.println s!"cofactors gen1 parse ERR {e}"
  | .ok g1 =>
    match ← HolCore.Parser.parse_term "y3 * (y2 - y3) + (x2 - x3) * x3" with
    | .error e => IO.println s!"cofactors gen2 parse ERR {e}"
    | .ok g2 =>
      match ← HolCore.Parser.parse_term
        "x3 * y3 * (y1 * (x2 - x3) - x1 * (y2 - y3))" with
      | .error e => IO.println s!"cofactors target parse ERR {e}"
      | .ok tgt =>
        match ← Session.real_ideal_cofactors [g1, g2] tgt with
        | .error e => IO.println s!"real_ideal_cofactors.hlp -> MISMATCH failed: {e}"
        | .ok cfs =>
          match ← HolCore.Parser.parse_term "&1 * y3 pow 2 + -- &1 * y2 * y3" with
          | .error e => IO.println s!"cofactors want1 parse ERR {e}"
          | .ok w1 =>
            match ← HolCore.Parser.parse_term "&1 * y1 * y3" with
            | .error e => IO.println s!"cofactors want2 parse ERR {e}"
            | .ok w2 =>
              match cfs with
              | [c1, c2] =>
                if aconv c1 w1 && aconv c2 w2 then
                  IO.println "real_ideal_cofactors.hlp -> OK"
                else
                  IO.println s!"real_ideal_cofactors.hlp -> MISMATCH got {← cfs.mapM HolCore.Printer.string_of_term}"
              | _ => IO.println s!"real_ideal_cofactors.hlp -> MISMATCH wrong count {cfs.length}")

/- REAL_IDEAL_CONV.hlp VERBATIM singleton example: polynomial division. -/
#eval (do
  forceReal
  match ← HolCore.Parser.parse_term "x - &1" with
  | .error e => IO.println s!"REAL_IDEAL_CONV gen parse ERR {e}"
  | .ok g1 =>
    match ← HolCore.Parser.parse_term "x pow 4 - &1" with
    | .error e => IO.println s!"REAL_IDEAL_CONV target parse ERR {e}"
    | .ok tgt =>
      ruleOK "REAL_IDEAL_CONV.hlp x^4-1 by x-1"
        (Session.REAL_IDEAL_CONV [g1] tgt)
        "x pow 4 - &1 = (&1 * x pow 3 + &1 * x pow 2 + &1 * x + &1) * (x - &1)")

/- ASM_REAL_ARITH_TAC.hlp example: with `abs x <= y` in the assumptions, the
   goal `abs (x - z) <= abs (y + abs z)` closes.  Build a goal with that
   assumption (ASSUME) and run TAC_PROOF; the result carries exactly that one
   hypothesis, so we check the conclusion + the single hypothesis explicitly. -/
#eval (do
  forceReal
  match ← HolCore.Parser.parse_term "abs x <= y" with
  | .error e => IO.println s!"ASM_REAL_ARITH asm parse ERR {e}"
  | .ok asmTm =>
    match ← HolCore.Parser.parse_term "abs (x - z) <= abs (y + abs z)" with
    | .error e => IO.println s!"ASM_REAL_ARITH goal parse ERR {e}"
    | .ok goalTm =>
      match ASSUME asmTm with
      | .error e => IO.println s!"ASM_REAL_ARITH ASSUME ERR {e}"
      | .ok asmTh =>
        let g : HolCore.Tactics.goal := ([("", asmTh)], goalTm)
        match ← Session.TAC_PROOF g Session.ASM_REAL_ARITH_TAC with
        | .error e => IO.println s!"ASM_REAL_ARITH_TAC.hlp -> MISMATCH failed: {e}"
        | .ok th =>
          let concOk := aconv (concl th) goalTm
          let hypOk := (hyp th).any (fun h => aconv h asmTm)
          if concOk && hypOk then IO.println "ASM_REAL_ARITH_TAC.hlp -> OK"
          else IO.println s!"ASM_REAL_ARITH_TAC.hlp -> MISMATCH {← HolCore.Printer.string_of_thm th}")

/- ASM_REAL_ARITH_TAC.hlp companion: plain REAL_ARITH_TAC CANNOT close the same
   goal (no access to the assumption).  Prove-by-tactic on the bare goal fails. -/
#eval (do
  forceReal
  match ← HolCore.Parser.parse_term "abs (x - z) <= abs (y + abs z)" with
  | .error e => IO.println s!"REAL_ARITH_TAC noasm parse ERR {e}"
  | .ok goalTm =>
    let g : HolCore.Tactics.goal := ([], goalTm)
    failsOK "REAL_ARITH_TAC cannot close ASM goal (no asm)"
      (Session.TAC_PROOF g Session.REAL_ARITH_TAC))

end HolTest.NormRealCheck
