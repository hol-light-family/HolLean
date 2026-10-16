/- ========================================================================= -/
/- Properties of real polynomials (not canonically represented).             -/
/- ========================================================================= -/
/- File: HolLibrary/Poly.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/poly.ml`, by hand, in file order, in
  the style of HolLibrary/Analysis.lean and HolLibrary/Transc.lean (see there
  and HolMath/Base.lean for the conventions).  poly.ml begins with
  `needs "Library/analysis.ml"`; analysis.ml's theorems it uses are supplied
  via the CoreThms structures (SessionLibrary.Poly fills them from
  SessionLibrary.Analysis).  Each section is a bundle (a `structure`) built by
  a `setup` function; SessionLibrary/Poly.lean builds the bundles in order and
  exports every name under its HOL Light name.

  poly.ml's conversions on polynomials with rational coefficients
  (POLY_DIFF_CONV, POLY_CMUL_CONV, POLY_ADD_CONV, POLY_MUL_CONV,
  POLY_NORMALIZE_CONV) are bundle fields; their recursive workers (OCaml's
  local `let rec`s) are top-level `partial def`s taking the theorems and
  sub-conversions they use, with the rewrite nets built once, as in OCaml.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, REAL_ARITH, TAUT) they are bound first, in
  OCaml's order.
-/

import HolLibrary.Analysis

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolLibrary.Analysis (undischCheck)
open HolLibrary.Analysis (undischCheck SELECT_CONV)

set_option maxRecDepth 8000

namespace HolLibrary.Poly

-- @@COREFILL BEGIN
/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD1 ADD_CLAUSES ALL ARITH COND_CLAUSES CONS_11 CONS_HD_TL DE_MORGAN_THM
   DIFF_ADD DIFF_CMUL DIFF_CONST DIFF_CONT DIFF_POW DIFF_UNIQ EL EQ_REFL
   EQ_TRANS EXTENSION FINITE_RULES FINITE_SUBSET FUN_EQ_THM HD IN_ELIM_THM
   IN_INSERT ITERATE_CLAUSES_NUMSEG IVT LE LEFT_AND_FORALL_THM
   LEFT_IMP_EXISTS_THM LENGTH LENGTH_EQ_NIL LE_0 LE_EXISTS LE_REFL LE_SUC_LT
   LT LT_ADD_LCANCEL LT_CASES LT_SUC_LE MAP MONOIDAL_REAL_ADD MVT
   NOT_CONS_NIL NOT_EXISTS_THM NOT_FORALL_THM NOT_IN_EMPTY NOT_LE NOT_SUC
   NSUM_LMUL POW_1 PRE REAL_ABS_0 REAL_ABS_MUL REAL_ABS_POS REAL_ABS_TRIANGLE
   REAL_ADD_AC REAL_ADD_ASSOC REAL_ADD_LDISTRIB REAL_ADD_LID
   REAL_ADD_RDISTRIB REAL_ADD_RID REAL_ADD_SYM REAL_ENTIRE
   REAL_EQ_ADD_LCANCEL REAL_EQ_MUL_LCANCEL REAL_LDISTRIB REAL_LE_LADD
   REAL_LE_MUL2 REAL_LE_REFL REAL_LE_TRANS : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (REAL_LT_ADDR REAL_LT_IMP_LE REAL_LT_LE REAL_LT_NEGTOTAL REAL_LT_REFL
   REAL_MUL_AC REAL_MUL_ASSOC REAL_MUL_LID REAL_MUL_LNEG REAL_MUL_LZERO
   REAL_MUL_RID REAL_MUL_RINV REAL_MUL_RNEG REAL_MUL_RZERO REAL_MUL_SYM
   REAL_NEG_NEG REAL_OF_NUM_ADD REAL_OF_NUM_EQ REAL_OF_NUM_SUC REAL_SUB_REFL
   RIGHT_FORALL_IMP_THM RIGHT_IMP_EXISTS_THM SELECT_UNIQUE SUBSET SUC_INJ
   SUC_SUB1 SUM_COMBINE_R SUM_LMUL SUM_OFFSET_0 SUM_SING TL differentiable
   list_RECURSION monoidal neutral num_RECURSION pow real_gt real_pow
   real_sub : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms3 where
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms4 where
  deriving Inhabited

-- @@COREFILL END

/-- What poly.ml uses from Session besides theorems. -/
structure PolyDeps where
  -- definitions and parser state
  new_definition : String → ExceptT String IO thm
  -- new_recursive_definition (see HolLibrary/RSTC.lean) for list_RECURSION/num_RECURSION
  new_recursive_definition : thm → String → ExceptT String IO thm
  prioritize_real : IO Unit
  -- parser-state functions (see HolLibrary/Analysis.lean)
  parse_as_infix : String × (Int × String) → IO Unit
  overload_interface : String → term → ExceptT String IO Unit
  override_interface : String → term → ExceptT String IO Unit
  -- conversions (see HolLibrary/Analysis.lean, HolLibrary/BitMatch.lean)
  num_CONV : ioconv
  ETA_CONV : ioconv
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  REAL_ARITH : term → ExceptT String IO thm
  REAL_ARITH_TAC : tactic
  INDUCT_TAC : tactic
  LIST_INDUCT_TAC : tactic
  -- conversions
  prove_recursive_functions_exist : thm → term → ExceptT String IO thm  -- recursion.ml; via Analysis Session
  -- calc_rat.ml's REAL_RAT_* conversions (via SessionLibrary.Analysis / CalcRat)
  REAL_RAT_MUL_CONV : ioconv
  REAL_RAT_ADD_CONV : ioconv
  REAL_RAT_EQ_CONV : ioconv
  -- calc_num.ml's NUM_SUC_CONV (successor conversion)
  NUM_SUC_CONV : ioconv
  -- calc_num.ml's num_CONV: `|- NUMERAL n = SUC (NUMERAL (n-1))`
  SIMP_RULE : List thm → thm → ExceptT String IO thm      -- simp.ml SIMP_RULE
  SELECT_ELIM_TAC : tactic                                 -- Session SELECT_ELIM_TAC
  NUMSEG_CONV : ioconv                                     -- iterate.ml NUMSEG_CONV
  reduce_interface : String → term → ExceptT String IO Unit  -- preterm.ml reduce_interface
  unparse_as_infix : String → IO Unit                      -- printer.ml unparse_as_infix
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3
  core4 : CoreThms4

/- ------------------------------------------------------------------------- -/
/- Header, definitions and clausifications.  (poly.ml 1-130)                 -/
/- ------------------------------------------------------------------------- -/

structure Defs where
  -- @@FIELDS
  poly : thm
  POLY_CONST : thm
  POLY_X : thm
  poly_add : thm
  poly_cmul : thm
  poly_neg : thm
  poly_mul : thm
  poly_exp : thm
  poly_diff_aux : thm
  poly_diff : thm
  LENGTH_POLY_DIFF_AUX : thm
  LENGTH_POLY_DIFF : thm
  POLY_ADD_CLAUSES : thm
  POLY_CMUL_CLAUSES : thm
  POLY_NEG_CLAUSES : thm
  POLY_MUL_CLAUSES : thm
  POLY_DIFF_CLAUSES : thm
  deriving Inhabited

@[nospecialize]
def setupDefs [HolBase] (D : PolyDeps) :
    ExceptT String IO Defs := do
  -- @@SCOPE BEGIN
  let { LIST_INDUCT_TAC, REAL_ARITH_TAC, new_definition, new_recursive_definition,
        overload_interface, override_interface, parse_as_infix, prioritize_real, .. } := D
  let { HD, LENGTH, NOT_CONS_NIL, PRE, .. } := D.core1
  let { REAL_MUL_LID, REAL_MUL_LNEG, TL, list_RECURSION, num_RECURSION, .. } := D.core2
  -- @@SCOPE END

  prioritize_real

  parse_as_infix ("++", (16, "right"))
  parse_as_infix ("**", (20, "right"))
  parse_as_infix ("##", (20, "right"))
  parse_as_infix ("divides", (14, "right"))
  parse_as_infix ("exp", (22, "right"))

  override_interface "++" (← q r"poly_add:real list->real list->real list")
  override_interface "**" (← q r"poly_mul:real list->real list->real list")
  override_interface "##" (← q r"poly_cmul:real->real list->real list")
  override_interface "neg" (← q r"poly_neg:real list->real list")
  override_interface "exp" (← q r"poly_exp:real list -> num -> real list")
  override_interface "diff" (← q r"poly_diff:real list->real list")

  overload_interface "divides" (← q r"poly_divides:real list->real list->bool")

  /- --------------------------------------------------------------------- -/
  /- Application of polynomial as a real function.                         -/
  /- --------------------------------------------------------------------- -/

  let poly ← new_recursive_definition list_RECURSION
   r"(poly [] x = &0) /\
   (poly (CONS h t) x = h + x * poly t x)"

  let POLY_CONST ← prove
   r"!c x. poly [c] x = c"
   (REWRITE_TAC [poly] THEN REAL_ARITH_TAC)

  let POLY_X ← prove
   r"!c x. poly [&0; &1] x = x"
   (REWRITE_TAC [poly] THEN REAL_ARITH_TAC)

  /- --------------------------------------------------------------------- -/
  /- Arithmetic operations on polynomials.                                 -/
  /- --------------------------------------------------------------------- -/

  let poly_add ← new_recursive_definition list_RECURSION
   r"([] ++ l2 = l2) /\
   ((CONS h t) ++ l2 =
        (if l2 = [] then CONS h t
                    else CONS (h + HD l2) (t ++ TL l2)))"

  let poly_cmul ← new_recursive_definition list_RECURSION
   r"(c ## [] = []) /\
   (c ## (CONS h t) = CONS (c * h) (c ## t))"

  let poly_neg ← new_definition
   r"neg = (##) (--(&1))"

  let poly_mul ← new_recursive_definition list_RECURSION
   r"([] ** l2 = []) /\
   ((CONS h t) ** l2 =
       (if t = [] then h ## l2
                  else (h ## l2) ++ CONS (&0) (t ** l2)))"

  let poly_exp ← new_recursive_definition num_RECURSION
   r"(p exp 0 = [&1]) /\
   (p exp (SUC n) = p ** p exp n)"

  /- --------------------------------------------------------------------- -/
  /- Differentiation of polynomials (needs an auxiliary function).         -/
  /- --------------------------------------------------------------------- -/

  let poly_diff_aux ← new_recursive_definition list_RECURSION
   r"(poly_diff_aux n [] = []) /\
   (poly_diff_aux n (CONS h t) = CONS (&n * h) (poly_diff_aux (SUC n) t))"

  let poly_diff ← new_definition
   r"diff l = (if l = [] then [] else (poly_diff_aux 1 (TL l)))"

  /- --------------------------------------------------------------------- -/
  /- Lengths.                                                              -/
  /- --------------------------------------------------------------------- -/

  let LENGTH_POLY_DIFF_AUX ← prove
   r"!l n. LENGTH(poly_diff_aux n l) = LENGTH l"
   (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH, poly_diff_aux])

  let LENGTH_POLY_DIFF ← prove
   r"!l. LENGTH(poly_diff l) = PRE(LENGTH l)"
   (LIST_INDUCT_TAC THEN
    SIMP_TAC [poly_diff, LENGTH, LENGTH_POLY_DIFF_AUX, NOT_CONS_NIL, TL, PRE])

  /- --------------------------------------------------------------------- -/
  /- Useful clausifications.                                               -/
  /- --------------------------------------------------------------------- -/

  let POLY_ADD_CLAUSES ← prove
   r"([] ++ p2 = p2) /\
   (p1 ++ [] = p1) /\
   ((CONS h1 t1) ++ (CONS h2 t2) = CONS (h1 + h2) (t1 ++ t2))"
   (REWRITE_TAC [poly_add, NOT_CONS_NIL, HD, TL] THEN
    SPEC_TAC (← q r"p1:real list", ← q r"p1:real list") THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [poly_add])

  let POLY_CMUL_CLAUSES ← prove
   r"(c ## [] = []) /\
   (c ## (CONS h t) = CONS (c * h) (c ## t))"
   (REWRITE_TAC [poly_cmul])

  let POLY_NEG_CLAUSES ← prove
   r"(neg [] = []) /\
   (neg (CONS h t) = CONS (--h) (neg t))"
   (REWRITE_TAC [poly_neg, POLY_CMUL_CLAUSES, REAL_MUL_LNEG, REAL_MUL_LID])

  let POLY_MUL_CLAUSES ← prove
   r"([] ** p2 = []) /\
   ([h1] ** p2 = h1 ## p2) /\
   ((CONS h1 (CONS k1 t1)) ** p2 = h1 ## p2 ++ CONS (&0) (CONS k1 t1 ** p2))"
   (REWRITE_TAC [poly_mul, NOT_CONS_NIL])

  let POLY_DIFF_CLAUSES ← prove
   r"(diff [] = []) /\
   (diff [c] = []) /\
   (diff (CONS h t) = poly_diff_aux 1 t)"
   (REWRITE_TAC [poly_diff, NOT_CONS_NIL, HD, TL, poly_diff_aux])

  -- @@RETURN BEGIN
  return { poly, POLY_CONST, POLY_X, poly_add, poly_cmul, poly_neg, poly_mul, poly_exp,
           poly_diff_aux, poly_diff, LENGTH_POLY_DIFF_AUX, LENGTH_POLY_DIFF,
           POLY_ADD_CLAUSES, POLY_CMUL_CLAUSES, POLY_NEG_CLAUSES, POLY_MUL_CLAUSES,
           POLY_DIFF_CLAUSES }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Natural consequences of the definitions; derivative lemma and derivative; -/
/- trivial consequences.  (poly.ml 132-316)                                  -/
/- ------------------------------------------------------------------------- -/

structure Consequences where
  -- @@FIELDS
  POLY_ADD : thm
  POLY_CMUL : thm
  POLY_NEG : thm
  POLY_MUL : thm
  POLY_EXP : thm
  POLY_DIFF_LEMMA : thm
  POLY_DIFF : thm
  POLY_DIFFERENTIABLE : thm
  POLY_CONT : thm
  POLY_IVT_POS : thm
  POLY_IVT_NEG : thm
  POLY_MVT : thm
  POLY_MVT_ADD : thm
  deriving Inhabited

@[nospecialize]
def setupConsequences [HolBase] (D : PolyDeps) (BDefs : Defs) :
    ExceptT String IO Consequences := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, LIST_INDUCT_TAC, REAL_ARITH, REAL_ARITH_TAC, .. } := D
  let { DIFF_ADD, DIFF_CMUL, DIFF_CONST, DIFF_CONT, DIFF_POW, DIFF_UNIQ, HD, IVT, MVT,
        NOT_CONS_NIL, POW_1, REAL_ADD_LID, REAL_ADD_RID, REAL_EQ_ADD_LCANCEL,
        REAL_LDISTRIB, REAL_LE_REFL, .. } := D.core1
  let { REAL_LT_ADDR, REAL_LT_IMP_LE, REAL_LT_LE, REAL_LT_NEGTOTAL, REAL_LT_REFL,
        REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_MUL_SYM,
        SUC_SUB1, TL, differentiable, pow, real_gt, real_pow, .. } := D.core2
  let { POLY_DIFF_CLAUSES, poly, poly_add, poly_cmul, poly_diff_aux, poly_exp,
        poly_mul, poly_neg, .. } := BDefs
  -- @@SCOPE END

  /- --------------------------------------------------------------------- -/
  /- Various natural consequences of syntactic definitions.                -/
  /- --------------------------------------------------------------------- -/

  let POLY_ADD ← prove
   r"!p1 p2 x. poly (p1 ++ p2) x = poly p1 x + poly p2 x"
   (LIST_INDUCT_TAC THEN REWRITE_TAC [poly_add, poly, REAL_ADD_LID] THEN
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [NOT_CONS_NIL, HD, TL, poly, REAL_ADD_RID] THEN
    REAL_ARITH_TAC)

  let POLY_CMUL ← prove
   r"!p c x. poly (c ## p) x = c * poly p x"
   (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [poly, poly_cmul] THEN
    REAL_ARITH_TAC)

  let POLY_NEG ← prove
   r"!p x. poly (neg p) x = --(poly p x)"
   (REWRITE_TAC [poly_neg, POLY_CMUL] THEN
    REAL_ARITH_TAC)

  let POLY_MUL ← prove
   r"!x p1 p2. poly (p1 ** p2) x = poly p1 x * poly p2 x"
   (GEN_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [poly_mul, poly, REAL_MUL_LZERO, POLY_CMUL, POLY_ADD] THEN
    SPEC_TAC (← q r"h:real", ← q r"h:real") THEN
    SPEC_TAC (← q r"t:real list", ← q r"t:real list") THEN
    LIST_INDUCT_TAC THEN
    REWRITE_TAC [poly_mul, POLY_CMUL, POLY_ADD, poly, POLY_CMUL,
      REAL_MUL_RZERO, REAL_ADD_RID, NOT_CONS_NIL] THEN
    ASM_REWRITE_TAC [POLY_ADD, POLY_CMUL, poly] THEN
    REAL_ARITH_TAC)

  let POLY_EXP ← prove
   r"!p n x. poly (p exp n) x = (poly p x) pow n"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [poly_exp, real_pow, POLY_MUL] THEN
    REWRITE_TAC [poly] THEN REAL_ARITH_TAC)

  /- --------------------------------------------------------------------- -/
  /- The derivative is a bit more complicated.                             -/
  /- --------------------------------------------------------------------- -/

  let POLY_DIFF_LEMMA ← prove
   r"!l n x. ((\x. (x pow (SUC n)) * poly l x) diffl
                   ((x pow n) * poly (poly_diff_aux (SUC n) l) x))(x)"
   (LIST_INDUCT_TAC THEN
    REWRITE_TAC [poly, poly_diff_aux, REAL_MUL_RZERO, DIFF_CONST] THEN
    MAP_EVERY X_GEN_TAC [← q "n:num", ← q "x:real"] THEN
    REWRITE_TAC [REAL_LDISTRIB, REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC [← GSYM (← ONCE_REWRITE_RULE [REAL_MUL_SYM] (← CONJUNCT2 pow))] THEN
    POP_ASSUM (MP_TAC o SPECL [← q "SUC n", ← q "x:real"]) THEN
    SUBGOAL_THEN (← q r"(((\x. (x pow (SUC n)) * h)) diffl
                        ((x pow n) * &(SUC n) * h))(x)")
    (fun th => DISCH_THEN (MP_TAC o CONJ th)) THENL
     [REWRITE_TAC [REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      MP_TAC (← SPEC (← q r"\x. x pow (SUC n)") DIFF_CMUL) THEN BETA_TAC THEN
      DISCH_THEN MATCH_MP_TAC THEN
      MP_TAC (← SPEC (← q "SUC n") DIFF_POW) THEN REWRITE_TAC [SUC_SUB1] THEN
      DISCH_THEN (MATCH_ACCEPT_TAC o ONCE_REWRITE_RULE [REAL_MUL_SYM]),
      DISCH_THEN (MP_TAC o MATCH_MP DIFF_ADD) THEN BETA_TAC THEN
      REWRITE_TAC [REAL_MUL_ASSOC]])

  let POLY_DIFF ← prove
   r"!l x. ((\x. poly l x) diffl (poly (diff l) x))(x)"
   (LIST_INDUCT_TAC THEN REWRITE_TAC [POLY_DIFF_CLAUSES] THEN
    ONCE_REWRITE_TAC [← SYM (← ExceptT.mk (D.ETA_CONV (← q r"\x. poly l x")))] THEN
    REWRITE_TAC [poly, DIFF_CONST] THEN
    MAP_EVERY X_GEN_TAC [← q "x:real"] THEN
    MP_TAC (← SPECL [← q "t:(real)list", ← q "0", ← q "x:real"] POLY_DIFF_LEMMA) THEN
    REWRITE_TAC [← SYM (← ExceptT.mk (D.num_CONV (← q "1")))] THEN
    REWRITE_TAC [pow, REAL_MUL_LID] THEN
    REWRITE_TAC [POW_1] THEN
    DISCH_THEN (MP_TAC o CONJ (← SPECL [← q "h:real", ← q "x:real"] DIFF_CONST)) THEN
    DISCH_THEN (MP_TAC o MATCH_MP DIFF_ADD) THEN BETA_TAC THEN
    REWRITE_TAC [REAL_ADD_LID])

  /- --------------------------------------------------------------------- -/
  /- Trivial consequences.                                                 -/
  /- --------------------------------------------------------------------- -/

  let POLY_DIFFERENTIABLE ← prove
   r"!l x. (\x. poly l x) differentiable x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [differentiable] THEN
    EXISTS_TAC (← q r"poly (diff l) x") THEN
    REWRITE_TAC [POLY_DIFF])

  let POLY_CONT ← prove
   r"!l x. (\x. poly l x) contl x"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC DIFF_CONT THEN
    EXISTS_TAC (← q r"poly (diff l) x") THEN
    MATCH_ACCEPT_TAC POLY_DIFF)

  let POLY_IVT_POS ← prove
   r"!p a b. a < b /\ poly p a < &0 /\ poly p b > &0
           ==> ?x. a < x /\ x < b /\ (poly p x = &0)"
   (REWRITE_TAC [real_gt] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"\x. poly p x", ← q "a:real", ← q "b:real", ← q "&0"] IVT) THEN
    REWRITE_TAC [POLY_CONT] THEN
    EVERY_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP REAL_LT_IMP_LE th])) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "x:real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q "x:real") THEN ASM_REWRITE_TAC [REAL_LT_LE] THEN
    CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [REAL_LT_REFL]) THEN
    FIRST_ASSUM (HolCore.Tactics.CONTR_TAC HolBase.B))

  let POLY_IVT_NEG ← prove
   r"!p a b. a < b /\ poly p a > &0 /\ poly p b < &0
           ==> ?x. a < x /\ x < b /\ (poly p x = &0)"
   (← do
    let r2 ← REAL_ARITH (← q r"(--x = &0) <=> (x = &0)")
    let r1 ← REAL_ARITH (← q r"(--x < &0 <=> x > &0) /\ (--x > &0 <=> x < &0)")
    pure (REPEAT STRIP_TAC THEN MP_TAC (← SPEC (← q r"poly_neg p") POLY_IVT_POS) THEN
    REWRITE_TAC [POLY_NEG, r1] THEN
    DISCH_THEN (MP_TAC o SPECL [← q "a:real", ← q "b:real"]) THEN
    ASM_REWRITE_TAC [r2]))

  let POLY_MVT ← prove
   r"!p a b. a < b ==>
           ?x. a < x /\ x < b /\
              (poly p b - poly p a = (b - a) * poly (diff p) x)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"poly p", ← q "a:real", ← q "b:real"] MVT) THEN
    ASM_REWRITE_TAC [← CONV_RULE (DEPTH_CONV D.ETA_CONV) (← SPEC_ALL POLY_CONT),
      ← CONV_RULE (DEPTH_CONV D.ETA_CONV) (← SPEC_ALL POLY_DIFFERENTIABLE)] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "l:real") MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "x:real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q "x:real") THEN ASM_REWRITE_TAC [] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC DIFF_UNIQ THEN
    EXISTS_TAC (← q r"poly p") THEN EXISTS_TAC (← q "x:real") THEN
    ASM_REWRITE_TAC [← CONV_RULE (DEPTH_CONV D.ETA_CONV) (← SPEC_ALL POLY_DIFF)])

  let POLY_MVT_ADD ← prove
   r"!p a x. ?y. abs(y) <= abs(x) /\
               (poly p (a + x) = poly p a + x * poly (diff p) (a + y))"
   (← do
    let a5 ← REAL_ARITH (← q r"x + (y - x) = y")
    let a4 ← REAL_ARITH (← q r"(x - y = (a - (a + b)) * z) <=>
                            (x = y + b * --z)")
    let a3 ← REAL_ARITH (← q r"a + x < a <=> &0 < --x")
    let a2 ← REAL_ARITH (← q r"x + (y - x) = y")
    let a1 ← REAL_ARITH (← q r"(x - y = ((a + b) - a) * z) <=>
                            (x = y + b * z)")
    pure (REPEAT GEN_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (← SPEC (← q "x:real") REAL_LT_NEGTOTAL) THENL
     [EXISTS_TAC (← q "&0") THEN
      ASM_REWRITE_TAC [REAL_LE_REFL, REAL_ADD_RID, REAL_MUL_LZERO],
      MP_TAC (← SPECL [← q "p:real list", ← q "a:real", ← q r"a + x"] POLY_MVT) THEN
      ASM_REWRITE_TAC [REAL_LT_ADDR] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "z:real") MP_TAC) THEN
      REWRITE_TAC [a1] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [REAL_EQ_ADD_LCANCEL] THEN
      EXISTS_TAC (← q r"z - a") THEN REWRITE_TAC [a2] THEN
      MAP_EVERY UNDISCH_TAC [← q r"&0 < x", ← q r"a < z", ← q r"z < a + x"] THEN
      REAL_ARITH_TAC,
      MP_TAC (← SPECL [← q "p:real list", ← q r"a + x", ← q "a:real"] POLY_MVT) THEN
      ASM_REWRITE_TAC [a3] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "z:real") MP_TAC) THEN
      REWRITE_TAC [a4] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [REAL_EQ_ADD_LCANCEL] THEN
      EXISTS_TAC (← q r"z - a") THEN REWRITE_TAC [a5] THEN
      MAP_EVERY UNDISCH_TAC [← q r"&0 < --x", ← q r"a + x < z", ← q r"z < a"] THEN
      REAL_ARITH_TAC]))

  -- @@RETURN BEGIN
  return { POLY_ADD, POLY_CMUL, POLY_NEG, POLY_MUL, POLY_EXP, POLY_DIFF_LEMMA, POLY_DIFF,
           POLY_DIFFERENTIABLE, POLY_CONT, POLY_IVT_POS, POLY_IVT_NEG, POLY_MVT,
           POLY_MVT_ADD }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Lemmas; lemmas for derivatives; final results for derivatives; the key    -/
/- divisibility property; length rather than degree.  (poly.ml 318-448)      -/
/- ------------------------------------------------------------------------- -/

structure Derivs where
  -- @@FIELDS
  POLY_ADD_RZERO : thm
  POLY_MUL_ASSOC : thm
  POLY_EXP_ADD : thm
  POLY_DIFF_AUX_ADD : thm
  POLY_DIFF_AUX_CMUL : thm
  POLY_DIFF_AUX_NEG : thm
  POLY_DIFF_AUX_MUL_LEMMA : thm
  POLY_DIFF_ADD : thm
  POLY_DIFF_CMUL : thm
  POLY_DIFF_NEG : thm
  POLY_DIFF_MUL_LEMMA : thm
  POLY_DIFF_MUL : thm
  POLY_DIFF_EXP : thm
  POLY_DIFF_EXP_PRIME : thm
  POLY_LINEAR_REM : thm
  POLY_LINEAR_DIVIDES : thm
  POLY_LENGTH_MUL : thm
  deriving Inhabited

@[nospecialize]
def setupDerivs [HolBase] (D : PolyDeps) (BDefs : Defs) (BConsequences : Consequences) :
    ExceptT String IO Derivs := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, LIST_INDUCT_TAC, REAL_ARITH, REAL_ARITH_TAC, .. } := D
  let { ADD1, ADD_CLAUSES, CONS_11, FUN_EQ_THM, HD, LENGTH, NOT_CONS_NIL, REAL_ADD_AC,
        REAL_ADD_LID, REAL_ADD_RDISTRIB, REAL_ADD_RID, .. } := D.core1
  let { REAL_MUL_AC, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_RID, REAL_MUL_RZERO,
        REAL_OF_NUM_ADD, REAL_OF_NUM_SUC, TL, .. } := D.core2
  let { POLY_ADD_CLAUSES, POLY_DIFF_CLAUSES, POLY_MUL_CLAUSES, poly, poly_add,
        poly_cmul, poly_diff, poly_diff_aux, poly_exp, poly_mul, poly_neg, .. } := BDefs
  let { POLY_ADD, POLY_CMUL, POLY_MUL, .. } := BConsequences
  -- @@SCOPE END

  /- --------------------------------------------------------------------- -/
  /- Lemmas.                                                               -/
  /- --------------------------------------------------------------------- -/

  let POLY_ADD_RZERO ← prove
   r"!p. poly (p ++ []) = poly p"
   (REWRITE_TAC [FUN_EQ_THM, POLY_ADD, poly, REAL_ADD_RID])

  let POLY_MUL_ASSOC ← prove
   r"!p q r. poly (p ** (q ** r)) = poly ((p ** q) ** r)"
   (REWRITE_TAC [FUN_EQ_THM, POLY_MUL, REAL_MUL_ASSOC])

  let POLY_EXP_ADD ← prove
   r"!d n p. poly(p exp (n + d)) = poly(p exp n ** p exp d)"
   (REWRITE_TAC [FUN_EQ_THM, POLY_MUL] THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC [POLY_MUL, ADD_CLAUSES, poly_exp, poly] THEN
    REAL_ARITH_TAC)

  /- --------------------------------------------------------------------- -/
  /- Lemmas for derivatives.                                               -/
  /- --------------------------------------------------------------------- -/

  let POLY_DIFF_AUX_ADD ← prove
   r"!p1 p2 n. poly (poly_diff_aux n (p1 ++ p2)) =
             poly (poly_diff_aux n p1 ++ poly_diff_aux n p2)"
   (REPEAT (LIST_INDUCT_TAC THEN REWRITE_TAC [poly_diff_aux, poly_add]) THEN
    ASM_REWRITE_TAC [poly_diff_aux, FUN_EQ_THM, poly, NOT_CONS_NIL, HD, TL] THEN
    REAL_ARITH_TAC)

  let POLY_DIFF_AUX_CMUL ← prove
   r"!p c n. poly (poly_diff_aux n (c ## p)) =
           poly (c ## poly_diff_aux n p)"
   (LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [FUN_EQ_THM, poly, poly_diff_aux, poly_cmul, REAL_MUL_AC])

  let POLY_DIFF_AUX_NEG ← prove
   r"!p n.  poly (poly_diff_aux n (neg p)) =
          poly (neg (poly_diff_aux n p))"
   (REWRITE_TAC [poly_neg, POLY_DIFF_AUX_CMUL])

  let POLY_DIFF_AUX_MUL_LEMMA ← prove
   r"!p n. poly (poly_diff_aux (SUC n) p) = poly (poly_diff_aux n p ++ p)"
   (LIST_INDUCT_TAC THEN REWRITE_TAC [poly_diff_aux, poly_add, NOT_CONS_NIL] THEN
    ASM_REWRITE_TAC [HD, TL, poly, FUN_EQ_THM] THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_SUC, REAL_ADD_RDISTRIB, REAL_MUL_LID])

  /- --------------------------------------------------------------------- -/
  /- Final results for derivatives.                                        -/
  /- --------------------------------------------------------------------- -/

  let POLY_DIFF_ADD ← prove
   r"!p1 p2. poly (diff (p1 ++ p2)) =
           poly (diff p1  ++ diff p2)"
   (REPEAT LIST_INDUCT_TAC THEN
    REWRITE_TAC [poly_add, poly_diff, NOT_CONS_NIL, POLY_ADD_RZERO] THEN
    ASM_REWRITE_TAC [HD, TL, POLY_DIFF_AUX_ADD])

  let POLY_DIFF_CMUL ← prove
   r"!p c. poly (diff (c ## p)) = poly (c ## diff p)"
   (LIST_INDUCT_TAC THEN REWRITE_TAC [poly_diff, poly_cmul] THEN
    REWRITE_TAC [NOT_CONS_NIL, HD, TL, POLY_DIFF_AUX_CMUL])

  let POLY_DIFF_NEG ← prove
   r"!p. poly (diff (neg p)) = poly (neg (diff p))"
   (REWRITE_TAC [poly_neg, POLY_DIFF_CMUL])

  let POLY_DIFF_MUL_LEMMA ← prove
   r"!t h. poly (diff (CONS h t)) =
         poly (CONS (&0) (diff t) ++ t)"
   (REWRITE_TAC [poly_diff, NOT_CONS_NIL] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [poly_diff_aux, NOT_CONS_NIL, HD, TL] THENL
     [REWRITE_TAC [FUN_EQ_THM, poly, poly_add, REAL_MUL_RZERO, REAL_ADD_LID],
      REWRITE_TAC [FUN_EQ_THM, poly, POLY_DIFF_AUX_MUL_LEMMA, POLY_ADD] THEN
      REAL_ARITH_TAC])

  let POLY_DIFF_MUL ← prove
   r"!p1 p2. poly (diff (p1 ** p2)) =
           poly (p1 ** diff p2 ++ diff p1 ** p2)"
   (LIST_INDUCT_TAC THEN REWRITE_TAC [poly_mul] THENL
     [REWRITE_TAC [poly_diff, poly_add, poly_mul], ALL_TAC] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
     [REWRITE_TAC [POLY_DIFF_CLAUSES] THEN
      REWRITE_TAC [poly_add, poly_mul, POLY_ADD_RZERO, POLY_DIFF_CMUL],
      ALL_TAC] THEN
    REWRITE_TAC [FUN_EQ_THM, POLY_DIFF_ADD, POLY_ADD] THEN
    REWRITE_TAC [poly, POLY_ADD, POLY_DIFF_MUL_LEMMA, POLY_MUL] THEN
    ASM_REWRITE_TAC [POLY_DIFF_CMUL, POLY_ADD, POLY_MUL] THEN
    REAL_ARITH_TAC)

  let POLY_DIFF_EXP ← prove
   r"!p n. poly (diff (p exp (SUC n))) =
         poly ((&(SUC n) ## (p exp n)) ** diff p)"
   (GEN_TAC THEN INDUCT_TAC THEN ONCE_REWRITE_TAC [poly_exp] THENL
     [REWRITE_TAC [poly_exp, POLY_DIFF_MUL] THEN
      REWRITE_TAC [FUN_EQ_THM, POLY_MUL, POLY_ADD, POLY_CMUL] THEN
      REWRITE_TAC [poly, POLY_DIFF_CLAUSES, ADD1, ADD_CLAUSES] THEN
      REAL_ARITH_TAC,
      REWRITE_TAC [POLY_DIFF_MUL] THEN
      ASM_REWRITE_TAC [POLY_MUL, POLY_ADD, FUN_EQ_THM, POLY_CMUL] THEN
      REWRITE_TAC [poly_exp, POLY_MUL] THEN
      REWRITE_TAC [ADD1, ← GSYM REAL_OF_NUM_ADD] THEN
      REAL_ARITH_TAC])

  let POLY_DIFF_EXP_PRIME ← prove
   r"!n a. poly (diff ([--a; &1] exp (SUC n))) =
         poly (&(SUC n) ## ([--a; &1] exp n))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [POLY_DIFF_EXP] THEN
    REWRITE_TAC [FUN_EQ_THM, POLY_MUL] THEN
    REWRITE_TAC [poly_diff, poly_diff_aux, TL, NOT_CONS_NIL] THEN
    REWRITE_TAC [poly] THEN REAL_ARITH_TAC)

  /- --------------------------------------------------------------------- -/
  /- Key property that f(a) = 0 ==> (x - a) divides p(x). Very delicate!   -/
  /- --------------------------------------------------------------------- -/

  let POLY_LINEAR_REM ← prove
   r"!t h. ?q r. CONS h t = [r] ++ [--a; &1] ** q"
   (LIST_INDUCT_TAC THEN REWRITE_TAC [] THENL
     [GEN_TAC THEN EXISTS_TAC (← q r"[]:real list") THEN
      EXISTS_TAC (← q "h:real") THEN
      REWRITE_TAC [poly_add, poly_mul, poly_cmul, NOT_CONS_NIL] THEN
      REWRITE_TAC [HD, TL, REAL_ADD_RID],
      X_GEN_TAC (← q "k:real") THEN POP_ASSUM (STRIP_ASSUME_TAC o SPEC (← q "h:real")) THEN
      EXISTS_TAC (← q r"CONS (r:real) q") THEN EXISTS_TAC (← q r"r * a + k") THEN
      ASM_REWRITE_TAC [POLY_ADD_CLAUSES, POLY_MUL_CLAUSES, poly_cmul] THEN
      REWRITE_TAC [CONS_11] THEN CONJ_TAC THENL
       [REAL_ARITH_TAC, ALL_TAC] THEN
      SPEC_TAC (← q r"q:real list", ← q r"q:real list") THEN
      LIST_INDUCT_TAC THEN
      REWRITE_TAC [POLY_ADD_CLAUSES, POLY_MUL_CLAUSES, poly_cmul] THEN
      REWRITE_TAC [REAL_ADD_RID, REAL_MUL_LID] THEN
      REWRITE_TAC [REAL_ADD_AC]])

  let POLY_LINEAR_DIVIDES ← prove
   r"!a p. (poly p a = &0) <=> (p = []) \/ ?q. p = [--a; &1] ** q"
   (GEN_TAC THEN LIST_INDUCT_TAC THENL
     [REWRITE_TAC [poly], ALL_TAC] THEN
    EQ_TAC THEN STRIP_TAC THENL
     [DISJ2_TAC THEN STRIP_ASSUME_TAC (← SPEC_ALL POLY_LINEAR_REM) THEN
      EXISTS_TAC (← q r"q:real list") THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"r = &0") SUBST_ALL_TAC THENL
       [UNDISCH_TAC (← q r"poly (CONS h t) a = &0") THEN
        ASM_REWRITE_TAC [] THEN REWRITE_TAC [POLY_ADD, POLY_MUL] THEN
        REWRITE_TAC [poly, REAL_MUL_RZERO, REAL_ADD_RID, REAL_MUL_RID] THEN
        REWRITE_TAC [← REAL_ARITH (← q r"--a + a = &0")] THEN REAL_ARITH_TAC,
        REWRITE_TAC [poly_mul] THEN REWRITE_TAC [NOT_CONS_NIL] THEN
        SPEC_TAC (← q r"q:real list", ← q r"q:real list") THEN LIST_INDUCT_TAC THENL
         [REWRITE_TAC [poly_cmul, poly_add, NOT_CONS_NIL, HD, TL, REAL_ADD_LID],
          REWRITE_TAC [poly_cmul, poly_add, NOT_CONS_NIL, HD, TL, REAL_ADD_LID]]],
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [poly],
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [poly] THEN
      REWRITE_TAC [POLY_MUL] THEN REWRITE_TAC [poly] THEN
      REWRITE_TAC [poly, REAL_MUL_RZERO, REAL_ADD_RID, REAL_MUL_RID] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"--a + a = &0")] THEN REAL_ARITH_TAC])

  /- --------------------------------------------------------------------- -/
  /- Thanks to the finesse of the above, we can use length rather than     -/
  /- degree.                                                               -/
  /- --------------------------------------------------------------------- -/

  let POLY_LENGTH_MUL ← prove
   r"!q. LENGTH([--a; &1] ** q) = SUC(LENGTH q)"
   (← do
    let lemma ← prove
     r"!p h k a. LENGTH (k ## p ++ CONS h (a ## p)) = SUC(LENGTH p)"
     (LIST_INDUCT_TAC THEN
      ASM_REWRITE_TAC [poly_cmul, POLY_ADD_CLAUSES, LENGTH])
    pure (REWRITE_TAC [poly_mul, NOT_CONS_NIL, lemma]))

  -- @@RETURN BEGIN
  return { POLY_ADD_RZERO, POLY_MUL_ASSOC, POLY_EXP_ADD, POLY_DIFF_AUX_ADD,
           POLY_DIFF_AUX_CMUL, POLY_DIFF_AUX_NEG, POLY_DIFF_AUX_MUL_LEMMA, POLY_DIFF_ADD,
           POLY_DIFF_CMUL, POLY_DIFF_NEG, POLY_DIFF_MUL_LEMMA, POLY_DIFF_MUL,
           POLY_DIFF_EXP, POLY_DIFF_EXP_PRIME, POLY_LINEAR_REM, POLY_LINEAR_DIVIDES,
           POLY_LENGTH_MUL }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Thus a nontrivial polynomial of degree n has no more than n roots.        -/
/- ------------------------------------------------------------------------- -/

structure RootsFinite where
  -- @@FIELDS
  POLY_ROOTS_INDEX_LEMMA : thm
  POLY_ROOTS_INDEX_LENGTH : thm
  POLY_ROOTS_FINITE_LEMMA : thm
  FINITE_LEMMA : thm
  POLY_ROOTS_FINITE : thm
  deriving Inhabited

@[nospecialize]
def setupRootsFinite [HolBase] (D : PolyDeps) (BDefs : Defs) (BConsequences : Consequences) (BDerivs : Derivs) :
    ExceptT String IO RootsFinite := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, .. } := D
  let { FUN_EQ_THM, LE, LEFT_IMP_EXISTS_THM, LENGTH_EQ_NIL, LT, LT_SUC_LE,
        NOT_EXISTS_THM, NOT_FORALL_THM, REAL_ENTIRE, .. } := D.core1
  let { REAL_LT_REFL, REAL_MUL_RZERO, RIGHT_IMP_EXISTS_THM, SUC_INJ, .. } := D.core2
  let { poly, .. } := BDefs
  let { POLY_MUL, .. } := BConsequences
  let { POLY_LENGTH_MUL, POLY_LINEAR_DIVIDES, .. } := BDerivs
  -- @@SCOPE END

  let POLY_ROOTS_INDEX_LEMMA ← prove
   r"!n. !p. ~(poly p = poly []) /\ (LENGTH p = n)
             ==> ?i. !x. (poly p (x) = &0) ==> ?m. m <= n /\ (x = i m)"
   (INDUCT_TAC THENL
     [REWRITE_TAC [LENGTH_EQ_NIL] THEN MESON_TAC [],
      REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"?a. poly p a = &0") THENL
       [UNDISCH_TAC (← q r"?a. poly p a = &0") THEN DISCH_THEN (CHOOSE_THEN MP_TAC) THEN
        GEN_REWRITE_TAC LAND_CONV [POLY_LINEAR_DIVIDES] THEN
        DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"q:real list") SUBST_ALL_TAC) THEN
        FIRST_ASSUM (undischCheck (fun c => pure (is_forall c))) THEN
        UNDISCH_TAC (← q r"~(poly ([-- a; &1] ** q) = poly [])") THEN
        POP_ASSUM MP_TAC THEN REWRITE_TAC [POLY_LENGTH_MUL, SUC_INJ] THEN
        DISCH_TAC THEN ASM_CASES_TAC (← q r"poly q = poly []") THENL
         [ASM_REWRITE_TAC [POLY_MUL, poly, REAL_MUL_RZERO, FUN_EQ_THM],
          DISCH_THEN (K ALL_TAC)] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"q:real list")) THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_TAC (← q r"i:num->real")) THEN
        EXISTS_TAC (← q r"\m. if m = SUC n then (a:real) else i m") THEN
        REWRITE_TAC [POLY_MUL, LE, REAL_ENTIRE] THEN
        X_GEN_TAC (← q r"x:real") THEN DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
         [DISCH_THEN (fun th => tactic_of do
           pure (EXISTS_TAC (← q r"SUC n") THEN MP_TAC th)) THEN
          REWRITE_TAC [poly] THEN REAL_ARITH_TAC,
          DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"m:num") STRIP_ASSUME_TAC) THEN
          EXISTS_TAC (← q r"m:num") THEN ASM_REWRITE_TAC [] THEN
          COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
          UNDISCH_TAC (← q r"m:num <= n") THEN ASM_REWRITE_TAC [] THEN ARITH_TAC],
        UNDISCH_TAC (← q r"~(?a. poly p a = &0)") THEN
        REWRITE_TAC [NOT_EXISTS_THM] THEN DISCH_TAC THEN ASM_REWRITE_TAC []]])

  let POLY_ROOTS_INDEX_LENGTH ← prove
   r"!p. ~(poly p = poly [])
         ==> ?i. !x. (poly p(x) = &0) ==> ?n. n <= LENGTH p /\ (x = i n)"
   (MESON_TAC [POLY_ROOTS_INDEX_LEMMA])

  let POLY_ROOTS_FINITE_LEMMA ← prove
   r"!p. ~(poly p = poly [])
         ==> ?N i. !x. (poly p(x) = &0) ==> ?n:num. n < N /\ (x = i n)"
   (MESON_TAC [POLY_ROOTS_INDEX_LENGTH, LT_SUC_LE])

  let FINITE_LEMMA ← prove
   r"!i N P. (!x. P x ==> ?n:num. n < N /\ (x = i n))
             ==> ?a. !x. P x ==> x < a"
   (← do
    let r1 ← REAL_ARITH (← q r"!u v x. x < v ==> x < abs(v) + abs(u) + &1")
    let r2 ← REAL_ARITH (← q r"!x v. x < abs(v) + abs(x) + &1")
    pure (GEN_TAC THEN ONCE_REWRITE_TAC [RIGHT_IMP_EXISTS_THM] THEN INDUCT_TAC THENL
     [REWRITE_TAC [LT] THEN MESON_TAC [], ALL_TAC] THEN
    X_GEN_TAC (← q r"P:real->bool") THEN
    POP_ASSUM (MP_TAC o SPEC (← q r"\z. P z /\ ~(z = (i:num->real) N)")) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"a:real")) THEN
    EXISTS_TAC (← q r"abs(a) + abs(i(N:num)) + &1") THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [LT] THEN
    MP_TAC r2 THEN
    MP_TAC r1 THEN
    MESON_TAC []))

  let POLY_ROOTS_FINITE ← prove
   r"!p. ~(poly p = poly []) <=>
         ?N i. !x. (poly p(x) = &0) ==> ?n:num. n < N /\ (x = i n)"
   (GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [POLY_ROOTS_FINITE_LEMMA] THEN
    REWRITE_TAC [FUN_EQ_THM, LEFT_IMP_EXISTS_THM, NOT_FORALL_THM, poly] THEN
    MP_TAC (← GENL [← q r"i:num->real", ← q r"N:num"]
     (← SPECL [← q r"i:num->real", ← q r"N:num", ← q r"\x. poly p x = &0"] FINITE_LEMMA)) THEN
    REWRITE_TAC [] THEN MESON_TAC [REAL_LT_REFL])

  -- @@RETURN BEGIN
  return { POLY_ROOTS_INDEX_LEMMA, POLY_ROOTS_INDEX_LENGTH, POLY_ROOTS_FINITE_LEMMA,
           FINITE_LEMMA, POLY_ROOTS_FINITE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Hence get entirety and cancellation for polynomials.                      -/
/- ------------------------------------------------------------------------- -/

structure Entire where
  -- @@FIELDS
  POLY_ENTIRE_LEMMA : thm
  POLY_ENTIRE : thm
  POLY_MUL_LCANCEL : thm
  POLY_EXP_EQ_0 : thm
  POLY_PRIME_EQ_0 : thm
  POLY_EXP_PRIME_EQ_0 : thm
  deriving Inhabited

@[nospecialize]
def setupEntire [HolBase] (D : PolyDeps) (BDefs : Defs) (BConsequences : Consequences) (BRootsFinite : RootsFinite) :
    ExceptT String IO Entire := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, INDUCT_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, .. } := D
  let { ARITH, FUN_EQ_THM, LEFT_AND_FORALL_THM, LT_ADD_LCANCEL, NOT_SUC, REAL_ADD_RID,
        REAL_ENTIRE, .. } := D.core1
  let { REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_OF_NUM_EQ, .. } := D.core2
  let { poly, poly_exp, .. } := BDefs
  let { POLY_ADD, POLY_MUL, POLY_NEG, .. } := BConsequences
  let { POLY_ROOTS_FINITE, .. } := BRootsFinite
  -- @@SCOPE END

  let POLY_ENTIRE_LEMMA ← prove
   r"!p q. ~(poly p = poly []) /\ ~(poly q = poly [])
           ==> ~(poly (p ** q) = poly [])"
   (← do
    let a1 ← ARITH_RULE (← q r"~(m + n < m:num)")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [POLY_ROOTS_FINITE] THEN
    DISCH_THEN (CONJUNCTS_THEN MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"N2:num") (X_CHOOSE_TAC (← q r"i2:num->real"))) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"N1:num") (X_CHOOSE_TAC (← q r"i1:num->real"))) THEN
    EXISTS_TAC (← q r"N1 + N2:num") THEN
    EXISTS_TAC (← q r"\n:num. if n < N1 then i1(n):real else i2(n - N1)") THEN
    X_GEN_TAC (← q r"x:real") THEN REWRITE_TAC [REAL_ENTIRE, POLY_MUL] THEN
    DISCH_THEN (DISJ_CASES_THEN (ANTE_RES_THEN (X_CHOOSE_TAC (← q r"n:num")))) THENL
     [EXISTS_TAC (← q r"n:num") THEN ASM_REWRITE_TAC [] THEN
      FIRST_ASSUM (MP_TAC o CONJUNCT1) THEN ARITH_TAC,
      EXISTS_TAC (← q r"N1 + n:num") THEN ASM_REWRITE_TAC [LT_ADD_LCANCEL] THEN
      REWRITE_TAC [a1] THEN
      AP_TERM_TAC THEN ARITH_TAC]))

  let POLY_ENTIRE ← prove
   r"!p q. (poly (p ** q) = poly []) <=>
           (poly p = poly []) \/ (poly q = poly [])"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [MESON_TAC [POLY_ENTIRE_LEMMA],
      REWRITE_TAC [FUN_EQ_THM, POLY_MUL] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [REAL_MUL_RZERO, REAL_MUL_LZERO, poly]])

  let POLY_MUL_LCANCEL ← prove
   r"!p q r. (poly (p ** q) = poly (p ** r)) <=>
             (poly p = poly []) \/ (poly q = poly r)"
   (← do
    let lemma2 ← prove
     r"!p q r. poly (p ** q ++ neg(p ** r)) = poly (p ** (q ++ neg(r)))"
     (REWRITE_TAC [FUN_EQ_THM, POLY_ADD, POLY_NEG, POLY_MUL] THEN
      REAL_ARITH_TAC)
    let lemma1 ← prove
     r"!p q. (poly (p ++ neg q) = poly []) <=> (poly p = poly q)"
     (← do
      let r1 ← REAL_ARITH (← q r"(p + --q = &0) <=> (p = q)")
      pure (REWRITE_TAC [FUN_EQ_THM, POLY_ADD, POLY_NEG, poly] THEN
      REWRITE_TAC [r1]))
    pure (ONCE_REWRITE_TAC [← GSYM lemma1] THEN
    REWRITE_TAC [lemma2, POLY_ENTIRE] THEN
    REWRITE_TAC [lemma1]))

  let POLY_EXP_EQ_0 ← prove
   r"!p n. (poly (p exp n) = poly []) <=> (poly p = poly []) /\ ~(n = 0)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM, poly] THEN
    REWRITE_TAC [LEFT_AND_FORALL_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
    SPEC_TAC (← q r"n:num", ← q r"n:num") THEN INDUCT_TAC THEN
    REWRITE_TAC [poly_exp, poly, REAL_MUL_RZERO, REAL_ADD_RID,
      REAL_OF_NUM_EQ, ARITH, NOT_SUC] THEN
    ASM_REWRITE_TAC [POLY_MUL, poly, REAL_ENTIRE] THEN
    CONV_TAC TAUT)

  let POLY_PRIME_EQ_0 ← prove
   r"!a. ~(poly [a ; &1] = poly [])"
   (GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM, poly] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"&1 - a")) THEN
    REAL_ARITH_TAC)

  let POLY_EXP_PRIME_EQ_0 ← prove
   r"!a n. ~(poly ([a ; &1] exp n) = poly [])"
   (MESON_TAC [POLY_EXP_EQ_0, POLY_PRIME_EQ_0])

  -- @@RETURN BEGIN
  return { POLY_ENTIRE_LEMMA, POLY_ENTIRE, POLY_MUL_LCANCEL, POLY_EXP_EQ_0,
           POLY_PRIME_EQ_0, POLY_EXP_PRIME_EQ_0 }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Can also prove a more "constructive" notion of polynomial being trivial.  -/
/- ------------------------------------------------------------------------- -/

structure Zero where
  -- @@FIELDS
  POLY_ZERO_LEMMA : thm
  POLY_ZERO : thm
  deriving Inhabited

@[nospecialize]
def setupZero [HolBase] (D : PolyDeps) (BDefs : Defs) (BRootsFinite : RootsFinite) :
    ExceptT String IO Zero := do
  -- @@SCOPE BEGIN
  let { LIST_INDUCT_TAC, REAL_ARITH_TAC, .. } := D
  let { ALL, DE_MORGAN_THM, FUN_EQ_THM, REAL_ADD_LID, REAL_ENTIRE, .. } := D.core1
  let { poly, .. } := BDefs
  let { FINITE_LEMMA, POLY_ROOTS_FINITE, .. } := BRootsFinite
  -- @@SCOPE END

  let POLY_ZERO_LEMMA ← prove
   r"!h t. (poly (CONS h t) = poly []) ==> (h = &0) /\ (poly t = poly [])"
   (← do
    let lemma ← REWRITE_RULE [FUN_EQ_THM, poly] POLY_ROOTS_FINITE
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM, poly] THEN
    ASM_CASES_TAC (← q r"h = &0") THEN ASM_REWRITE_TAC [] THENL
     [REWRITE_TAC [REAL_ADD_LID],
      DISCH_THEN (MP_TAC o SPEC (← q r"&0")) THEN
      POP_ASSUM MP_TAC THEN REAL_ARITH_TAC] THEN
    CONV_TAC CONTRAPOS_CONV THEN
    DISCH_THEN (MP_TAC o REWRITE_RULE [lemma]) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"N:num") (X_CHOOSE_TAC (← q r"i:num->real"))) THEN
    MP_TAC (← SPECL [← q r"i:num->real", ← q r"N:num", ← q r"\x. poly t x = &0"] FINITE_LEMMA) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"a:real")) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"abs(a) + &1")) THEN
    REWRITE_TAC [REAL_ENTIRE, DE_MORGAN_THM] THEN CONJ_TAC THENL
     [REAL_ARITH_TAC,
      DISCH_THEN (MP_TAC o MATCH_MP (← ASSUME (← q r"!x. (poly t x = &0) ==> x < a"))) THEN
      REAL_ARITH_TAC]))

  let POLY_ZERO ← prove
   r"!p. (poly p = poly []) <=> ALL (\c. c = &0) p"
   (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL] THEN EQ_TAC THENL
     [DISCH_THEN (MP_TAC o MATCH_MP POLY_ZERO_LEMMA) THEN ASM_REWRITE_TAC [],
      POP_ASSUM (SUBST1_TAC o SYM) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [FUN_EQ_THM, poly] THEN REAL_ARITH_TAC])

  -- @@RETURN BEGIN
  return { POLY_ZERO_LEMMA, POLY_ZERO }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Useful triviality.                                                        -/
/- ------------------------------------------------------------------------- -/

structure Trivial where
  -- @@FIELDS
  POLY_DIFF_AUX_ISZERO : thm
  POLY_DIFF_ISZERO : thm
  POLY_DIFF_ZERO : thm
  POLY_DIFF_WELLDEF : thm
  deriving Inhabited

@[nospecialize]
def setupTrivial [HolBase] (D : PolyDeps) (BDefs : Defs) (BConsequences : Consequences) (BDerivs : Derivs) (BZero : Zero) :
    ExceptT String IO Trivial := do
  -- @@SCOPE BEGIN
  let { LIST_INDUCT_TAC, REAL_ARITH, REAL_ARITH_TAC, num_CONV, .. } := D
  let { ALL, FUN_EQ_THM, NOT_CONS_NIL, NOT_SUC, REAL_ENTIRE, .. } := D.core1
  let { REAL_MUL_RZERO, REAL_OF_NUM_EQ, TL, .. } := D.core2
  let { POLY_DIFF_CLAUSES, poly, poly_diff, poly_diff_aux, .. } := BDefs
  let { POLY_ADD, POLY_NEG, .. } := BConsequences
  let { POLY_DIFF_ADD, POLY_DIFF_NEG, .. } := BDerivs
  let { POLY_ZERO, .. } := BZero
  -- @@SCOPE END

  let POLY_DIFF_AUX_ISZERO ← prove
   r"!p n. ALL (\c. c = &0) (poly_diff_aux (SUC n) p) <=>
           ALL (\c. c = &0) p"
   (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC
     [ALL, poly_diff_aux, REAL_ENTIRE, REAL_OF_NUM_EQ, NOT_SUC])

  let POLY_DIFF_ISZERO ← prove
   r"!p. (poly (diff p) = poly []) ==> ?h. poly p = poly [h]"
   (← do
    let n1 ← num_CONV (← q "1")
    pure (REWRITE_TAC [POLY_ZERO] THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [POLY_DIFF_CLAUSES, ALL] THENL
     [EXISTS_TAC (← q r"&0") THEN REWRITE_TAC [FUN_EQ_THM, poly] THEN REAL_ARITH_TAC,
      REWRITE_TAC [n1, POLY_DIFF_AUX_ISZERO] THEN
      REWRITE_TAC [← GSYM POLY_ZERO] THEN DISCH_TAC THEN
      EXISTS_TAC (← q r"h:real") THEN ASM_REWRITE_TAC [poly, FUN_EQ_THM]]))

  let POLY_DIFF_ZERO ← prove
   r"!p. (poly p = poly []) ==> (poly (diff p) = poly [])"
   (REWRITE_TAC [POLY_ZERO] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [poly_diff, NOT_CONS_NIL] THEN
    REWRITE_TAC [ALL, TL] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    SPEC_TAC (← q r"1", ← q r"n:num") THEN POP_ASSUM_LIST (K ALL_TAC) THEN
    SPEC_TAC (← q r"t:real list", ← q r"t:real list") THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [ALL, poly_diff_aux] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [REAL_MUL_RZERO] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [])

  let POLY_DIFF_WELLDEF ← prove
   r"!p q. (poly p = poly q) ==> (poly (diff p) = poly (diff q))"
   (← do
    let r2 ← REAL_ARITH (← q r"(a + --b = &0) <=> (a = b)")
    let r1 ← REAL_ARITH (← q r"a + --a = &0")
    pure (REPEAT STRIP_TAC THEN MP_TAC (← SPEC (← q r"p ++ neg(q)") POLY_DIFF_ZERO) THEN
    REWRITE_TAC [FUN_EQ_THM, POLY_DIFF_ADD, POLY_DIFF_NEG, POLY_ADD] THEN
    ASM_REWRITE_TAC [POLY_NEG, poly, r1] THEN
    REWRITE_TAC [r2]))

  -- @@RETURN BEGIN
  return { POLY_DIFF_AUX_ISZERO, POLY_DIFF_ISZERO, POLY_DIFF_ZERO, POLY_DIFF_WELLDEF }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Basics of divisibility.                                                   -/
/- ------------------------------------------------------------------------- -/

structure Divides where
  -- @@FIELDS
  divides : thm
  POLY_PRIMES : thm
  POLY_DIVIDES_REFL : thm
  POLY_DIVIDES_TRANS : thm
  POLY_DIVIDES_EXP : thm
  POLY_EXP_DIVIDES : thm
  POLY_DIVIDES_ADD : thm
  POLY_DIVIDES_SUB : thm
  POLY_DIVIDES_SUB2 : thm
  POLY_DIVIDES_ZERO : thm
  deriving Inhabited

@[nospecialize]
def setupDivides [HolBase] (D : PolyDeps) (BDefs : Defs) (BConsequences : Consequences) (BDerivs : Derivs) :
    ExceptT String IO Divides := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, MESON_TAC, REAL_ARITH_TAC, new_definition, .. } := D
  let { ADD_CLAUSES, FUN_EQ_THM, LE_EXISTS, REAL_ADD_LDISTRIB, REAL_ADD_RID,
        REAL_ENTIRE, .. } := D.core1
  let { REAL_MUL_ASSOC, REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RNEG, REAL_MUL_RZERO,
        REAL_NEG_NEG, REAL_SUB_REFL, real_sub, .. } := D.core2
  let { poly, poly_exp, .. } := BDefs
  let { POLY_ADD, POLY_MUL, POLY_NEG, .. } := BConsequences
  let { POLY_LINEAR_DIVIDES, .. } := BDerivs
  -- @@SCOPE END

  let divides ← new_definition
   r"p1 divides p2 <=> ?q. poly p2 = poly (p1 ** q)"

  let POLY_PRIMES ← prove
   r"!a p q. [a; &1] divides (p ** q) <=>
            [a; &1] divides p \/ [a; &1] divides q"
   (REPEAT GEN_TAC THEN REWRITE_TAC [divides, POLY_MUL, FUN_EQ_THM, poly] THEN
    REWRITE_TAC [REAL_MUL_RZERO, REAL_ADD_RID, REAL_MUL_RID] THEN EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q r"r:real list") (MP_TAC o SPEC (← q r"--a"))) THEN
      REWRITE_TAC [REAL_ENTIRE, ← GSYM real_sub, REAL_SUB_REFL, REAL_MUL_LZERO] THEN
      DISCH_THEN DISJ_CASES_TAC THENL [DISJ1_TAC, DISJ2_TAC] THEN
      (POP_ASSUM (MP_TAC o REWRITE_RULE [POLY_LINEAR_DIVIDES]) THEN
       REWRITE_TAC [REAL_NEG_NEG] THEN
       DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC
          (X_CHOOSE_THEN (← q r"s:real list") SUBST_ALL_TAC)) THENL
        [EXISTS_TAC (← q r"[]:real list") THEN REWRITE_TAC [poly, REAL_MUL_RZERO],
         EXISTS_TAC (← q r"s:real list") THEN GEN_TAC THEN
         REWRITE_TAC [POLY_MUL, poly] THEN REAL_ARITH_TAC]),
      DISCH_THEN (DISJ_CASES_THEN (X_CHOOSE_TAC (← q r"s:real list"))) THEN
      ASM_REWRITE_TAC [] THENL
       [EXISTS_TAC (← q r"s ** q"), EXISTS_TAC (← q r"p ** s")] THEN
      GEN_TAC THEN REWRITE_TAC [POLY_MUL] THEN REAL_ARITH_TAC])

  let POLY_DIVIDES_REFL ← prove
   r"!p. p divides p"
   (GEN_TAC THEN REWRITE_TAC [divides] THEN EXISTS_TAC (← q r"[&1]") THEN
    REWRITE_TAC [FUN_EQ_THM, POLY_MUL, poly] THEN REAL_ARITH_TAC)

  let POLY_DIVIDES_TRANS ← prove
   r"!p q r. p divides q /\ q divides r ==> p divides r"
   (REPEAT GEN_TAC THEN REWRITE_TAC [divides] THEN
    DISCH_THEN (CONJUNCTS_THEN MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"s:real list") ASSUME_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"t:real list") ASSUME_TAC) THEN
    EXISTS_TAC (← q r"t ** s") THEN
    ASM_REWRITE_TAC [FUN_EQ_THM, POLY_MUL, REAL_MUL_ASSOC])

  let POLY_DIVIDES_EXP ← prove
   r"!p m n. m <= n ==> (p exp m) divides (p exp n)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [LE_EXISTS] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:num") SUBST1_TAC) THEN
    SPEC_TAC (← q r"d:num", ← q r"d:num") THEN INDUCT_TAC THEN
    REWRITE_TAC [ADD_CLAUSES, POLY_DIVIDES_REFL] THEN
    MATCH_MP_TAC POLY_DIVIDES_TRANS THEN
    EXISTS_TAC (← q r"p exp (m + d)") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [divides] THEN EXISTS_TAC (← q r"p:real list") THEN
    REWRITE_TAC [poly_exp, FUN_EQ_THM, POLY_MUL] THEN
    REAL_ARITH_TAC)

  let POLY_EXP_DIVIDES ← prove
   r"!p q m n. (p exp n) divides q /\ m <= n ==> (p exp m) divides q"
   (MESON_TAC [POLY_DIVIDES_TRANS, POLY_DIVIDES_EXP])

  let POLY_DIVIDES_ADD ← prove
   r"!p q r. p divides q /\ p divides r ==> p divides (q ++ r)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [divides] THEN
    DISCH_THEN (CONJUNCTS_THEN MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"s:real list") ASSUME_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"t:real list") ASSUME_TAC) THEN
    EXISTS_TAC (← q r"t ++ s") THEN
    ASM_REWRITE_TAC [FUN_EQ_THM, POLY_ADD, POLY_MUL] THEN
    REAL_ARITH_TAC)

  let POLY_DIVIDES_SUB ← prove
   r"!p q r. p divides q /\ p divides (q ++ r) ==> p divides r"
   (REPEAT GEN_TAC THEN REWRITE_TAC [divides] THEN
    DISCH_THEN (CONJUNCTS_THEN MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"s:real list") ASSUME_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"t:real list") ASSUME_TAC) THEN
    EXISTS_TAC (← q r"s ++ neg(t)") THEN
    POP_ASSUM_LIST (MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC [FUN_EQ_THM, POLY_ADD, POLY_MUL, POLY_NEG] THEN
    DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THEN
    REWRITE_TAC [REAL_ADD_LDISTRIB, REAL_MUL_RNEG] THEN
    ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC)

  let POLY_DIVIDES_SUB2 ← prove
   r"!p q r. p divides r /\ p divides (q ++ r) ==> p divides q"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC POLY_DIVIDES_SUB THEN
    EXISTS_TAC (← q r"r:real list") THEN ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC (← q r"p divides (q ++ r)") THEN
    REWRITE_TAC [divides, POLY_ADD, FUN_EQ_THM, POLY_MUL] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"s:real list")) THEN
    EXISTS_TAC (← q r"s:real list") THEN
    X_GEN_TAC (← q r"x:real") THEN POP_ASSUM (MP_TAC o SPEC (← q r"x:real")) THEN
    REAL_ARITH_TAC)

  let POLY_DIVIDES_ZERO ← prove
   r"!p q. (poly p = poly []) ==> q divides p"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [divides] THEN
    EXISTS_TAC (← q r"[]:real list") THEN
    ASM_REWRITE_TAC [FUN_EQ_THM, POLY_MUL, poly, REAL_MUL_RZERO])

  -- @@RETURN BEGIN
  return { divides, POLY_PRIMES, POLY_DIVIDES_REFL, POLY_DIVIDES_TRANS, POLY_DIVIDES_EXP,
           POLY_EXP_DIVIDES, POLY_DIVIDES_ADD, POLY_DIVIDES_SUB, POLY_DIVIDES_SUB2,
           POLY_DIVIDES_ZERO }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Order of a root, its definition, and composition properties.             -/
/- (poly.ml 745-1010)                                                        -/
/- ------------------------------------------------------------------------- -/

structure Order where
  -- @@FIELDS
  POLY_ORDER_EXISTS : thm
  POLY_ORDER : thm
  order : thm
  ORDER : thm
  ORDER_THM : thm
  ORDER_UNIQUE : thm
  ORDER_POLY : thm
  ORDER_ROOT : thm
  ORDER_DIVIDES : thm
  ORDER_DECOMP : thm
  ORDER_MUL : thm
  ORDER_DIFF : thm
  deriving Inhabited

@[nospecialize]
def setupOrder [HolBase] (D : PolyDeps) (BDefs : Defs) (BConsequences : Consequences) (BDerivs : Derivs) (BEntire : Entire) (BTrivial : Trivial) (BDivides : Divides) :
    ExceptT String IO Order := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, REAL_ARITH_TAC, new_definition,
        prove_recursive_functions_exist, .. } := D
  let { DE_MORGAN_THM, FUN_EQ_THM, LENGTH_EQ_NIL, LE_SUC_LT, LT_CASES, NOT_LE, NOT_SUC,
        REAL_EQ_MUL_LCANCEL, .. } := D.core1
  let { REAL_MUL_AC, REAL_MUL_ASSOC, REAL_MUL_RID, REAL_MUL_RINV, REAL_MUL_RZERO,
        REAL_MUL_SYM, REAL_OF_NUM_EQ, SELECT_UNIQUE, SUC_INJ, num_RECURSION, .. } := D.core2
  let { poly, poly_exp, .. } := BDefs
  let { POLY_ADD, POLY_CMUL, POLY_MUL, POLY_NEG, .. } := BConsequences
  let { POLY_DIFF_EXP_PRIME, POLY_DIFF_MUL, POLY_EXP_ADD, POLY_LENGTH_MUL,
        POLY_LINEAR_DIVIDES, POLY_MUL_ASSOC, .. } := BDerivs
  let { POLY_ENTIRE, POLY_EXP_PRIME_EQ_0, POLY_MUL_LCANCEL, .. } := BEntire
  let { POLY_DIFF_WELLDEF, POLY_DIFF_ZERO, .. } := BTrivial
  let { POLY_EXP_DIVIDES, POLY_PRIMES, divides, .. } := BDivides
  -- @@SCOPE END

  /- (* At last, we can consider the order of a root. *) -/

  let POLY_ORDER_EXISTS ← prove
   r"!a d. !p. (LENGTH p = d) /\ ~(poly p = poly [])
             ==> ?n. ([--a; &1] exp n) divides p /\
                     ~(([--a; &1] exp (SUC n)) divides p)"
   (← do
    let pt ← q
      r"(!p q. mulexp 0 p q = q) /\
     (!p q n. mulexp (SUC n) p q = p ** (mulexp n p q))"
    pure (GEN_TAC THEN
    (fun g => tactic_of (do
       pure (STRIP_ASSUME_TAC (← prove_recursive_functions_exist num_RECURSION pt))) g)
      THEN
    SUBGOAL_THEN
     (← q r"!d. !p. (LENGTH p = d) /\ ~(poly p = poly [])
           ==> ?n q. (p = mulexp (n:num) [--a; &1] q) /\
                     ~(poly q a = &0)")
    MP_TAC THENL
     [INDUCT_TAC THENL
       [REWRITE_TAC [LENGTH_EQ_NIL] THEN MESON_TAC [], ALL_TAC] THEN
      X_GEN_TAC (← q r"p:real list") THEN
      ASM_CASES_TAC (← q r"poly p a = &0") THENL
       [STRIP_TAC THEN UNDISCH_TAC (← q r"poly p a = &0") THEN
        DISCH_THEN (MP_TAC o REWRITE_RULE [POLY_LINEAR_DIVIDES]) THEN
        DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"q:real list") SUBST_ALL_TAC) THEN
        UNDISCH_TAC
         (← q r"!p. (LENGTH p = d) /\ ~(poly p = poly [])
              ==> ?n q. (p = mulexp (n:num) [--a; &1] q) /\
                        ~(poly q a = &0)") THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"q:real list")) THEN
        RULE_ASSUM_TAC (REWRITE_RULE [POLY_LENGTH_MUL, POLY_ENTIRE,
          DE_MORGAN_THM, SUC_INJ]) THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"n:num")
         (X_CHOOSE_THEN (← q r"s:real list") STRIP_ASSUME_TAC)) THEN
        EXISTS_TAC (← q r"SUC n") THEN EXISTS_TAC (← q r"s:real list") THEN
        ASM_REWRITE_TAC [],
        STRIP_TAC THEN EXISTS_TAC (← q r"0") THEN EXISTS_TAC (← q r"p:real list") THEN
        ASM_REWRITE_TAC []],
      DISCH_TAC THEN REPEAT GEN_TAC THEN
      DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"n:num")
         (X_CHOOSE_THEN (← q r"s:real list") STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC (← q r"n:num") THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [divides] THEN CONJ_TAC THENL
       [EXISTS_TAC (← q r"s:real list") THEN
        SPEC_TAC (← q r"n:num", ← q r"n:num") THEN INDUCT_TAC THEN
        ASM_REWRITE_TAC [poly_exp, FUN_EQ_THM, POLY_MUL, poly] THEN
        REAL_ARITH_TAC,
        DISCH_THEN (X_CHOOSE_THEN (← q r"r:real list") MP_TAC) THEN
        SPEC_TAC (← q r"n:num", ← q r"n:num") THEN INDUCT_TAC THEN
        ASM_REWRITE_TAC [] THENL
         [UNDISCH_TAC (← q r"~(poly s a = &0)") THEN CONV_TAC CONTRAPOS_CONV THEN
          REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
          REWRITE_TAC [poly, poly_exp, POLY_MUL] THEN REAL_ARITH_TAC,
          REWRITE_TAC [] THEN ONCE_ASM_REWRITE_TAC [] THEN
          ONCE_REWRITE_TAC [poly_exp] THEN
          REWRITE_TAC [← GSYM POLY_MUL_ASSOC, POLY_MUL_LCANCEL] THEN
          REWRITE_TAC [DE_MORGAN_THM] THEN CONJ_TAC THENL
           [REWRITE_TAC [FUN_EQ_THM] THEN
            DISCH_THEN (MP_TAC o SPEC (← q r"a + &1")) THEN
            REWRITE_TAC [poly] THEN REAL_ARITH_TAC,
            DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN REWRITE_TAC []]]]]))

  let POLY_ORDER ← prove
   r"!p a. ~(poly p = poly [])
         ==> ?!n. ([--a; &1] exp n) divides p /\
                      ~(([--a; &1] exp (SUC n)) divides p)"
   (MESON_TAC [POLY_ORDER_EXISTS, POLY_EXP_DIVIDES, LE_SUC_LT, LT_CASES])

  /- (* Definition of order. *) -/

  let order ← new_definition
   r"order a p = @n. ([--a; &1] exp n) divides p /\
                   ~(([--a; &1] exp (SUC n)) divides p)"

  let ORDER ← prove
   r"!p a n. ([--a; &1] exp n) divides p /\
           ~(([--a; &1] exp (SUC n)) divides p) <=>
           (n = order a p) /\
           ~(poly p = poly [])"
   (REPEAT GEN_TAC THEN REWRITE_TAC [order] THEN
    EQ_TAC THEN STRIP_TAC THENL
     [SUBGOAL_THEN (← q r"~(poly p = poly [])") ASSUME_TAC THENL
       [FIRST_ASSUM (undischCheck (fun c => pure (is_neg c))) THEN
        CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [divides] THEN
        DISCH_THEN SUBST1_TAC THEN EXISTS_TAC (← q r"[]:real list") THEN
        REWRITE_TAC [FUN_EQ_THM, POLY_MUL, poly, REAL_MUL_RZERO],
        ASM_REWRITE_TAC [] THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC []],
      ONCE_ASM_REWRITE_TAC [] THEN CONV_TAC SELECT_CONV] THEN
    ASM_MESON_TAC [POLY_ORDER])

  let ORDER_THM ← prove
   r"!p a. ~(poly p = poly [])
         ==> ([--a; &1] exp (order a p)) divides p /\
             ~(([--a; &1] exp (SUC(order a p))) divides p)"
   (MESON_TAC [ORDER])

  let ORDER_UNIQUE ← prove
   r"!p a n. ~(poly p = poly []) /\
           ([--a; &1] exp n) divides p /\
           ~(([--a; &1] exp (SUC n)) divides p)
           ==> (n = order a p)"
   (MESON_TAC [ORDER])

  let ORDER_POLY ← prove
   r"!p q a. (poly p = poly q) ==> (order a p = order a q)"
   (REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [order, divides, FUN_EQ_THM, POLY_MUL])

  let ORDER_ROOT ← prove
   r"!p a. (poly p a = &0) <=> (poly p = poly []) \/ ~(order a p = 0)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"poly p = poly []") THEN
    ASM_REWRITE_TAC [poly] THEN EQ_TAC THENL
     [DISCH_THEN (MP_TAC o REWRITE_RULE [POLY_LINEAR_DIVIDES]) THEN
      ASM_CASES_TAC (← q r"p:real list = []") THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"q:real list") SUBST_ALL_TAC) THEN DISCH_TAC THEN
      FIRST_ASSUM (MP_TAC o SPEC (← q r"a:real") o MATCH_MP ORDER_THM) THEN
      ASM_REWRITE_TAC [poly_exp, DE_MORGAN_THM] THEN DISJ2_TAC THEN
      REWRITE_TAC [divides] THEN EXISTS_TAC (← q r"q:real list") THEN
      REWRITE_TAC [FUN_EQ_THM, POLY_MUL, poly] THEN REAL_ARITH_TAC,
      DISCH_TAC THEN
      FIRST_ASSUM (MP_TAC o SPEC (← q r"a:real") o MATCH_MP ORDER_THM) THEN
      UNDISCH_TAC (← q r"~(order a p = 0)") THEN
      SPEC_TAC (← q r"order a p", ← q r"n:num") THEN
      INDUCT_TAC THEN ASM_REWRITE_TAC [poly_exp, NOT_SUC] THEN
      DISCH_THEN (MP_TAC o CONJUNCT1) THEN REWRITE_TAC [divides] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"s:real list") SUBST1_TAC) THEN
      REWRITE_TAC [POLY_MUL, poly] THEN REAL_ARITH_TAC])

  let ORDER_DIVIDES ← prove
   r"!p a n. ([--a; &1] exp n) divides p <=>
           (poly p = poly []) \/ n <= order a p"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"poly p = poly []") THEN
    ASM_REWRITE_TAC [] THENL
     [ASM_REWRITE_TAC [divides] THEN EXISTS_TAC (← q r"[]:real list") THEN
      REWRITE_TAC [FUN_EQ_THM, POLY_MUL, poly, REAL_MUL_RZERO],
      ASM_MESON_TAC [ORDER_THM, POLY_EXP_DIVIDES, NOT_LE, LE_SUC_LT]])

  let ORDER_DECOMP ← prove
   r"!p a. ~(poly p = poly [])
         ==> ?q. (poly p = poly (([--a; &1] exp (order a p)) ** q)) /\
                 ~([--a; &1] divides q)"
   (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o MATCH_MP ORDER_THM) THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC o SPEC (← q r"a:real")) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"q:real list") o REWRITE_RULE [divides]) THEN
    EXISTS_TAC (← q r"q:real list") THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"r: real list") o REWRITE_RULE [divides]) THEN
    UNDISCH_TAC (← q r"~([-- a; &1] exp SUC (order a p) divides p)") THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [divides] THEN
    EXISTS_TAC (← q r"r:real list") THEN
    ASM_REWRITE_TAC [POLY_MUL, FUN_EQ_THM, poly_exp] THEN
    REAL_ARITH_TAC)

  /- (* Important composition properties of orders. *) -/

  let ORDER_MUL ← prove
   r"!a p q. ~(poly (p ** q) = poly []) ==>
           (order a (p ** q) = order a p + order a q)"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (fun th => ASSUME_TAC th THEN MP_TAC th) THEN
    REWRITE_TAC [POLY_ENTIRE, DE_MORGAN_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(order a p + order a q = order a (p ** q)) /\
                ~(poly (p ** q) = poly [])")
    MP_TAC THENL [ALL_TAC, MESON_TAC []] THEN
    REWRITE_TAC [← GSYM ORDER] THEN CONJ_TAC THENL
     [MP_TAC (← CONJUNCT1 (← SPEC (← q r"a:real")
        (← MATCH_MP ORDER_THM (← ASSUME (← q r"~(poly p = poly [])"))))) THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"r: real list") o REWRITE_RULE [divides]) THEN
      MP_TAC (← CONJUNCT1 (← SPEC (← q r"a:real")
        (← MATCH_MP ORDER_THM (← ASSUME (← q r"~(poly q = poly [])"))))) THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"s: real list") o REWRITE_RULE [divides]) THEN
      REWRITE_TAC [divides, FUN_EQ_THM] THEN EXISTS_TAC (← q r"s ** r") THEN
      ASM_REWRITE_TAC [POLY_MUL, POLY_EXP_ADD] THEN REAL_ARITH_TAC,
      X_CHOOSE_THEN (← q r"r: real list") STRIP_ASSUME_TAC
      (← SPEC (← q r"a:real") (← MATCH_MP ORDER_DECOMP (← ASSUME (← q r"~(poly p = poly [])")))) THEN
      X_CHOOSE_THEN (← q r"s: real list") STRIP_ASSUME_TAC
      (← SPEC (← q r"a:real") (← MATCH_MP ORDER_DECOMP (← ASSUME (← q r"~(poly q = poly [])")))) THEN
      ASM_REWRITE_TAC [divides, FUN_EQ_THM, POLY_EXP_ADD, POLY_MUL, poly_exp] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"t:real list") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"[--a; &1] divides (r ** s)") MP_TAC THENL
       [ALL_TAC, ASM_REWRITE_TAC [POLY_PRIMES]] THEN
      REWRITE_TAC [divides] THEN EXISTS_TAC (← q r"t:real list") THEN
      SUBGOAL_THEN (← q r"poly ([-- a; &1] exp (order a p) ** r ** s) =
                  poly ([-- a; &1] exp (order a p) ** ([-- a; &1] ** t))")
      MP_TAC THENL
       [ALL_TAC, MESON_TAC [POLY_MUL_LCANCEL, POLY_EXP_PRIME_EQ_0]] THEN
      SUBGOAL_THEN (← q r"poly ([-- a; &1] exp (order a q) **
                        [-- a; &1] exp (order a p) ** r ** s) =
                  poly ([-- a; &1] exp (order a q) **
                        [-- a; &1] exp (order a p) **
                        [-- a; &1] ** t)")
      MP_TAC THENL
       [ALL_TAC, MESON_TAC [POLY_MUL_LCANCEL, POLY_EXP_PRIME_EQ_0]] THEN
      REWRITE_TAC [FUN_EQ_THM, POLY_MUL, POLY_ADD] THEN
      FIRST_ASSUM (undischCheck (fun c => pure (is_forall c))) THEN
      REWRITE_TAC [REAL_MUL_AC]])

  let ORDER_DIFF ← prove
   r"!p a. ~(poly (diff p) = poly []) /\
         ~(order a p = 0)
         ==> (order a p = SUC (order a (diff p)))"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    SUBGOAL_THEN (← q r"~(poly p = poly [])") MP_TAC THENL
     [ASM_MESON_TAC [POLY_DIFF_ZERO], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"q:real list") MP_TAC o
      SPEC (← q r"a:real") o MATCH_MP ORDER_DECOMP) THEN
    SPEC_TAC (← q r"order a p", ← q r"n:num") THEN
    INDUCT_TAC THEN REWRITE_TAC [NOT_SUC, SUC_INJ] THEN
    STRIP_TAC THEN MATCH_MP_TAC ORDER_UNIQUE THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"!r. r divides (diff p) <=>
                    r divides (diff ([-- a; &1] exp SUC n ** q))")
    (fun th => REWRITE_TAC [th]) THENL
     [GEN_TAC THEN REWRITE_TAC [divides] THEN
      FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP POLY_DIFF_WELLDEF th])),
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [divides, FUN_EQ_THM] THEN
      EXISTS_TAC (← q r"[--a; &1] ** (diff q) ++ &(SUC n) ## q") THEN
      REWRITE_TAC [POLY_DIFF_MUL, POLY_DIFF_EXP_PRIME,
        POLY_ADD, POLY_MUL, POLY_CMUL] THEN
      REWRITE_TAC [poly_exp, POLY_MUL] THEN REAL_ARITH_TAC,
      REWRITE_TAC [FUN_EQ_THM, divides, POLY_DIFF_MUL, POLY_DIFF_EXP_PRIME,
        POLY_ADD, POLY_MUL, POLY_CMUL] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"r:real list") ASSUME_TAC) THEN
      UNDISCH_TAC (← q r"~([-- a; &1] divides q)") THEN
      REWRITE_TAC [divides] THEN
      EXISTS_TAC (← q r"inv(&(SUC n)) ## (r ++ neg(diff q))") THEN
      SUBGOAL_THEN
          (← q r"poly ([--a; &1] exp n ** q) =
         poly ([--a; &1] exp n ** ([-- a; &1] ** (inv (&(SUC n)) ##
                                   (r ++ neg (diff q)))))")
      MP_TAC THENL
       [ALL_TAC, MESON_TAC [POLY_MUL_LCANCEL, POLY_EXP_PRIME_EQ_0]] THEN
      REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"x:real") THEN
      SUBGOAL_THEN
          (← q r"!a b. (&(SUC n) * a = &(SUC n) * b) ==> (a = b)")
      MATCH_MP_TAC THENL
       [REWRITE_TAC [REAL_EQ_MUL_LCANCEL, REAL_OF_NUM_EQ, NOT_SUC], ALL_TAC] THEN
      REWRITE_TAC [POLY_MUL, POLY_CMUL] THEN
      SUBGOAL_THEN (← q r"!a b c. &(SUC n) * a * b * inv(&(SUC n)) * c =
                          a * b * c")
      (fun th => REWRITE_TAC [th]) THENL
        [REPEAT GEN_TAC THEN
         GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
         REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
         AP_TERM_TAC THEN
         GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
         GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_RID] THEN
         REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
         MATCH_MP_TAC REAL_MUL_RINV THEN
         REWRITE_TAC [REAL_OF_NUM_EQ, NOT_SUC], ALL_TAC] THEN
      FIRST_ASSUM (MP_TAC o SPEC (← q r"x:real")) THEN
      REWRITE_TAC [poly_exp, POLY_MUL, POLY_ADD, POLY_NEG] THEN
      REAL_ARITH_TAC])

  -- @@RETURN BEGIN
  return { POLY_ORDER_EXISTS, POLY_ORDER, order, ORDER, ORDER_THM, ORDER_UNIQUE,
           ORDER_POLY, ORDER_ROOT, ORDER_DIVIDES, ORDER_DECOMP, ORDER_MUL, ORDER_DIFF }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Now justify the standard squarefree decomposition, i.e. f / gcd(f,f').    -/
/- Define being "squarefree" --- NB with respect to real roots only.         -/
/- Standard squarefree criterion and rephasing of squarefree decomposition.  -/
/- (poly.ml 1011-1143)                                                       -/
/- ------------------------------------------------------------------------- -/

structure Squarefree where
  -- @@FIELDS
  POLY_SQUAREFREE_DECOMP_ORDER : thm
  rsquarefree : thm
  RSQUAREFREE_ROOTS : thm
  RSQUAREFREE_DECOMP : thm
  POLY_SQUAREFREE_DECOMP : thm
  deriving Inhabited

@[nospecialize]
def setupSquarefree [HolBase] (D : PolyDeps) (BDefs : Defs) (BConsequences : Consequences) (BDerivs : Derivs) (BEntire : Entire) (BTrivial : Trivial) (BDivides : Divides) (BOrder : Order) :
    ExceptT String IO Squarefree := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, MESON_TAC, REAL_ARITH_TAC, new_definition, num_CONV, .. } := D
  let { ARITH, DE_MORGAN_THM, EQ_TRANS, FUN_EQ_THM, LE_REFL, NOT_FORALL_THM, PRE,
        REAL_ADD_RID, .. } := D.core1
  let { REAL_MUL_RZERO, SUC_INJ, .. } := D.core2
  let { poly, poly_exp, .. } := BDefs
  let { POLY_ADD, POLY_MUL, .. } := BConsequences
  let { POLY_LINEAR_DIVIDES, .. } := BDerivs
  let { POLY_ENTIRE, .. } := BEntire
  let { POLY_DIFF_ISZERO, POLY_DIFF_ZERO, .. } := BTrivial
  let { divides, .. } := BDivides
  let { ORDER_DECOMP, ORDER_DIFF, ORDER_DIVIDES, ORDER_MUL, ORDER_POLY, ORDER_ROOT, .. } := BOrder
  -- @@SCOPE END

  let POLY_SQUAREFREE_DECOMP_ORDER ← prove
   r"!p q d e r s.
        ~(poly (diff p) = poly []) /\
        (poly p = poly (q ** d)) /\
        (poly (diff p) = poly (e ** d)) /\
        (poly d = poly (r ** p ++ s ** diff p))
        ==> !a. order a q = (if order a p = 0 then 0 else 1)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"order a p = order a q + order a d") MP_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"order a (q ** d)") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC ORDER_POLY THEN ASM_REWRITE_TAC [],
        MATCH_MP_TAC ORDER_MUL THEN
        FIRST_ASSUM (fun th => tactic_of do
          pure (GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [← SYM th])) THEN
        ASM_MESON_TAC [POLY_DIFF_ZERO]], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"order a p = 0") THEN ASM_REWRITE_TAC [] THENL
     [ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN (← q r"order a (diff p) =
                  order a e + order a d") MP_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"order a (e ** d)") THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC [ORDER_POLY], ASM_MESON_TAC [ORDER_MUL]], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~(poly p = poly [])") ASSUME_TAC THENL
     [ASM_MESON_TAC [POLY_DIFF_ZERO], ALL_TAC] THEN
    MP_TAC (← SPECL [← q r"p:real list", ← q r"a:real"] ORDER_DIFF) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th => tactic_of do pure (MP_TAC th THEN MP_TAC (← AP_TERM (← q r"PRE") th))) THEN
    REWRITE_TAC [PRE] THEN DISCH_THEN (ASSUME_TAC o SYM) THEN
    SUBGOAL_THEN (← q r"order a (diff p) <= order a d") MP_TAC THENL
     [SUBGOAL_THEN (← q r"([--a; &1] exp (order a (diff p))) divides d")
      MP_TAC THENL [ALL_TAC, ASM_MESON_TAC [POLY_ENTIRE, ORDER_DIVIDES]] THEN
      SUBGOAL_THEN
        (← q r"([--a; &1] exp (order a (diff p))) divides p /\
         ([--a; &1] exp (order a (diff p))) divides (diff p)")
      MP_TAC THENL
       [REWRITE_TAC [ORDER_DIVIDES, LE_REFL] THEN DISJ2_TAC THEN
        REWRITE_TAC [← ASSUME (← q r"order a (diff p) = PRE (order a p)")] THEN
        ARITH_TAC,
        DISCH_THEN (CONJUNCTS_THEN MP_TAC) THEN REWRITE_TAC [divides] THEN
        REWRITE_TAC [← ASSUME (← q r"poly d = poly (r ** p ++ s ** diff p)")] THEN
        POP_ASSUM_LIST (K ALL_TAC) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"f:real list") ASSUME_TAC) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"g:real list") ASSUME_TAC) THEN
        EXISTS_TAC (← q r"r ** g ++ s ** f") THEN ASM_REWRITE_TAC [] THEN
        ASM_REWRITE_TAC [FUN_EQ_THM, POLY_MUL, POLY_ADD] THEN ARITH_TAC],
      ARITH_TAC])

  /- --------------------------------------------------------------------- -/
  /- Define being "squarefree" --- NB with respect to real roots only.     -/
  /- --------------------------------------------------------------------- -/

  let rsquarefree ← new_definition
   r"rsquarefree p <=> ~(poly p = poly []) /\
                       !a. (order a p = 0) \/ (order a p = 1)"

  /- --------------------------------------------------------------------- -/
  /- Standard squarefree criterion and rephasing of squarefree decomp.     -/
  /- --------------------------------------------------------------------- -/

  let RSQUAREFREE_ROOTS ← prove
   r"!p. rsquarefree p <=> !a. ~((poly p a = &0) /\ (poly (diff p) a = &0))"
   (← do
    let n1 ← ExceptT.mk (num_CONV (← q r"1"))
    pure (GEN_TAC THEN REWRITE_TAC [rsquarefree] THEN
    ASM_CASES_TAC (← q r"poly p = poly []") THEN ASM_REWRITE_TAC [] THENL
     [FIRST_ASSUM (SUBST1_TAC o MATCH_MP POLY_DIFF_ZERO) THEN
      ASM_REWRITE_TAC [poly, NOT_FORALL_THM],
      ASM_CASES_TAC (← q r"poly(diff p) = poly []") THEN ASM_REWRITE_TAC [] THENL
       [FIRST_ASSUM (X_CHOOSE_THEN (← q r"h:real") MP_TAC o
          MATCH_MP POLY_DIFF_ISZERO) THEN
        DISCH_THEN (fun th => ASSUME_TAC th THEN MP_TAC th) THEN
        DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP ORDER_POLY th])) THEN
        UNDISCH_TAC (← q r"~(poly p = poly [])") THEN ASM_REWRITE_TAC [poly] THEN
        REWRITE_TAC [FUN_EQ_THM, poly, REAL_MUL_RZERO, REAL_ADD_RID] THEN
        DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
        X_GEN_TAC (← q r"a:real") THEN DISJ1_TAC THEN
        MP_TAC (← SPECL [← q r"[h:real]", ← q r"a:real"] ORDER_ROOT) THEN
        ASM_REWRITE_TAC [FUN_EQ_THM, poly, REAL_MUL_RZERO, REAL_ADD_RID],
        ASM_REWRITE_TAC [ORDER_ROOT, DE_MORGAN_THM, n1] THEN
        ASM_MESON_TAC [ORDER_DIFF, SUC_INJ]]]))

  let RSQUAREFREE_DECOMP ← prove
   r"!p a. rsquarefree p /\ (poly p a = &0)
           ==> ?q. (poly p = poly ([--a; &1] ** q)) /\
                   ~(poly q a = &0)"
   (← do
    let n1 ← ExceptT.mk (num_CONV (← q r"1"))
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [rsquarefree] THEN STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP ORDER_DECOMP) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"q:real list") MP_TAC o SPEC (← q r"a:real")) THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [ORDER_ROOT]) THEN
    FIRST_ASSUM (DISJ_CASES_TAC o SPEC (← q r"a:real")) THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [ARITH] THEN
    DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    EXISTS_TAC (← q r"q:real list") THEN CONJ_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, POLY_MUL] THEN GEN_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [n1] THEN
      REWRITE_TAC [poly_exp, POLY_MUL] THEN
      REWRITE_TAC [poly] THEN REAL_ARITH_TAC,
      DISCH_TAC THEN UNDISCH_TAC (← q r"~([-- a; &1] divides q)") THEN
      REWRITE_TAC [divides] THEN
      UNDISCH_TAC (← q r"poly q a = &0") THEN
      GEN_REWRITE_TAC LAND_CONV [POLY_LINEAR_DIVIDES] THEN
      ASM_CASES_TAC (← q r"q:real list = []") THEN ASM_REWRITE_TAC [] THENL
       [EXISTS_TAC (← q r"[] : real list") THEN REWRITE_TAC [FUN_EQ_THM] THEN
        REWRITE_TAC [POLY_MUL, poly, REAL_MUL_RZERO],
        MESON_TAC []]]))

  let POLY_SQUAREFREE_DECOMP ← prove
   r"!p q d e r s.
        ~(poly (diff p) = poly []) /\
        (poly p = poly (q ** d)) /\
        (poly (diff p) = poly (e ** d)) /\
        (poly d = poly (r ** p ++ s ** diff p))
        ==> rsquarefree q /\ (!a. (poly q a = &0) <=> (poly p a = &0))"
   (REPEAT GEN_TAC THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC th THEN
      ASSUME_TAC (← MATCH_MP POLY_SQUAREFREE_DECOMP_ORDER th))) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    SUBGOAL_THEN (← q r"~(poly p = poly [])") ASSUME_TAC THENL
     [ASM_MESON_TAC [POLY_DIFF_ZERO], ALL_TAC] THEN
    DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN
    UNDISCH_TAC (← q r"~(poly p = poly [])") THEN
    DISCH_THEN (fun th => MP_TAC th THEN MP_TAC th) THEN
    DISCH_THEN (fun th => ASM_REWRITE_TAC [] THEN ASSUME_TAC th) THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [POLY_ENTIRE, DE_MORGAN_THM] THEN STRIP_TAC THEN
    UNDISCH_TAC (← q r"poly p = poly (q ** d)") THEN
    DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC [rsquarefree, ORDER_ROOT] THEN
    CONJ_TAC THEN GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [ARITH])

  -- @@RETURN BEGIN
  return { POLY_SQUAREFREE_DECOMP_ORDER, rsquarefree, RSQUAREFREE_ROOTS,
           RSQUAREFREE_DECOMP, POLY_SQUAREFREE_DECOMP }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Normalization of a polynomial, degree, finiteness of roots, crude bound.  -/
/- (poly.ml 1145-1216)                                                       -/
/- ------------------------------------------------------------------------- -/

structure Normalize where
  -- @@FIELDS
  normalize : thm
  POLY_NORMALIZE : thm
  degree : thm
  DEGREE_ZERO : thm
  POLY_ROOTS_FINITE_SET : thm
  POLY_MONO : thm
  deriving Inhabited

@[nospecialize]
def setupNormalize [HolBase] (D : PolyDeps) (BDefs : Defs) (BRootsFinite : RootsFinite) (BZero : Zero) :
    ExceptT String IO Normalize := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, LIST_INDUCT_TAC, MESON_TAC, new_definition,
        new_recursive_definition, .. } := D
  let { ALL, EXTENSION, FINITE_RULES, FINITE_SUBSET, FUN_EQ_THM, IN_ELIM_THM,
        IN_INSERT, LENGTH, LT, MAP, NOT_IN_EMPTY, PRE, REAL_ABS_0, REAL_ABS_MUL,
        REAL_ABS_POS, REAL_ABS_TRIANGLE, REAL_ADD_LID, REAL_LE_LADD, REAL_LE_MUL2,
        REAL_LE_REFL, REAL_LE_TRANS, .. } := D.core1
  let { REAL_MUL_RZERO, RIGHT_FORALL_IMP_THM, SUBSET, list_RECURSION, .. } := D.core2
  let { poly, .. } := BDefs
  let { POLY_ROOTS_FINITE, .. } := BRootsFinite
  let { POLY_ZERO, .. } := BZero
  -- @@SCOPE END

  let normalize ← new_recursive_definition list_RECURSION
   r"(normalize [] = []) /\
     (normalize (CONS h t) =
        if normalize t = [] then if h = &0 then [] else [h]
                            else CONS h (normalize t))"

  let POLY_NORMALIZE ← prove
   r"!p. poly (normalize p) = poly p"
   (LIST_INDUCT_TAC THEN REWRITE_TAC [normalize, poly] THEN
    ASM_CASES_TAC (← q r"h = &0") THEN ASM_REWRITE_TAC [] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [poly, FUN_EQ_THM] THEN
    UNDISCH_TAC (← q r"poly (normalize t) = poly t") THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [poly] THEN
    REWRITE_TAC [REAL_MUL_RZERO, REAL_ADD_LID])

  /- --------------------------------------------------------------------- -/
  /- The degree of a polynomial.                                           -/
  /- --------------------------------------------------------------------- -/

  let degree ← new_definition
   r"degree p = PRE(LENGTH(normalize p))"

  let DEGREE_ZERO ← prove
   r"!p. (poly p = poly []) ==> (degree p = 0)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [degree] THEN
    SUBGOAL_THEN (← q r"normalize p = []") SUBST1_TAC THENL
     [POP_ASSUM MP_TAC THEN SPEC_TAC (← q r"p:real list", ← q r"p:real list") THEN
      REWRITE_TAC [POLY_ZERO] THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [normalize, ALL] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"normalize t = []") (fun th => REWRITE_TAC [th]) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [LENGTH, PRE]])

  /- --------------------------------------------------------------------- -/
  /- Tidier versions of finiteness of roots.                               -/
  /- --------------------------------------------------------------------- -/

  let POLY_ROOTS_FINITE_SET ← prove
   r"!p. ~(poly p = poly []) ==> FINITE { x | poly p x = &0}"
   (GEN_TAC THEN REWRITE_TAC [POLY_ROOTS_FINITE] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"N:num") MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"i:num->real") ASSUME_TAC) THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC (← q r"{x:real | ?n:num. n < N /\ (x = i n)}") THEN
    CONJ_TAC THENL
     [SPEC_TAC (← q r"N:num", ← q r"N:num") THEN POP_ASSUM_LIST (K ALL_TAC) THEN
      INDUCT_TAC THENL
       [SUBGOAL_THEN (← q r"{x:real | ?n. n < 0 /\ (x = i n)} = {}")
        (fun th => REWRITE_TAC [th, FINITE_RULES]) THEN
        REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY, LT],
        SUBGOAL_THEN (← q r"{x:real | ?n. n < SUC N /\ (x = i n)} =
                      (i N) INSERT {x:real | ?n. n < N /\ (x = i n)}")
        SUBST1_TAC THENL
         [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT, LT] THEN MESON_TAC [],
          MATCH_MP_TAC (← CONJUNCT2 FINITE_RULES) THEN ASM_REWRITE_TAC []]],
      ASM_REWRITE_TAC [SUBSET, IN_ELIM_THM]])

  /- --------------------------------------------------------------------- -/
  /- Crude bound for polynomial.                                           -/
  /- --------------------------------------------------------------------- -/

  let POLY_MONO ← prove
   r"!x k p. abs(x) <= k ==> abs(poly p x) <= poly (MAP abs p) k"
   (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    DISCH_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [poly, REAL_LE_REFL, MAP, REAL_ABS_0] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"abs(h) + abs(x * poly t x)") THEN
    REWRITE_TAC [REAL_ABS_TRIANGLE, REAL_LE_LADD] THEN
    REWRITE_TAC [REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC [REAL_ABS_POS])

  -- @@RETURN BEGIN
  return { normalize, POLY_NORMALIZE, degree, DEGREE_ZERO, POLY_ROOTS_FINITE_SET,
           POLY_MONO }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Conversions to perform operations if coefficients are rational constants. -/
/- (poly.ml 1218-1287)                                                       -/
/- ------------------------------------------------------------------------- -/

structure Convs where
  -- @@FIELDS
  POLY_DIFF_CONV : term → ExceptT String IO thm
  POLY_CMUL_CONV : term → ExceptT String IO thm
  POLY_ADD_CONV : term → ExceptT String IO thm
  POLY_MUL_CONV : term → ExceptT String IO thm
  POLY_NORMALIZE_CONV : term → ExceptT String IO thm
  deriving Inhabited

/-- poly.ml's `POLY_DIFF_AUX_CONV`, the inner `let rec` of `POLY_DIFF_CONV`. -/
partial def loc_POLY_DIFF_AUX_CONV (aux_conv0 aux_conv1 REAL_RAT_MUL_CONV NUM_SUC_CONV : ioconv) :
    ioconv := fun tm =>
 (aux_conv0 ORELSEC
  (aux_conv1 THENC
   LAND_CONV REAL_RAT_MUL_CONV THENC
   RAND_CONV (LAND_CONV NUM_SUC_CONV THENC
              loc_POLY_DIFF_AUX_CONV aux_conv0 aux_conv1 REAL_RAT_MUL_CONV NUM_SUC_CONV))) tm

/-- poly.ml's `POLY_CMUL_CONV` (the inner `let rec`). -/
partial def loc_POLY_CMUL_CONV (cmul_conv0 cmul_conv1 REAL_RAT_MUL_CONV : ioconv) :
    ioconv := fun tm =>
 (cmul_conv0 ORELSEC
  (cmul_conv1 THENC
   LAND_CONV REAL_RAT_MUL_CONV THENC
   RAND_CONV (loc_POLY_CMUL_CONV cmul_conv0 cmul_conv1 REAL_RAT_MUL_CONV))) tm

/-- poly.ml's `POLY_ADD_CONV` (the inner `let rec`). -/
partial def loc_POLY_ADD_CONV (add_conv0 add_conv1 REAL_RAT_ADD_CONV : ioconv) :
    ioconv := fun tm =>
 (add_conv0 ORELSEC
  (add_conv1 THENC
   LAND_CONV REAL_RAT_ADD_CONV THENC
   RAND_CONV (loc_POLY_ADD_CONV add_conv0 add_conv1 REAL_RAT_ADD_CONV))) tm

/-- poly.ml's `POLY_MUL_CONV` (the inner `let rec`); it reuses `POLY_CMUL_CONV`
    and `POLY_ADD_CONV` passed in as `cmul`, `add`. -/
partial def loc_POLY_MUL_CONV (mul_conv0 mul_conv1 mul_conv2 cmul add : ioconv) :
    ioconv := fun tm =>
 (mul_conv0 ORELSEC
  (mul_conv1 THENC cmul) ORELSEC
  (mul_conv2 THENC
   LAND_CONV cmul THENC
   RAND_CONV (RAND_CONV (loc_POLY_MUL_CONV mul_conv0 mul_conv1 mul_conv2 cmul add)) THENC
   add)) tm

/-- poly.ml's `POLY_NORMALIZE_CONV` (the inner `let rec`). -/
partial def loc_POLY_NORMALIZE_CONV
    (norm_conv0 norm_conv1 norm_conv2 REAL_RAT_EQ_CONV : ioconv) : ioconv := fun tm =>
 (norm_conv0 ORELSEC
  (norm_conv1 THENC
   RAND_CONV (loc_POLY_NORMALIZE_CONV norm_conv0 norm_conv1 norm_conv2 REAL_RAT_EQ_CONV) THENC
   BETA_CONV THENC
   RATOR_CONV (RAND_CONV (RATOR_CONV (LAND_CONV REAL_RAT_EQ_CONV))) THENC
   norm_conv2)) tm

@[nospecialize]
def setupConvs [HolBase] (D : PolyDeps) (BDefs : Defs) (BNormalize : Normalize) :
    ExceptT String IO Convs := do
  -- @@SCOPE BEGIN
  let { NUM_SUC_CONV, REAL_RAT_ADD_CONV, REAL_RAT_EQ_CONV, REAL_RAT_MUL_CONV, .. } := D
  let { COND_CLAUSES, EQ_REFL, NOT_CONS_NIL, .. } := D.core1
  let { POLY_ADD_CLAUSES, POLY_DIFF_CLAUSES, POLY_MUL_CLAUSES, poly_cmul,
        poly_diff_aux, .. } := BDefs
  let { normalize, .. } := BNormalize
  -- @@SCOPE END

  let POLY_DIFF_CONV : term → ExceptT String IO thm ← do
    let aux_conv0 ← GEN_REWRITE_CONV_NET id [← CONJUNCT1 poly_diff_aux]
    let aux_conv1 ← GEN_REWRITE_CONV_NET id [← CONJUNCT2 poly_diff_aux]
    let diff_conv0 ← GEN_REWRITE_CONV_NET id (← liftExcept (butlast (CONJUNCTS POLY_DIFF_CLAUSES)))
    let diff_conv1 ← GEN_REWRITE_CONV_NET id [← liftExcept (last (CONJUNCTS POLY_DIFF_CLAUSES))]
    let POLY_DIFF_AUX_CONV := loc_POLY_DIFF_AUX_CONV aux_conv0 aux_conv1 REAL_RAT_MUL_CONV NUM_SUC_CONV
    pure (fun tm => ExceptT.mk ((diff_conv0 ORELSEC
      (diff_conv1 THENC POLY_DIFF_AUX_CONV)) tm))

  -- the inner conversions of POLY_CMUL_CONV / POLY_ADD_CONV, as `ioconv`, so
  -- that POLY_MUL_CONV below can compose them exactly as poly.ml does.
  let loc_cmul_conv0 ← GEN_REWRITE_CONV_NET id [← CONJUNCT1 poly_cmul]
  let loc_cmul_conv1 ← GEN_REWRITE_CONV_NET id [← CONJUNCT2 poly_cmul]
  let loc_cmul := loc_POLY_CMUL_CONV loc_cmul_conv0 loc_cmul_conv1 REAL_RAT_MUL_CONV
  let POLY_CMUL_CONV : term → ExceptT String IO thm ←
    pure (fun tm => ExceptT.mk (loc_cmul tm))

  let loc_add_conv0 ← GEN_REWRITE_CONV_NET id (← liftExcept (butlast (CONJUNCTS POLY_ADD_CLAUSES)))
  let loc_add_conv1 ← GEN_REWRITE_CONV_NET id [← liftExcept (last (CONJUNCTS POLY_ADD_CLAUSES))]
  let loc_add := loc_POLY_ADD_CONV loc_add_conv0 loc_add_conv1 REAL_RAT_ADD_CONV
  let POLY_ADD_CONV : term → ExceptT String IO thm ←
    pure (fun tm => ExceptT.mk (loc_add tm))

  let POLY_MUL_CONV : term → ExceptT String IO thm ← do
    let mul_conv0 ← GEN_REWRITE_CONV_NET id [← CONJUNCT1 POLY_MUL_CLAUSES]
    let mul_conv1 ← GEN_REWRITE_CONV_NET id [← CONJUNCT1 (← CONJUNCT2 POLY_MUL_CLAUSES)]
    let mul_conv2 ← GEN_REWRITE_CONV_NET id [← CONJUNCT2 (← CONJUNCT2 POLY_MUL_CLAUSES)]
    let POLY_MUL_CONV := loc_POLY_MUL_CONV mul_conv0 mul_conv1 mul_conv2 loc_cmul loc_add
    pure (fun tm => ExceptT.mk (POLY_MUL_CONV tm))

  let POLY_NORMALIZE_CONV : term → ExceptT String IO thm ← do
    let pth ← prove
     r"normalize (CONS h t) =
        (\n. if n = [] then if h = &0 then [] else [h] else CONS h n)
        (normalize t)"
     (REWRITE_TAC [normalize])
    let norm_conv0 ← GEN_REWRITE_CONV_NET id [← CONJUNCT1 normalize]
    let norm_conv1 ← GEN_REWRITE_CONV_NET id [pth]
    let norm_conv2 ← GEN_REWRITE_CONV_NET DEPTH_CONV
     [COND_CLAUSES, NOT_CONS_NIL, ← EQT_INTRO (← SPEC_ALL EQ_REFL)]
    let POLY_NORMALIZE_CONV :=
      loc_POLY_NORMALIZE_CONV norm_conv0 norm_conv1 norm_conv2 REAL_RAT_EQ_CONV
    pure (fun tm => ExceptT.mk (POLY_NORMALIZE_CONV tm))

  -- @@RETURN BEGIN
  return { POLY_DIFF_CONV, POLY_CMUL_CONV, POLY_ADD_CONV, POLY_MUL_CONV,
           POLY_NORMALIZE_CONV }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Some theorems asserting that operations give non-nil results, and some    -/
/- general lemmas.                                                           -/
/- ------------------------------------------------------------------------- -/

structure NonNil where
  -- @@FIELDS
  NOT_POLY_CMUL_NIL : thm
  NOT_POLY_MUL_NIL : thm
  NOT_POLY_EXP_NIL : thm
  NOT_POLY_EXP_X_NIL : thm
  POLY_CMUL_LID : thm
  POLY_MUL_LID : thm
  POLY_MUL_RID : thm
  POLY_ADD_SYM : thm
  POLY_ADD_ASSOC : thm
  deriving Inhabited

@[nospecialize]
def setupNonNil [HolBase] (D : PolyDeps) (BDefs : Defs) :
    ExceptT String IO NonNil := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, LIST_INDUCT_TAC, REAL_ARITH, SIMP_RULE, .. } := D
  let { HD, NOT_CONS_NIL, REAL_ADD_ASSOC, REAL_ADD_SYM, .. } := D.core1
  let { TL, .. } := D.core2
  let { POLY_ADD_CLAUSES, poly_add, poly_cmul, poly_exp, poly_mul, .. } := BDefs
  -- @@SCOPE END

  let NOT_POLY_CMUL_NIL ← prove
   r"!h p. ~(p = []) ==> ~((h ## p) = [])"
   (STRIP_TAC THEN LIST_INDUCT_TAC THENL
     [SIMP_TAC [], SIMP_TAC [poly_cmul, NOT_CONS_NIL]])

  let NOT_POLY_MUL_NIL ← prove
   r"!p1 p2. ~(p1 = []) /\ ~(p2 = []) ==> ~((p1 ** p2) = [])"
   (LIST_INDUCT_TAC THENL
     [SIMP_TAC [],
      LIST_INDUCT_TAC THENL
       [SIMP_TAC [],
        SIMP_TAC [poly_mul, NOT_CONS_NIL] THEN
        SPEC_TAC (← q r"t:(real)list", ← q r"t:(real)list") THEN LIST_INDUCT_TAC THENL
         [SIMP_TAC [poly_cmul, NOT_CONS_NIL],
          SIMP_TAC [poly_cmul, poly_add, NOT_CONS_NIL]]]])

  let NOT_POLY_EXP_NIL ← prove
   r"!n p . ~(p = []) ==> ~((poly_exp p n) = [])"
   (← do
    let lem001 ← ASSUME (← q r"!p . ~(p = []) ==> ~(poly_exp p n = [])")
    let lem002 ← SIMP_RULE [NOT_CONS_NIL] (← SPEC (← q r"CONS (h:real) t") lem001)
    pure (INDUCT_TAC THENL
     [SIMP_TAC [poly_exp, NOT_CONS_NIL],
      LIST_INDUCT_TAC THENL
       [SIMP_TAC [],
        SIMP_TAC [lem002, NOT_POLY_MUL_NIL, poly_exp, NOT_CONS_NIL]]]))

  let NOT_POLY_EXP_X_NIL ← prove
   r"!n. ~((poly_exp [&0;&1] n) = [])"
   (← do
    let lem01 ← prove
     r"~([&0;&1] = [])"
     (SIMP_TAC [NOT_CONS_NIL])
    pure (INDUCT_TAC THENL
     [SIMP_TAC [poly_exp, NOT_CONS_NIL],
      ASM_SIMP_TAC [poly_exp, NOT_POLY_MUL_NIL, lem01]]))

  /- --------------------------------------------------------------------- -/
  /- Some general lemmas.                                                  -/
  /- --------------------------------------------------------------------- -/

  let POLY_CMUL_LID ← prove
   r"!p. &1 ## p = p"
   (← do
    let r1 ← REAL_ARITH (← q r"&1 * h = h")
    pure (LIST_INDUCT_TAC THENL
     [SIMP_TAC [poly_cmul],
      ASM_SIMP_TAC [poly_cmul] THEN SIMP_TAC [r1]]))

  let POLY_MUL_LID ← prove
   r"!p. [&1] ** p = p"
   (LIST_INDUCT_TAC THENL
     [SIMP_TAC [poly_mul, poly_cmul],
      ONCE_REWRITE_TAC [poly_mul] THEN SIMP_TAC [POLY_CMUL_LID]])

  let POLY_MUL_RID ← prove
   r"!p. p ** [&1] = p"
   (← do
    let r2 ← REAL_ARITH (← q r"h * (real_of_num 1) = h")
    let r1 ← REAL_ARITH (← q r"h + (real_of_num 0) = h")
    pure (LIST_INDUCT_TAC THENL
     [SIMP_TAC [poly_mul],
      ASM_CASES_TAC (← q r"t:(real)list = []") THEN
      ASM_SIMP_TAC [poly_mul, poly_cmul, poly_add, NOT_CONS_NIL, HD, TL,
       r1, r2]]))

  let POLY_ADD_SYM ← prove
   r"!x y . x ++ y = y ++ x"
   (← do
    let lem1 ← ASSUME (← q r"!y . t ++ y = y ++ t")
    let lem2 ← SPEC (← q r"t':(real)list") lem1
    pure (LIST_INDUCT_TAC THENL
     [LIST_INDUCT_TAC THENL [SIMP_TAC [poly_add], SIMP_TAC [poly_add]],
      LIST_INDUCT_TAC THENL
        [SIMP_TAC [poly_add],
         SIMP_TAC [POLY_ADD_CLAUSES] THEN
         ONCE_REWRITE_TAC [lem2] THEN
         SIMP_TAC [← SPECL [← q r"h:real", ← q r"h':real"] REAL_ADD_SYM]]]))

  let POLY_ADD_ASSOC ← prove
   r"!x y z . x ++ (y ++ z) = (x ++ y) ++ z"
   (← do
    let lem1 ← ASSUME (← q r"!y z. t ++ y ++ z = (t ++ y) ++ z")
    let lem2 ← SPECL [← q r"t':(real)list", ← q r"t'':(real)list"] lem1
    pure (LIST_INDUCT_TAC THENL
     [SIMP_TAC [POLY_ADD_CLAUSES],
      LIST_INDUCT_TAC THENL
       [SIMP_TAC [POLY_ADD_CLAUSES],
        LIST_INDUCT_TAC THENL
        [SIMP_TAC [POLY_ADD_CLAUSES],
         SIMP_TAC [POLY_ADD_CLAUSES] THEN
         SIMP_TAC [REAL_ADD_ASSOC] THEN
         SIMP_TAC [lem2]]]]))

  -- @@RETURN BEGIN
  return { NOT_POLY_CMUL_NIL, NOT_POLY_MUL_NIL, NOT_POLY_EXP_NIL, NOT_POLY_EXP_X_NIL,
           POLY_CMUL_LID, POLY_MUL_LID, POLY_MUL_RID, POLY_ADD_SYM, POLY_ADD_ASSOC }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Heads and tails resulting from operations.                                -/
/- ------------------------------------------------------------------------- -/

structure HeadsTails where
  -- @@FIELDS
  TL_POLY_MUL_X : thm
  HD_POLY_MUL_X : thm
  TL_POLY_EXP_X_SUC : thm
  HD_POLY_EXP_X_SUC : thm
  HD_POLY_ADD : thm
  HD_POLY_CMUL : thm
  TL_POLY_CMUL : thm
  HD_POLY_MUL : thm
  HD_POLY_EXP : thm
  deriving Inhabited

@[nospecialize]
def setupHeadsTails [HolBase] (D : PolyDeps) (BDefs : Defs) (BNonNil : NonNil) :
    ExceptT String IO HeadsTails := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, LIST_INDUCT_TAC, REAL_ARITH, REAL_ARITH_TAC, .. } := D
  let { HD, NOT_CONS_NIL, .. } := D.core1
  let { TL, pow, .. } := D.core2
  let { poly_add, poly_cmul, poly_exp, poly_mul, .. } := BDefs
  let { NOT_POLY_CMUL_NIL, NOT_POLY_EXP_NIL, POLY_MUL_LID, .. } := BNonNil
  -- @@SCOPE END

  let TL_POLY_MUL_X ← prove
   r"!p. TL ([&0;&1] ** p) = p"
   (← do
    let r1 ← REAL_ARITH (← q r"(&0) * h + h' = h'")
    pure (LIST_INDUCT_TAC THENL
     [ONCE_REWRITE_TAC [poly_mul] THEN
      SIMP_TAC [NOT_CONS_NIL, poly_cmul, poly_add, TL, poly_mul],
      ONCE_REWRITE_TAC [poly_mul] THEN SIMP_TAC [NOT_CONS_NIL] THEN
      ONCE_REWRITE_TAC [poly_cmul] THEN ONCE_REWRITE_TAC [poly_add] THEN
      SIMP_TAC [NOT_CONS_NIL] THEN SIMP_TAC [TL, POLY_MUL_LID] THEN
      SPEC_TAC (← q r"h:real", ← q r"h:real") THEN
      SPEC_TAC (← q r"t:(real)list", ← q r"t:(real)list") THEN
      LIST_INDUCT_TAC THENL
       [SIMP_TAC [poly_cmul, poly_add],
        ASM_SIMP_TAC [poly_cmul, poly_add, NOT_CONS_NIL, HD, TL, r1]]]))

  let HD_POLY_MUL_X ← prove
   r"!p. HD ([&0;&1] ** p) = &0"
   (← do
    let r1 ← REAL_ARITH (← q r"&0 * h + &0 = &0")
    pure (LIST_INDUCT_TAC THEN
    SIMP_TAC [poly_mul, NOT_CONS_NIL, poly_cmul, poly_add, HD, r1]))

  let TL_POLY_EXP_X_SUC ← prove
   r"!n . TL (poly_exp [&0;&1] (SUC n)) = poly_exp [&0;&1] n"
   (SIMP_TAC [poly_exp, TL_POLY_MUL_X])

  let HD_POLY_EXP_X_SUC ← prove
   r"!n . HD (poly_exp [&0;&1] (SUC n)) = &0"
   (← do
    let r1 ← REAL_ARITH (← q r"&0 * &1 + &0 = &0")
    pure (INDUCT_TAC THENL
     [SIMP_TAC [poly_exp, poly_add, HD, TL, poly_cmul, poly_mul, NOT_CONS_NIL,
               r1],
      SIMP_TAC [poly_exp, HD_POLY_MUL_X]]))

  let HD_POLY_ADD ← prove
   r"!p1 p2. ~(p1 = []) /\ ~(p2 = []) ==> HD (p1 ++ p2) = (HD p1) + (HD p2)"
   (LIST_INDUCT_TAC THENL
     [SIMP_TAC [],
       LIST_INDUCT_TAC THENL
        [SIMP_TAC [],
         SIMP_TAC [NOT_CONS_NIL, poly_add] THEN
         ONCE_REWRITE_TAC [← ISPECL [← q r"h':real", ← q r"t':(real)list"] NOT_CONS_NIL] THEN
         SIMP_TAC [HD]]])

  let HD_POLY_CMUL ← prove
   r"!x p . ~(p = []) ==> HD (x ## p) = x * (HD p)"
   (STRIP_TAC THEN LIST_INDUCT_TAC THENL
     [SIMP_TAC [], SIMP_TAC [NOT_CONS_NIL, poly_cmul, HD]])

  let TL_POLY_CMUL ← prove
   r"!x p . ~(p = []) ==> TL (x ## p) = x ## (TL p)"
   (STRIP_TAC THEN LIST_INDUCT_TAC THENL
     [SIMP_TAC [], SIMP_TAC [NOT_CONS_NIL, poly_cmul, TL]])

  let HD_POLY_MUL ← prove
   r"!p1 p2 . ~(p1 = []) /\ ~(p2 = [])  ==> HD (p1 ** p2) = (HD p1) * (HD p2)"
   (LIST_INDUCT_TAC THENL
     [SIMP_TAC [],
      LIST_INDUCT_TAC THENL
       [SIMP_TAC [],
        SIMP_TAC [NOT_CONS_NIL, poly_mul] THEN
        ASM_CASES_TAC (← q r"(t:(real)list) = []") THENL
         [ASM_SIMP_TAC [poly_cmul, HD],
          ASM_SIMP_TAC [poly_cmul, poly_add, NOT_CONS_NIL, HD] THEN REAL_ARITH_TAC]]])

  let HD_POLY_EXP ← prove
   r"!n p . ~(p = []) ==> HD (poly_exp p n) = (HD p) pow n"
   (INDUCT_TAC THENL
     [SIMP_TAC [poly_exp] THEN LIST_INDUCT_TAC THENL
       [SIMP_TAC [], SIMP_TAC [HD, pow]],
      SIMP_TAC [poly_exp] THEN LIST_INDUCT_TAC THENL
       [SIMP_TAC [],
        SIMP_TAC [HD, ← GSYM pow, NOT_CONS_NIL, poly_mul] THEN
        ASM_CASES_TAC (← q r"(t:(real)list) = []") THENL
         [ASM_SIMP_TAC [HD_POLY_CMUL, NOT_POLY_CMUL_NIL, NOT_POLY_EXP_NIL,
                       NOT_CONS_NIL, HD, ← GSYM pow],
          ASM_SIMP_TAC [NOT_POLY_CMUL_NIL, NOT_POLY_EXP_NIL, NOT_CONS_NIL,
                       HD_POLY_ADD, HD, HD_POLY_CMUL, ← GSYM pow] THEN
          REAL_ARITH_TAC]]])

  -- @@RETURN BEGIN
  return { TL_POLY_MUL_X, HD_POLY_MUL_X, TL_POLY_EXP_X_SUC, HD_POLY_EXP_X_SUC,
           HD_POLY_ADD, HD_POLY_CMUL, TL_POLY_CMUL, HD_POLY_MUL, HD_POLY_EXP }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Additional general lemmas.                                                -/
/- ------------------------------------------------------------------------- -/

structure AdditionalLemmas where
  -- @@FIELDS
  POLY_ADD_IDENT : thm
  POLY_ADD_NEUTRAL : thm
  MONOIDAL_POLY_ADD : thm
  POLY_DIFF_AUX_ADD_LEMMA : thm
  POLYDIFF_ADD : thm
  POLY_DIFF_AUX_POLY_CMUL : thm
  POLY_CMUL_POLY_DIFF : thm
  deriving Inhabited

@[nospecialize]
def setupAdditionalLemmas [HolBase] (D : PolyDeps) (BDefs : Defs) (BNonNil : NonNil) (BHeadsTails : HeadsTails) :
    ExceptT String IO AdditionalLemmas := do
  -- @@SCOPE BEGIN
  let { LIST_INDUCT_TAC, REAL_ARITH, SELECT_ELIM_TAC, SIMP_RULE, .. } := D
  let { NOT_CONS_NIL, .. } := D.core1
  let { TL, monoidal, neutral, .. } := D.core2
  let { POLY_ADD_CLAUSES, poly_add, poly_cmul, poly_diff, poly_diff_aux, .. } := BDefs
  let { POLY_ADD_ASSOC, POLY_ADD_SYM, .. } := BNonNil
  let { TL_POLY_CMUL, .. } := BHeadsTails
  -- @@SCOPE END

  let POLY_ADD_IDENT ← prove
   r"neutral (++) = []"
   (← do
    let l1 ← ASSUME (← q r"!x. (!y. x ++ y = y /\ y ++ x = y)
                     ==> (!y. (CONS h t) ++ y = y /\ y ++ (CONS h t) = y)")
    let l2 ← SPEC (← q r"[]:(real)list") l1
    let l3 ← SIMP_RULE [POLY_ADD_CLAUSES] l2
    let l4 ← SPEC (← q r"[]:(real)list") l3
    let l5 ← CONJUNCT1 l4
    let l6 ← SIMP_RULE [POLY_ADD_CLAUSES, NOT_CONS_NIL] l5
    let l7 ← NOT_INTRO (← DISCH_ALL l6)
    pure (ONCE_REWRITE_TAC [neutral] THEN SELECT_ELIM_TAC THEN LIST_INDUCT_TAC THENL
    [SIMP_TAC [], SIMP_TAC [l7]]))

  let POLY_ADD_NEUTRAL ← prove
   r"!x. neutral (++) ++ x = x"
   (SIMP_TAC [POLY_ADD_IDENT, POLY_ADD_CLAUSES])

  let MONOIDAL_POLY_ADD ← prove
   r"monoidal poly_add"
   (← do
    let lem1 ← CONJ POLY_ADD_SYM (← CONJ POLY_ADD_ASSOC POLY_ADD_NEUTRAL)
    pure (ONCE_REWRITE_TAC [monoidal] THEN ACCEPT_TAC lem1))

  let POLY_DIFF_AUX_ADD_LEMMA ← prove
   r"!t1 t2 n. poly_diff_aux n (t1 ++ t2) =
             (poly_diff_aux n t1) ++ (poly_diff_aux n t2)"
   (← do
    let lem ← REAL_ARITH (← q r"!n h h'. (&n * h) + (&n * h') = &n * (h + h')")
    pure (LIST_INDUCT_TAC THEN SIMP_TAC [POLY_ADD_CLAUSES, poly_diff_aux] THEN
    LIST_INDUCT_TAC THEN SIMP_TAC [POLY_ADD_CLAUSES, poly_diff_aux] THEN
    STRIP_TAC THEN
    ONCE_REWRITE_TAC [POLY_ADD_CLAUSES] THEN
    ONCE_REWRITE_TAC [poly_diff_aux] THEN
    ONCE_REWRITE_TAC [POLY_ADD_CLAUSES] THEN
    ONCE_REWRITE_TAC [lem] THEN
    ASM_SIMP_TAC []))

  let POLYDIFF_ADD ← prove
   r"!p1 p2. (poly_diff (p1 ++ p2)) = (poly_diff p1  ++ poly_diff p2)"
   (← do
    let lem1 ← prove
     r"!h0 t0 h1 t1. ~(((CONS h0 t0) ++ (CONS h1 t1)) = [])"
     (SIMP_TAC [POLY_ADD_CLAUSES, NOT_CONS_NIL])
    let lem2 ← prove
     r"!h0 t0 h1 t1.
          (TL ((CONS h0 t0) ++ (CONS h1 t1))
        = (TL (CONS h0 t0)) ++ (TL (CONS h1 t1)))"
     (REPEAT STRIP_TAC THEN REWRITE_TAC [poly_add] THEN
      ONCE_REWRITE_TAC [NOT_CONS_NIL] THEN REWRITE_TAC [TL]
      THEN SIMP_TAC [])
    pure (REPEAT LIST_INDUCT_TAC THENL
     [SIMP_TAC [poly_add, poly_diff],
      SIMP_TAC [poly_add, poly_diff],
      SIMP_TAC [poly_add, poly_diff, POLY_ADD_CLAUSES],
      SIMP_TAC [poly_diff] THEN
      ONCE_REWRITE_TAC [lem1, NOT_CONS_NIL] THEN
      SIMP_TAC [lem2, POLY_DIFF_AUX_ADD_LEMMA]]))

  let POLY_DIFF_AUX_POLY_CMUL ← prove
   r"!p c n. poly_diff_aux n (c ## p) = c ## (poly_diff_aux n p)"
   (← do
    let r1 ← REAL_ARITH (← q r"(a:real) * b * c = b * a * c")
    let lem01 ← ASSUME
     (← q r"!c n. poly_diff_aux n (c ## t) = c ## poly_diff_aux n t")
    let lem02 ← SPECL [← q r"c:real", ← q r"SUC n"] lem01
    pure (LIST_INDUCT_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
    SIMP_TAC [poly_cmul, poly_diff_aux, lem02, r1]))

  let POLY_CMUL_POLY_DIFF ← prove
   r"!p c. poly_diff (c ## p) = c ## (poly_diff p)"
   (LIST_INDUCT_TAC THEN
    SIMP_TAC [poly_diff, POLY_DIFF_AUX_POLY_CMUL, TL_POLY_CMUL,
             poly_cmul, NOT_CONS_NIL])

  -- @@RETURN BEGIN
  return { POLY_ADD_IDENT, POLY_ADD_NEUTRAL, MONOIDAL_POLY_ADD, POLY_DIFF_AUX_ADD_LEMMA,
           POLYDIFF_ADD, POLY_DIFF_AUX_POLY_CMUL, POLY_CMUL_POLY_DIFF }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Theorems about the lengths of lists from the polynomial operations, the   -/
/- expansion of a polynomial as a power sum, and the end of the file.        -/
/- ------------------------------------------------------------------------- -/

structure Lengths where
  -- @@FIELDS
  POLY_CMUL_LENGTH : thm
  POLY_ADD_LENGTH : thm
  POLY_MUL_LENGTH : thm
  POLY_EXP_X_REC : thm
  POLY_MUL_LENGTH2 : thm
  POLY_EXP_X_LENGTH : thm
  POLY_SUM_EQUIV : thm
  ITERATE_RADD_POLYADD : thm
  deriving Inhabited

@[nospecialize]
def setupLengths [HolBase] (D : PolyDeps) (BDefs : Defs) (BConsequences : Consequences) (BNonNil : NonNil) (BHeadsTails : HeadsTails) (BAdditionalLemmas : AdditionalLemmas) :
    ExceptT String IO Lengths := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, INDUCT_TAC, LIST_INDUCT_TAC, NUMSEG_CONV, REAL_ARITH,
        REAL_ARITH_TAC, reduce_interface, unparse_as_infix, .. } := D
  let { ADD1, CONS_HD_TL, EL, HD, ITERATE_CLAUSES_NUMSEG, LENGTH, LENGTH_EQ_NIL, LE_0,
        MONOIDAL_REAL_ADD, NOT_CONS_NIL, NSUM_LMUL, PRE, .. } := D.core1
  let { REAL_MUL_RID, SUM_COMBINE_R, SUM_LMUL, SUM_OFFSET_0, SUM_SING, TL, real_pow, .. } := D.core2
  let { POLY_CONST, POLY_MUL_CLAUSES, poly, poly_add, poly_cmul, poly_exp, poly_mul, .. } := BDefs
  let { POLY_ADD, .. } := BConsequences
  let { NOT_POLY_EXP_X_NIL, .. } := BNonNil
  let { HD_POLY_EXP_X_SUC, TL_POLY_EXP_X_SUC, .. } := BHeadsTails
  let { MONOIDAL_POLY_ADD, .. } := BAdditionalLemmas
  -- @@SCOPE END

  let POLY_CMUL_LENGTH ← prove
   r"!c p. LENGTH (c ## p) =  LENGTH p"
   (STRIP_TAC THEN LIST_INDUCT_TAC THENL
     [SIMP_TAC [poly_cmul],
      SIMP_TAC [poly_cmul] THEN ASM_SIMP_TAC [LENGTH]])

  let POLY_ADD_LENGTH ← prove
   r"!p q. LENGTH (p ++ q) =  MAX (LENGTH p) (LENGTH q)"
   (← do
    let r3 ← ARITH_RULE (← q r"~(x > y) ==> ~((SUC x) > (SUC y))")
    let r2 ← ARITH_RULE (← q r"x > y ==> (SUC x) > (SUC y)")
    let r1 ← ARITH_RULE (← q r"MAX x y = if (x > y) then x else y")
    pure (LIST_INDUCT_TAC THENL
     [SIMP_TAC [poly_add, LENGTH] THEN ARITH_TAC,
      LIST_INDUCT_TAC THENL
       [SIMP_TAC [poly_add, LENGTH] THEN ARITH_TAC,
        SIMP_TAC [poly_add, LENGTH] THEN
        ONCE_REWRITE_TAC [NOT_CONS_NIL] THEN SIMP_TAC [HD, TL, LENGTH] THEN
        ASM_SIMP_TAC [] THEN
        ONCE_REWRITE_TAC [r1] THEN
        ASM_CASES_TAC (← q r"LENGTH (t:(real)list) > LENGTH (t':(real)list)") THENL
         [ASM_SIMP_TAC [r2],
          ASM_SIMP_TAC [r3]]]]))

  let POLY_MUL_LENGTH ← prove
   r"!p h t. LENGTH (p ** (CONS h t)) >= LENGTH p"
   (← do
    let lemma01 ← ASSUME (← q r"!h t'. LENGTH (t ** CONS h t') >= LENGTH t")
    let lemma02 ← SPECL [← q r"h':real", ← q r"t':(real)list"] lemma01
    let lemma03 ← ONCE_REWRITE_RULE [← ARITH_RULE (← q r"(x:num) >= y <=> SUC x >= SUC y")]
       lemma02
    let lemma05 ← ARITH_RULE (← q r"(y:num) >= z ==> (x + (y - x) >= z) ")
    let lemma06 ← SPECL [← q r"SUC (LENGTH (t ** (CONS (h':real) t')))",
                         ← q r"LENGTH (h ## (CONS h' t'))",
                         ← q r"SUC (LENGTH (t:(real)list))"] (← GEN_ALL lemma05)
    let lemma07 ← MATCH_MP (lemma06) (lemma03)
    let r1 ← ARITH_RULE (← q r"!x y. (MAX x y) = x + (y - x)")
    pure (LIST_INDUCT_TAC THENL
     [SIMP_TAC [POLY_MUL_CLAUSES] THEN ARITH_TAC,
      SIMP_TAC [poly_mul] THEN ASM_CASES_TAC (← q r"(t:(real)list) = []") THENL
       [ASM_SIMP_TAC [POLY_CMUL_LENGTH, LENGTH] THEN ARITH_TAC,
        ASM_SIMP_TAC [POLY_ADD_LENGTH, LENGTH, lemma07, r1]]]))

  let POLY_EXP_X_REC ← prove
   r"!n. poly_exp [&0;&1] (SUC n) = CONS (&0) (poly_exp [&0;&1] n)"
   (← do
    let lem01 ← MATCH_MP CONS_HD_TL (← SPEC (← q r"(SUC n)") NOT_POLY_EXP_X_NIL)
    let lem02 ← ONCE_REWRITE_RULE [HD_POLY_EXP_X_SUC, TL_POLY_EXP_X_SUC] lem01
    pure (ACCEPT_TAC (← GEN_ALL lem02)))

  let POLY_MUL_LENGTH2 ← prove
   r"!q p. ~(q = []) ==> LENGTH (p ** q) >= LENGTH p"
   (LIST_INDUCT_TAC THEN SIMP_TAC [NOT_CONS_NIL, POLY_MUL_LENGTH])

  let POLY_EXP_X_LENGTH ← prove
   r"!n. LENGTH (poly_exp [&0;&1] n) = SUC n"
   (← do
    let r1 ← ARITH_RULE (← q r"(SUC x) = (SUC y) <=> x = y")
    pure (INDUCT_TAC THEN
    ASM_SIMP_TAC [poly_exp, LENGTH, POLY_EXP_X_REC, r1]))

  /- --------------------------------------------------------------------- -/
  /- Expansion of a polynomial as a power sum.                             -/
  /- --------------------------------------------------------------------- -/

  let POLY_SUM_EQUIV ← prove
   r"!p x.
     ~(p = []) ==>
     poly p x = sum (0..(PRE (LENGTH p))) (\i. (EL i p)*(x pow i))"
   (← do
    let lem000 ← ARITH_RULE (← q r"0 <= 0 + 1 /\ 0 <= (LENGTH (t:(real)list))")
    let lem001 ← SPECL
                   [← q r"f:num->real", ← q r"0", ← q r"0", ← q r"LENGTH (t:(real)list)"]
                   SUM_COMBINE_R
    let lem002 ← MP lem001 lem000
    let lem003 ← SPECL
                   [← q r"f:num->real", ← q r"1", ← q r"LENGTH (t:(real)list)"]
                   SUM_OFFSET_0
    let lem004 ← ASSUME (← q r"~((t:(real)list) = [])")
    let lem005 ← ONCE_REWRITE_RULE [← GSYM LENGTH_EQ_NIL] lem004
    let lem006 ← ONCE_REWRITE_RULE [← ARITH_RULE (← q r"~(x = 0) <=> (1 <= x)")] lem005
    let lem007 ← MP lem003 lem006
    let lem017 ← ARITH_RULE (← q r"1 <= (LENGTH (t:(real)list))
                       ==> ((LENGTH t) - 1 = PRE (LENGTH t))")
    let lem018 ← MP lem017 lem006
    let r1 ← ARITH_RULE (← q r"0 + 1 = 1")
    let r2 ← REAL_ARITH (← q r"(A:real) * B * C = B * (A * C)")
    pure (LIST_INDUCT_TAC THENL
      [SIMP_TAC [NOT_CONS_NIL]
            ,
            ASM_CASES_TAC (← q r"(t:(real)list) = []") THENL
       [
            ASM_SIMP_TAC [POLY_CONST, LENGTH, PRE]
       THEN ONCE_REWRITE_TAC [← ExceptT.mk (NUMSEG_CONV (← q r"0..0"))]
       THEN ONCE_REWRITE_TAC [SUM_SING]
       THEN BETA_TAC
       THEN ONCE_REWRITE_TAC [EL]
       THEN ONCE_REWRITE_TAC [HD]
       THEN REAL_ARITH_TAC
       ,
            ASM_SIMP_TAC [POLY_CONST, LENGTH, PRE]
       THEN ONCE_REWRITE_TAC [poly]
       THEN ONCE_REWRITE_TAC [← GSYM lem002]
       THEN ONCE_REWRITE_TAC [r1]
       THEN ONCE_REWRITE_TAC [← ExceptT.mk (NUMSEG_CONV (← q r"0..0"))]
       THEN ONCE_REWRITE_TAC [SUM_SING]
       THEN BETA_TAC
       THEN SIMP_TAC [EL, HD]
       THEN ONCE_REWRITE_TAC [lem007]
       THEN BETA_TAC
       THEN ONCE_REWRITE_TAC [← GSYM ADD1]
       THEN SIMP_TAC [EL, TL]
       THEN ONCE_REWRITE_TAC [real_pow]
       THEN ONCE_REWRITE_TAC [REAL_MUL_RID]
       THEN ONCE_REWRITE_TAC [r2]
       THEN ONCE_REWRITE_TAC [NSUM_LMUL]
       THEN ONCE_REWRITE_TAC [SUM_LMUL]
       THEN ASM_SIMP_TAC []
       THEN SIMP_TAC [NOT_CONS_NIL]
       THEN ONCE_REWRITE_TAC [lem018]
       THEN SIMP_TAC []
      ]]))

  let ITERATE_RADD_POLYADD ← prove
   r"!n x f. iterate (+) (0..n) (\i.poly (f i) x) =
           poly (iterate (++) (0..n) f) x"
   (INDUCT_TAC THEN
    ASM_SIMP_TAC [ITERATE_CLAUSES_NUMSEG, MONOIDAL_REAL_ADD, MONOIDAL_POLY_ADD,
                 LE_0, POLY_ADD])

  /- --------------------------------------------------------------------- -/
  /- Now we're finished with polynomials...                                -/
  /- --------------------------------------------------------------------- -/

  -- `do_list reduce_interface [...]`; faithful `for` loop as in HolMath/RealAx.
  for p in [("divides", r"poly_divides:real list->real list->bool"),
            ("exp", r"poly_exp:real list -> num -> real list"),
            ("diff", r"poly_diff:real list->real list")] do
    reduce_interface p.1 (← q p.2)

  unparse_as_infix "exp"

  -- @@RETURN BEGIN
  return { POLY_CMUL_LENGTH, POLY_ADD_LENGTH, POLY_MUL_LENGTH, POLY_EXP_X_REC,
           POLY_MUL_LENGTH2, POLY_EXP_X_LENGTH, POLY_SUM_EQUIV, ITERATE_RADD_POLYADD }
  -- @@RETURN END

end HolLibrary.Poly
