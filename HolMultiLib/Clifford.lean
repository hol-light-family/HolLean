/- ========================================================================= -/
/- Geometric algebra.                                                        -/
/- ========================================================================= -/
/- File: HolMultiLib/Clifford.lean

  Original (c) Copyright, John Harrison 1998-2008
  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/clifford.ml`, in the style of
  HolMultiLib/Determinants.lean: pure, the proofs translated by hand, one
  `let` per OCaml `let`, in file order.  What clifford.ml uses from the core
  library, from Multivariate/vectors.ml and from Library/binary.ml is passed
  in `CliffordDeps`; SessionMultiLib/Clifford.lean supplies it.

  clifford.ml's `needs` are the wiring's imports.  Its load-time effects
  (`prioritize_real`, the new type `multivector`, the infixes, the `lambdas`
  binder and the `*` overload) are made inside the bundles at their file
  positions.
-/

import HolMath

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs rhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolMultiLib.Clifford

/-- The core theorems clifford.ml uses. -/
structure CoreThms where
  (ADD_SUB2 ARITH ARITH_GE ARITH_GT CARD_CLAUSES CARD_DELETE CARD_EQ_0 CARD_UNION
   CARD_UNION_EQ CART_EQ COND_ID COND_RAND COND_RATOR CONJ_ACI DELETE_INSERT DE_MORGAN_THM
   DIMINDEX_UNIQUE EMPTY_SUBSET EMPTY_UNION EQ_SYM_EQ EQ_TRANS ETA_AX EVEN_ADD EVEN_MULT
   EXISTS_PAIR_THM EXTENSION FINITE_DELETE FINITE_DIFF FINITE_IMAGE FINITE_INDUCT_DELETE
   FINITE_INDUCT_STRONG FINITE_INSERT FINITE_NUMSEG FINITE_POWERSET FINITE_PRODUCT
   FINITE_RULES FINITE_SUBSET FORALL_IN_IMAGE FORALL_PAIR_THM FORALL_SIMP FUN_EQ_THM GT
   HAS_SIZE HAS_SIZE_IMAGE_INJ HAS_SIZE_NUMSEG_1 HAS_SIZE_POWERSET IMAGE_SUBSET IMAGE_o
   IMP_CONJ IMP_IMP INFINITE INTER_ACI INTER_EMPTY IN_DELETE IN_DIFF IN_ELIM_PAIR_THM
   IN_ELIM_THM IN_IMAGE IN_INSERT IN_INTER IN_NUMSEG IN_SING IN_UNION IN_UNIV
   ITERATE_CLAUSES LAMBDA_BETA LET_DEF LET_END_DEF LT_ANTISYM LT_CASES LT_REFL MEASURE
   MEMBER_NOT_EMPTY MINIMAL MONO_EXISTS NOT_INSERT_EMPTY NOT_IN_EMPTY PAIR_EQ PRE
   REAL_MUL_AC REAL_MUL_ASSOC REAL_MUL_LID REAL_MUL_LZERO REAL_MUL_RID REAL_MUL_RZERO
   REAL_POW_ADD REAL_POW_NEG REAL_POW_ONE RIGHT_FORALL_IMP_THM RIGHT_IMP_FORALL_THM
   SELECT_UNIQUE SKOLEM_THM SUBSET SUBSET_REFL SUM_DELTA SUM_EQ SUM_LMUL SUM_RMUL SUM_SWAP
   UNION_ASSOC UNION_EMPTY UNION_SUBSET WF_MEASURE WF_REC minimal monoidal neutral num_WOP
   o_DEF real_pow : thm)
  deriving Inhabited

/-- The vectors.ml theorems clifford.ml uses. -/
structure VecThms where
  (BILINEAR_EQ BILINEAR_LADD BILINEAR_LMUL BILINEAR_LNEG BILINEAR_LZERO BILINEAR_RADD
   BILINEAR_RMUL BILINEAR_RNEG BILINEAR_RZERO COND_COMPONENT LINEAR_EQ SPAN_MUL
   SPAN_SUPERSET SPAN_VSUM VECTOR_ADD_AC VECTOR_ADD_ASSOC VECTOR_ADD_COMPONENT
   VECTOR_ADD_LDISTRIB VECTOR_ADD_LID VECTOR_ADD_RDISTRIB VECTOR_ADD_RID VECTOR_MUL_ASSOC
   VECTOR_MUL_COMPONENT VECTOR_MUL_LID VECTOR_MUL_LZERO VECTOR_MUL_RZERO VECTOR_NEG_0
   VECTOR_NEG_MINUS1 VECTOR_NEG_NEG VECTOR_SUB VEC_COMPONENT VSUM_0 VSUM_ADD VSUM_CLAUSES
   VSUM_DELTA VSUM_EQ VSUM_LMUL bilinear linear vsum : thm)
  deriving Inhabited

/-- The Library/binary.ml theorems clifford.ml uses. -/
structure BinThms where
  (BINARYSUM_BITSET BINARYSUM_BOUND BITSET_BINARYSUM BITSET_BOUND : thm)
  deriving Inhabited

/-- What clifford.ml uses from the core library's procedures and parser. -/
structure CliffordDeps where
  -- definitions and parser state
  new_definition : String → ExceptT String IO thm
  new_type_definition : String → String × String → thm → ExceptT String IO thm
  new_specification : List String → thm → ExceptT String IO thm
  parse_as_infix : String × (Int × String) → IO Unit
  parse_as_binder : String → IO Unit
  overload_interface : String → term → ExceptT String IO Unit
  prioritize_real : IO Unit
  -- decision procedures and rules
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_MESON_TAC : List thm → tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  REAL_ARITH : term → ExceptT String IO thm
  REAL_ARITH_TAC : tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  SIMP_RULE : List thm → thm → ExceptT String IO thm
  DISJ_ACI_RULE : term → ExceptT String IO thm
  LET_TAC : tactic
  -- conversions
  let_CONV : ioconv
  NUM_REDUCE_CONV : ioconv
  REAL_RAT_REDUCE_CONV : ioconv
  REAL_POLY_CONV : ioconv
  PURE_SIMP_CONV : List thm → ioconv
  -- syntax
  dest_setenum : term → Except String (List term)
  mk_setenum : List term × hol_type → ExceptT String IO term
  mk_numeral : Rat → Except String term
  is_numeral : term → Bool
  -- vectors.ml's procedures
  VECTOR_ARITH : term → ExceptT String IO thm
  VECTOR_ARITH_TAC : tactic
  -- theorems
  core : CoreThms
  vec : VecThms
  bin : BinThms

/- ------------------------------------------------------------------------- -/
/- Some basic lemmas, mostly set theory; the index type for "multivectors"   -/
/- (k-vectors for all k <= N).  (clifford.ml 10-99)                          -/
/- ------------------------------------------------------------------------- -/

structure Basics where
  CARD_UNION_LEMMA : thm
  CARD_DIFF_INTER : thm
  CARD_ADD_SYMDIFF_INTER : thm
  SYMDIFF_PARITY_LEMMA : thm
  FINITE_CART_SUBSET_LEMMA : thm
  multivector_tybij_th : thm
  multivector_tybij : thm
  MULTIVECTOR_IMAGE : thm
  HAS_SIZE_MULTIVECTOR : thm
  FINITE_MULTIVECTOR : thm
  DIMINDEX_MULTIVECTOR : thm
  DEST_MK_MULTIVECTOR : thm
  FORALL_MULTIVECTOR : thm
  deriving Inhabited

@[nospecialize]
def setupBasics [HolBase] (D : CliffordDeps) : ExceptT String IO Basics := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON_TAC, SET_TAC, new_type_definition, .. } := D
  let { ARITH, CARD_UNION, CARD_UNION_EQ, DIMINDEX_UNIQUE, EMPTY_SUBSET, EVEN_ADD, EVEN_MULT,
        EXISTS_PAIR_THM, EXTENSION, FINITE_DIFF, FINITE_NUMSEG, FINITE_PRODUCT, FINITE_SUBSET,
        FORALL_PAIR_THM, HAS_SIZE, HAS_SIZE_IMAGE_INJ, HAS_SIZE_NUMSEG_1, HAS_SIZE_POWERSET,
        INTER_ACI, IN_ELIM_PAIR_THM, IN_ELIM_THM, IN_IMAGE, IN_UNIV, SUBSET, .. } := D.core
  -- @@SCOPE END

  D.prioritize_real

  let CARD_UNION_LEMMA ← prove
   r"FINITE s /\ FINITE t /\ FINITE u /\ FINITE v /\
   s INTER t = {} /\ u INTER v = {} /\ s UNION t = u UNION v
   ==> CARD(s) + CARD(t) = CARD(u) + CARD(v)"
   (MESON_TAC [CARD_UNION])

  let CARD_DIFF_INTER ← prove
   r"!s t. FINITE s ==> CARD s = CARD(s DIFF t) + CARD(s INTER t)"
   (REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
    ASM_REWRITE_TAC [] THEN SET_TAC [])

  let CARD_ADD_SYMDIFF_INTER ← prove
   r"!s t:A->bool.
        FINITE s /\ FINITE t
        ==> CARD s + CARD t =
            CARD((s DIFF t) UNION (t DIFF s)) + 2 * CARD(s INTER t)"
   (REPEAT STRIP_TAC THEN
    SUBST1_TAC (← SPEC (← q r"t:A->bool") (← MATCH_MP CARD_DIFF_INTER
     (← ASSUME (← q r"FINITE(s:A->bool)")))) THEN
    SUBST1_TAC (← SPEC (← q r"s:A->bool") (← MATCH_MP CARD_DIFF_INTER
     (← ASSUME (← q r"FINITE(t:A->bool)")))) THEN
    REWRITE_TAC [INTER_ACI] THEN
    MATCH_MP_TAC (← ARITH_RULE (← q r"c = a + b ==> (a + x) + (b + x) = c + 2 * x")) THEN
    MATCH_MP_TAC CARD_UNION THEN ASM_SIMP_TAC [FINITE_DIFF] THEN SET_TAC [])

  let SYMDIFF_PARITY_LEMMA ← prove
   r"!s t u. FINITE s /\ FINITE t /\ (s DIFF t) UNION (t DIFF s) = u
           ==> EVEN(CARD u) = (EVEN(CARD s) <=> EVEN(CARD t))"
   (ONCE_REWRITE_TAC [← GSYM EVEN_ADD] THEN
    SIMP_TAC [CARD_ADD_SYMDIFF_INTER] THEN
    REWRITE_TAC [EVEN_ADD, EVEN_MULT, ARITH])

  let FINITE_CART_SUBSET_LEMMA ← prove
   r"!P m n. FINITE {i,j | i IN 1..m /\ j IN 1..n /\ P i j}"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC (← q r"{i,j | i IN 1..m /\ j IN 1..n}") THEN
    SIMP_TAC [SUBSET, FINITE_PRODUCT, FINITE_NUMSEG] THEN
    SIMP_TAC [FORALL_PAIR_THM, IN_ELIM_PAIR_THM])

  let multivector_tybij_th ← prove
   r"?s. s SUBSET (1..dimindex(:N))"
   (MESON_TAC [EMPTY_SUBSET])

  let multivector_tybij ←
    new_type_definition "multivector" ("mk_multivector", "dest_multivector")
      multivector_tybij_th

  let MULTIVECTOR_IMAGE ← prove
   r"(:(N)multivector) = IMAGE mk_multivector {s | s SUBSET 1..dimindex(:N)}"
   (REWRITE_TAC [EXTENSION, IN_UNIV, IN_IMAGE, IN_ELIM_THM] THEN
    MESON_TAC [multivector_tybij])

  let HAS_SIZE_MULTIVECTOR ← prove
   r"(:(N)multivector) HAS_SIZE (2 EXP dimindex(:N))"
   (REWRITE_TAC [MULTIVECTOR_IMAGE] THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    SIMP_TAC [HAS_SIZE_POWERSET, HAS_SIZE_NUMSEG_1, IN_ELIM_THM] THEN
    MESON_TAC [multivector_tybij])

  let FINITE_MULTIVECTOR ← prove
   r"FINITE(:(N)multivector)"
   (MESON_TAC [HAS_SIZE, HAS_SIZE_MULTIVECTOR])

  let DIMINDEX_MULTIVECTOR ← prove
   r"dimindex(:(N)multivector) = 2 EXP dimindex(:N)"
   (MESON_TAC [DIMINDEX_UNIQUE, HAS_SIZE_MULTIVECTOR])

  let DEST_MK_MULTIVECTOR ← prove
   r"!s. s SUBSET 1..dimindex(:N)
         ==> dest_multivector(mk_multivector s :(N)multivector) = s"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC id [← GSYM multivector_tybij] THEN
    ASM_REWRITE_TAC [])

  let FORALL_MULTIVECTOR ← prove
   r"(!s. s SUBSET 1..dimindex(:N) ==> P(mk_multivector s)) <=>
   (!m:(N)multivector. P m)"
   (EQ_TAC THENL [ALL_TAC, SIMP_TAC []] THEN DISCH_TAC THEN GEN_TAC THEN
    MP_TAC (← ISPEC (← q r"m:(N)multivector")
     (← REWRITE_RULE [EXTENSION] MULTIVECTOR_IMAGE)) THEN
    REWRITE_TAC [IN_UNIV, IN_IMAGE, EXISTS_PAIR_THM, IN_ELIM_THM] THEN
    ASM_MESON_TAC [])

  return { CARD_UNION_LEMMA, CARD_DIFF_INTER, CARD_ADD_SYMDIFF_INTER, SYMDIFF_PARITY_LEMMA,
           FINITE_CART_SUBSET_LEMMA, multivector_tybij_th, multivector_tybij,
           MULTIVECTOR_IMAGE, HAS_SIZE_MULTIVECTOR, FINITE_MULTIVECTOR, DIMINDEX_MULTIVECTOR,
           DEST_MK_MULTIVECTOR, FORALL_MULTIVECTOR }

/- ------------------------------------------------------------------------- -/
/- The bijections we use for indexing; indexing directly via subsets;       -/
/- crucial properties; componentwise operations.  (clifford.ml 108-225)     -/
/- ------------------------------------------------------------------------- -/

structure Indexing where
  setcode : thm
  codeset : thm
  CODESET_SETCODE_BIJECTIONS : thm
  FORALL_SETCODE : thm
  SETCODE_BOUNDS : thm
  sindex : thm
  lambdas : thm
  MULTIVECTOR_EQ : thm
  MULTIVECTOR_BETA : thm
  MULTIVECTOR_UNIQUE : thm
  MULTIVECTOR_ETA : thm
  MULTIVECTOR_ADD_COMPONENT : thm
  MULTIVECTOR_MUL_COMPONENT : thm
  MULTIVECTOR_VEC_COMPONENT : thm
  MULTIVECTOR_VSUM_COMPONENT : thm
  MULTIVECTOR_VSUM : thm
  deriving Inhabited

@[nospecialize]
def setupIndexing [HolBase] (D : CliffordDeps) (BBasics : Basics) :
    ExceptT String IO Indexing := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, MESON_TAC, SET_RULE, new_definition,
        parse_as_binder, parse_as_infix, .. } := D
  let { ADD_SUB2, CART_EQ, EQ_TRANS, EXTENSION, FINITE_IMAGE, FINITE_NUMSEG, FINITE_SUBSET,
        FORALL_IN_IMAGE, IMAGE_SUBSET, IMAGE_o, IN_IMAGE, IN_NUMSEG, LAMBDA_BETA, PRE, SUBSET,
        o_DEF, .. } := D.core
  let { VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, VEC_COMPONENT, vsum, .. } := D.vec
  let { BINARYSUM_BITSET, BINARYSUM_BOUND, BITSET_BINARYSUM, BITSET_BOUND, .. } := D.bin
  let { DIMINDEX_MULTIVECTOR, .. } := BBasics
  -- @@SCOPE END
  let ar (s : String) : ExceptT String IO thm := do ARITH_RULE (← q s)

  let setcode ← new_definition
   r"setcode s = 1 + binarysum (IMAGE PRE s)"

  let codeset ← new_definition
   r"codeset n = IMAGE SUC (bitset(n - 1))"

  let CODESET_SETCODE_BIJECTIONS ← prove
   r"(!i. i IN 1..(2 EXP n)
        ==> codeset i SUBSET 1..n /\ setcode(codeset i) = i) /\
   (!s. s SUBSET (1..n)
        ==> (setcode s) IN 1..(2 EXP n) /\ codeset(setcode s) = s)"
   (REWRITE_TAC [codeset, setcode, ADD_SUB2, ← GSYM IMAGE_o, o_DEF, PRE] THEN
    REWRITE_TAC [← SET_RULE (← q r"IMAGE (\x. x) s = s")] THEN CONJ_TAC THEN GEN_TAC THENL
     [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_NUMSEG] THEN
      SIMP_TAC [← ar r"1 <= i ==> (1 + b = i <=> b = i - 1)"] THEN
      REWRITE_TAC [← ar r"1 <= SUC n /\ SUC n <= k <=> n < k"] THEN
      DISCH_THEN (MP_TAC o MATCH_MP
       (← ar r"1 <= i /\ i <= t ==> i - 1 < t")) THEN
      MESON_TAC [BITSET_BOUND, BINARYSUM_BITSET],
      ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o ISPEC (← q r"PRE") o MATCH_MP IMAGE_SUBSET) THEN
    REWRITE_TAC [IN_NUMSEG, SUBSET] THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC (← ar r"x < n ==> 1 <= 1 + x /\ 1 + x <= n") THEN
      MATCH_MP_TAC BINARYSUM_BOUND THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"i:num")) THEN
      ASM_REWRITE_TAC [IN_IMAGE, IN_NUMSEG] THEN ARITH_TAC,
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"IMAGE SUC (IMAGE PRE s)") THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC [FINITE_IMAGE, FINITE_SUBSET, FINITE_NUMSEG, BITSET_BINARYSUM],
      ALL_TAC] THEN
    UNDISCH_TAC (← q r"s SUBSET 1..n") THEN
    REWRITE_TAC [SUBSET, EXTENSION, IN_IMAGE, IN_NUMSEG] THEN
    MESON_TAC [← ar r"1 <= n ==> SUC(PRE n) = n"])

  let FORALL_SETCODE ← prove
   r"(!s. s SUBSET (1..n) ==> P(setcode s)) <=> (!i. i IN 1..(2 EXP n) ==> P i)"
   (MESON_TAC [CODESET_SETCODE_BIJECTIONS, SUBSET])

  let SETCODE_BOUNDS ← prove
   r"!s n. s SUBSET 1..n ==> setcode s IN (1..(2 EXP n))"
   (MESON_TAC [CODESET_SETCODE_BIJECTIONS])

  parse_as_infix ("$$", (25, "left"))

  let sindex ← new_definition
   r"(x:real^(N)multivector)$$s = x$(setcode s)"

  parse_as_binder "lambdas"

  let lambdas ← new_definition
   r"(lambdas) (g:(num->bool)->real) =
    (lambda i. g(codeset i)):real^(N)multivector"

  let MULTIVECTOR_EQ ← prove
   r"!x y:real^(N)multivector.
        x = y <=> !s. s SUBSET 1..dimindex(:N) ==> x$$s = y$$s"
   (SIMP_TAC [CART_EQ, sindex, FORALL_SETCODE, ← GSYM IN_NUMSEG,
              DIMINDEX_MULTIVECTOR])

  let MULTIVECTOR_BETA ← prove
   r"!s. s SUBSET 1..dimindex(:N)
         ==> ((lambdas) g :real^(N)multivector)$$s = g s"
   (SIMP_TAC [sindex, lambdas, LAMBDA_BETA, SETCODE_BOUNDS,
              DIMINDEX_MULTIVECTOR, ← GSYM IN_NUMSEG] THEN
    MESON_TAC [CODESET_SETCODE_BIJECTIONS])

  let MULTIVECTOR_UNIQUE ← prove
   r"!m:real^(N)multivector g.
        (!s. s SUBSET 1..dimindex(:N) ==> m$$s = g s)
        ==> (lambdas) g = m"
   (SIMP_TAC [MULTIVECTOR_EQ, MULTIVECTOR_BETA] THEN MESON_TAC [])

  let MULTIVECTOR_ETA ← prove
   r"(lambdas s. m$$s) = m"
   (SIMP_TAC [MULTIVECTOR_EQ, MULTIVECTOR_BETA])

  let MULTIVECTOR_ADD_COMPONENT ← prove
   r"!x y:real^(N)multivector s.
      s SUBSET (1..dimindex(:N)) ==> (x + y)$$s = x$$s + y$$s"
   (SIMP_TAC [sindex, SETCODE_BOUNDS, DIMINDEX_MULTIVECTOR,
              ← GSYM IN_NUMSEG, VECTOR_ADD_COMPONENT])

  let MULTIVECTOR_MUL_COMPONENT ← prove
   r"!c x:real^(N)multivector s.
      s SUBSET (1..dimindex(:N)) ==> (c % x)$$s = c * x$$s"
   (SIMP_TAC [sindex, SETCODE_BOUNDS, DIMINDEX_MULTIVECTOR,
              ← GSYM IN_NUMSEG, VECTOR_MUL_COMPONENT])

  let MULTIVECTOR_VEC_COMPONENT ← prove
   r"!k s. s SUBSET (1..dimindex(:N)) ==> (vec k :real^(N)multivector)$$s = &k"
   (SIMP_TAC [sindex, SETCODE_BOUNDS, DIMINDEX_MULTIVECTOR,
              ← GSYM IN_NUMSEG, VEC_COMPONENT])

  let MULTIVECTOR_VSUM_COMPONENT ← prove
   r"!f:A->real^(N)multivector t s.
        s SUBSET (1..dimindex(:N))
        ==> (vsum t f)$$s = sum t (\x. (f x)$$s)"
   (SIMP_TAC [vsum, sindex, LAMBDA_BETA, SETCODE_BOUNDS, ← GSYM IN_NUMSEG,
              DIMINDEX_MULTIVECTOR])

  let MULTIVECTOR_VSUM ← prove
   r"!t f. vsum t f = lambdas s. sum t (\x. (f x)$$s)"
   (SIMP_TAC [MULTIVECTOR_EQ, MULTIVECTOR_BETA, MULTIVECTOR_VSUM_COMPONENT])

  return { setcode, codeset, CODESET_SETCODE_BIJECTIONS, FORALL_SETCODE, SETCODE_BOUNDS,
           sindex, lambdas, MULTIVECTOR_EQ, MULTIVECTOR_BETA, MULTIVECTOR_UNIQUE,
           MULTIVECTOR_ETA, MULTIVECTOR_ADD_COMPONENT, MULTIVECTOR_MUL_COMPONENT,
           MULTIVECTOR_VEC_COMPONENT, MULTIVECTOR_VSUM_COMPONENT, MULTIVECTOR_VSUM }

/- ------------------------------------------------------------------------- -/
/- Basis vectors indexed by subsets of 1..N; linear and bilinear functions   -/
/- are determined by their effect on basis; proving linear properties by    -/
/- extension from basis; injection from regular vectors; k-vectors and the  -/
/- k-grade part of a multivector.  (clifford.ml 230-364)                    -/
/- ------------------------------------------------------------------------- -/

structure Mbasis where
  mbasis : thm
  MBASIS_COMPONENT : thm
  MBASIS_EQ_0 : thm
  MBASIS_NONZERO : thm
  MBASIS_EXPANSION : thm
  SPAN_MBASIS : thm
  LINEAR_EQ_MBASIS : thm
  BILINEAR_EQ_MBASIS : thm
  LINEAR_PROPERTY : thm
  MBASIS_EXTENSION : thm
  multivec : thm
  multivector : thm
  grade : thm
  MULTIVECTOR_GRADE : thm
  GRADE_ADD : thm
  GRADE_CMUL : thm
  deriving Inhabited

@[nospecialize]
def setupMbasis [HolBase] (D : CliffordDeps) (BIndexing : Indexing) :
    ExceptT String IO Mbasis := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, SIMP_RULE, new_definition,
        parse_as_infix, .. } := D
  let { EMPTY_SUBSET, EQ_SYM_EQ, EXTENSION, FINITE_INDUCT_STRONG, FINITE_NUMSEG,
        FINITE_POWERSET, FUN_EQ_THM, IMP_CONJ, IMP_IMP, IN_ELIM_THM, IN_INSERT, IN_UNIV,
        RIGHT_IMP_FORALL_THM, SUBSET_REFL, SUM_DELTA, .. } := D.core
  let { BILINEAR_EQ, COND_COMPONENT, LINEAR_EQ, SPAN_MUL, SPAN_SUPERSET, SPAN_VSUM,
        VECTOR_MUL_LZERO, VSUM_CLAUSES, .. } := D.vec
  let { MULTIVECTOR_ADD_COMPONENT, MULTIVECTOR_BETA, MULTIVECTOR_EQ,
        MULTIVECTOR_MUL_COMPONENT, MULTIVECTOR_VEC_COMPONENT, MULTIVECTOR_VSUM_COMPONENT,
        .. } := BIndexing
  -- @@SCOPE END

  let mbasis ← new_definition
   r"mbasis i = lambdas s. if i = s then &1 else &0"

  let MBASIS_COMPONENT ← prove
   r"!s t. s SUBSET (1..dimindex(:N))
         ==> (mbasis t :real^(N)multivector)$$s = if s = t then &1 else &0"
   (SIMP_TAC [mbasis, IN_ELIM_THM, MULTIVECTOR_BETA] THEN MESON_TAC [])

  let MBASIS_EQ_0 ← prove
   r"!s. (mbasis s :real^(N)multivector = vec 0) <=>
       ~(s SUBSET 1..dimindex(:N))"
   (SIMP_TAC [MULTIVECTOR_EQ, MBASIS_COMPONENT, MULTIVECTOR_VEC_COMPONENT] THEN
    MESON_TAC [← REAL_ARITH (← q r"~(&1 = &0)")])

  let MBASIS_NONZERO ← prove
   r"!s. s SUBSET 1..dimindex(:N) ==> ~(mbasis s :real^(N)multivector = vec 0)"
   (REWRITE_TAC [MBASIS_EQ_0])

  let MBASIS_EXPANSION ← prove
   r"!x:real^(N)multivector.
        vsum {s | s SUBSET 1..dimindex(:N)} (\s. x$$s % mbasis s) = x"
   (SIMP_TAC [MULTIVECTOR_EQ, MULTIVECTOR_VSUM_COMPONENT,
              MULTIVECTOR_MUL_COMPONENT, MBASIS_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC [← REAL_ARITH (← q r"x * (if p then &1 else &0) = if p then x else &0"),
                  SUM_DELTA, IN_ELIM_THM])

  let SPAN_MBASIS ← prove
   r"span {mbasis s :real^(N)multivector | s SUBSET 1..dimindex(:N)} = UNIV"
   (REWRITE_TAC [EXTENSION, IN_UNIV] THEN X_GEN_TAC (← q r"x:real^(N)multivector") THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM MBASIS_EXPANSION] THEN
    MATCH_MP_TAC SPAN_VSUM THEN
    SIMP_TAC [FINITE_NUMSEG, FINITE_POWERSET, IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
    MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC [IN_ELIM_THM] THEN
    ASM_MESON_TAC [])

  let LINEAR_EQ_MBASIS ← prove
   r"!f:real^(M)multivector->real^N g s.
        linear f /\ linear g /\
        (!s. s SUBSET 1..dimindex(:M) ==> f(mbasis s) = g(mbasis s))
        ==> f = g"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"!x. x IN UNIV ==> (f:real^(M)multivector->real^N) x = g x")
     (fun th => MP_TAC th THEN REWRITE_TAC [FUN_EQ_THM, IN_UNIV]) THEN
    MATCH_MP_TAC LINEAR_EQ THEN
    EXISTS_TAC (← q r"{mbasis s :real^(M)multivector | s SUBSET 1..dimindex(:M)}") THEN
    ASM_REWRITE_TAC [SPAN_MBASIS, SUBSET_REFL, IN_ELIM_THM] THEN
    ASM_MESON_TAC [])

  let BILINEAR_EQ_MBASIS ← prove
   r"!f:real^(M)multivector->real^(N)multivector->real^P g s.
        bilinear f /\ bilinear g /\
        (!s t.  s SUBSET 1..dimindex(:M) /\ t SUBSET 1..dimindex(:N)
                ==> f (mbasis s) (mbasis t) = g (mbasis s) (mbasis t))
        ==> f = g"
   (REPEAT STRIP_TAC THEN SUBGOAL_THEN
     (← q r"!x y. x IN UNIV /\ y IN UNIV
          ==> (f:real^(M)multivector->real^(N)multivector->real^P) x y = g x y")
     (fun th => MP_TAC th THEN REWRITE_TAC [FUN_EQ_THM, IN_UNIV]) THEN
    MATCH_MP_TAC BILINEAR_EQ THEN
    EXISTS_TAC (← q r"{mbasis s :real^(M)multivector | s SUBSET 1..dimindex(:M)}") THEN
    EXISTS_TAC (← q r"{mbasis t :real^(N)multivector | t SUBSET 1..dimindex(:N)}") THEN
    ASM_REWRITE_TAC [SPAN_MBASIS, SUBSET_REFL, IN_ELIM_THM] THEN
    ASM_MESON_TAC [])

  let LINEAR_PROPERTY ← prove
   r"!P. P(vec 0) /\ (!x y. P x /\ P y ==> P(x + y))
       ==> !f s. FINITE s /\ (!i. i IN s ==> P(f i)) ==> P(vsum s f)"
   (GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [VSUM_CLAUSES, IN_INSERT])

  let MBASIS_EXTENSION ← prove
   r"!P. (!s. s SUBSET 1..dimindex(:N) ==> P(mbasis s)) /\
       (!c x. P x ==> P(c % x)) /\ (!x y. P x /\ P y ==> P(x + y))
       ==> !x:real^(N)multivector. P x"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [← GSYM MBASIS_EXPANSION] THEN
    MATCH_MP_TAC (← SIMP_RULE [RIGHT_IMP_FORALL_THM, IMP_IMP] LINEAR_PROPERTY) THEN
    ASM_SIMP_TAC [FINITE_POWERSET, FINITE_NUMSEG, IN_ELIM_THM] THEN
    ASM_MESON_TAC [EMPTY_SUBSET, VECTOR_MUL_LZERO])

  let multivec ← new_definition
   r"(multivec:real^N->real^(N)multivector) x =
      vsum(1..dimindex(:N)) (\i. x$i % mbasis{i})"

  parse_as_infix ("multivector", (12, "right"))

  let multivector ← new_definition
   r"k multivector (p:real^(N)multivector) <=>
        !s. s SUBSET (1..dimindex(:N)) /\ ~(p$$s = &0) ==> s HAS_SIZE k"

  parse_as_infix ("grade", (22, "right"))

  let grade ← new_definition
   r"k grade (p:real^(N)multivector) =
     (lambdas s. if s HAS_SIZE k then p$$s else &0):real^(N)multivector"

  let MULTIVECTOR_GRADE ← prove
   r"!k x. k multivector (k grade x)"
   (SIMP_TAC [multivector, grade, MULTIVECTOR_BETA, IMP_CONJ] THEN
    MESON_TAC [])

  let GRADE_ADD ← prove
   r"!x y k. k grade (x + y) = (k grade x) + (k grade y)"
   (SIMP_TAC [grade, MULTIVECTOR_EQ, MULTIVECTOR_ADD_COMPONENT,
              MULTIVECTOR_BETA, COND_COMPONENT] THEN
    REAL_ARITH_TAC)

  let GRADE_CMUL ← prove
   r"!c x k. k grade (c % x) = c % (k grade x)"
   (SIMP_TAC [grade, MULTIVECTOR_EQ, MULTIVECTOR_MUL_COMPONENT,
              MULTIVECTOR_BETA, COND_COMPONENT] THEN
    REAL_ARITH_TAC)

  return { mbasis, MBASIS_COMPONENT, MBASIS_EQ_0, MBASIS_NONZERO, MBASIS_EXPANSION,
           SPAN_MBASIS, LINEAR_EQ_MBASIS, BILINEAR_EQ_MBASIS, LINEAR_PROPERTY,
           MBASIS_EXTENSION, multivec, multivector, grade, MULTIVECTOR_GRADE, GRADE_ADD,
           GRADE_CMUL }

/-- lib.ml's `repeat`: apply `f` until it fails. -/
partial def repeatIO {α : Type} (f : α → ExceptT String IO α) (x : α) :
    ExceptT String IO α :=
  tryCatch (do repeatIO f (← f x)) (fun _ => pure x)

/- ------------------------------------------------------------------------- -/
/- General product construct; it is always bilinear, and under suitable     -/
/- conditions associative.  (clifford.ml 370-436)                           -/
/- ------------------------------------------------------------------------- -/

structure Product where
  Product_DEF : thm
  BILINEAR_PRODUCT : thm
  PRODUCT_LADD : thm
  PRODUCT_RADD : thm
  PRODUCT_LMUL : thm
  PRODUCT_RMUL : thm
  PRODUCT_LNEG : thm
  PRODUCT_RNEG : thm
  PRODUCT_LZERO : thm
  PRODUCT_RZERO : thm
  PRODUCT_ASSOCIATIVE : thm
  deriving Inhabited

@[nospecialize]
def setupProduct [HolBase] (D : CliffordDeps) (BIndexing : Indexing) (BMbasis : Mbasis) :
    ExceptT String IO Product := do
  -- @@SCOPE BEGIN
  let { REAL_ARITH, SIMP_RULE, VECTOR_ARITH_TAC, new_definition, .. } := D
  let { FINITE_NUMSEG, FINITE_POWERSET, IN_ELIM_THM, REAL_MUL_AC, REAL_MUL_ASSOC,
        REAL_MUL_LID, REAL_MUL_RID, SUM_DELTA, SUM_EQ, SUM_LMUL, SUM_RMUL, SUM_SWAP,
        .. } := D.core
  let { BILINEAR_LADD, BILINEAR_LMUL, BILINEAR_LNEG, BILINEAR_LZERO, BILINEAR_RADD,
        BILINEAR_RMUL, BILINEAR_RNEG, BILINEAR_RZERO, VECTOR_MUL_ASSOC, VSUM_ADD, VSUM_EQ,
        VSUM_LMUL, bilinear, linear, .. } := D.vec
  let { MULTIVECTOR_ADD_COMPONENT, MULTIVECTOR_EQ, MULTIVECTOR_MUL_COMPONENT,
        MULTIVECTOR_VSUM_COMPONENT, .. } := BIndexing
  let { MBASIS_COMPONENT, .. } := BMbasis
  -- @@SCOPE END
  let ra (s : String) : ExceptT String IO thm := do REAL_ARITH (← q s)

  let Product_DEF ← new_definition
   r"(Product mult op
     :real^(N)multivector->real^(N)multivector->real^(N)multivector) x y =
        vsum {s | s SUBSET 1..dimindex(:N)}
         (\s. vsum {s | s SUBSET 1..dimindex(:N)}
                (\t. (x$$s * y$$t * mult s t) % mbasis (op s t)))"

  let BILINEAR_PRODUCT ← prove
   r"!mult op. bilinear(Product mult op)"
   (REWRITE_TAC [bilinear, linear, Product_DEF] THEN
    SIMP_TAC [← GSYM VSUM_LMUL, MULTIVECTOR_MUL_COMPONENT] THEN
    REWRITE_TAC [VECTOR_MUL_ASSOC, REAL_MUL_AC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [Product_DEF] THEN
    SIMP_TAC [← GSYM VSUM_ADD, FINITE_POWERSET, FINITE_NUMSEG] THEN
    REPEAT (MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN
           REPEAT STRIP_TAC) THEN
    ASM_SIMP_TAC [MULTIVECTOR_ADD_COMPONENT] THEN VECTOR_ARITH_TAC)

  let PRODUCT_LADD ← MATCH_MP BILINEAR_LADD (← SPEC_ALL BILINEAR_PRODUCT)
  let PRODUCT_RADD ← MATCH_MP BILINEAR_RADD (← SPEC_ALL BILINEAR_PRODUCT)
  let PRODUCT_LMUL ← MATCH_MP BILINEAR_LMUL (← SPEC_ALL BILINEAR_PRODUCT)
  let PRODUCT_RMUL ← MATCH_MP BILINEAR_RMUL (← SPEC_ALL BILINEAR_PRODUCT)
  let PRODUCT_LNEG ← MATCH_MP BILINEAR_LNEG (← SPEC_ALL BILINEAR_PRODUCT)
  let PRODUCT_RNEG ← MATCH_MP BILINEAR_RNEG (← SPEC_ALL BILINEAR_PRODUCT)
  let PRODUCT_LZERO ← MATCH_MP BILINEAR_LZERO (← SPEC_ALL BILINEAR_PRODUCT)
  let PRODUCT_RZERO ← MATCH_MP BILINEAR_RZERO (← SPEC_ALL BILINEAR_PRODUCT)

  let PRODUCT_ASSOCIATIVE ← do
    let SUM_SWAP_POWERSET ← SIMP_RULE [FINITE_POWERSET, FINITE_NUMSEG]
       (← repeatIO (fun th => do SPEC (← q r"{s | s SUBSET 1..dimindex(:N)}") th)
          (← ISPEC (← q r"f:(num->bool)->(num->bool)->real") SUM_SWAP))
    let SWAP_TAC (cnv : ioconv → ioconv) (n : Nat) : tactic :=
      GEN_REWRITE_TAC (cnv o funpow n BINDER_CONV) [SUM_SWAP_POWERSET] THEN
      REWRITE_TAC []
    let SWAPS_TAC (cnv : ioconv → ioconv) (ns : List Nat) (x : term) : tactic :=
      MAP_EVERY (SWAP_TAC cnv) ns THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC x THEN
      REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC
    prove
     r"!op mult. (!s t. s SUBSET 1..dimindex(:N) /\ t SUBSET 1..dimindex(:N)
                    ==> (op s t) SUBSET 1..dimindex(:N)) /\
             (!s t u. op s (op t u) = op (op s t) u) /\
             (!s t u. mult t u * mult s (op t u) = mult s t * mult (op s t) u)
             ==> !x y z:real^(N)multivector.
                        Product mult op x (Product mult op y z) =
                        Product mult op (Product mult op x y) z"
     (REWRITE_TAC [Product_DEF] THEN REPEAT STRIP_TAC THEN
      SIMP_TAC [MULTIVECTOR_EQ, MULTIVECTOR_VSUM_COMPONENT, MBASIS_COMPONENT,
                MULTIVECTOR_MUL_COMPONENT] THEN
      SIMP_TAC [← GSYM SUM_LMUL, ← GSYM SUM_RMUL] THEN
      X_GEN_TAC (← q r"r:num->bool") THEN STRIP_TAC THEN
      SWAPS_TAC RAND_CONV [1, 0] (← q r"s:num->bool") THEN
      SWAP_TAC LAND_CONV 0 THEN SWAPS_TAC RAND_CONV [1, 0] (← q r"t:num->bool") THEN
      SWAP_TAC RAND_CONV 0 THEN SWAPS_TAC LAND_CONV [0] (← q r"u:num->bool") THEN
      REWRITE_TAC [← GSYM REAL_MUL_ASSOC,
        ← ra r"(if p then a else &0) * b = if p then a * b else &0",
        ← ra r"a * (if p then b else &0) = if p then a * b else &0"] THEN
      SIMP_TAC [SUM_DELTA] THEN ASM_SIMP_TAC [IN_ELIM_THM] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_MUL_LID, REAL_MUL_RID] THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [REAL_MUL_AC])

  return { Product_DEF, BILINEAR_PRODUCT, PRODUCT_LADD, PRODUCT_RADD, PRODUCT_LMUL,
           PRODUCT_RMUL, PRODUCT_LNEG, PRODUCT_RNEG, PRODUCT_LZERO, PRODUCT_RZERO,
           PRODUCT_ASSOCIATIVE }

/- ------------------------------------------------------------------------- -/
/- Geometric product.  (clifford.ml 442-488)                                 -/
/- ------------------------------------------------------------------------- -/

structure Geom where
  geom_mul : thm
  BILINEAR_GEOM : thm
  GEOM_LADD : thm
  GEOM_RADD : thm
  GEOM_LMUL : thm
  GEOM_RMUL : thm
  GEOM_LNEG : thm
  GEOM_RNEG : thm
  GEOM_LZERO : thm
  GEOM_RZERO : thm
  GEOM_ASSOC : thm
  deriving Inhabited

@[nospecialize]
def setupGeom [HolBase] (D : CliffordDeps) (BBasics : Basics) (BProduct : Product) :
    ExceptT String IO Geom := do
  -- @@SCOPE BEGIN
  let { SET_TAC, new_definition, overload_interface, .. } := D
  let { EQ_TRANS, ETA_AX, EVEN_ADD, EXTENSION, FORALL_PAIR_THM, FUN_EQ_THM, IN_DIFF,
        IN_ELIM_PAIR_THM, IN_UNION, REAL_POW_ADD, REAL_POW_NEG, REAL_POW_ONE, .. } := D.core
  let { BILINEAR_LADD, BILINEAR_LMUL, BILINEAR_LNEG, BILINEAR_LZERO, BILINEAR_RADD,
        BILINEAR_RMUL, BILINEAR_RNEG, BILINEAR_RZERO, .. } := D.vec
  let { FINITE_CART_SUBSET_LEMMA, SYMDIFF_PARITY_LEMMA, .. } := BBasics
  let { BILINEAR_PRODUCT, PRODUCT_ASSOCIATIVE, .. } := BProduct
  -- @@SCOPE END

  overload_interface "*"
    (← q r"geom_mul:real^(N)multivector->real^(N)multivector->real^(N)multivector")

  let geom_mul ← new_definition
   r"(x:real^(N)multivector) * y =
        Product (\s t. --(&1) pow CARD {i,j | i IN 1..dimindex(:N) /\
                                              j IN 1..dimindex(:N) /\
                                              i IN s /\ j IN t /\ i > j})
                (\s t. (s DIFF t) UNION (t DIFF s))
                x y"

  let BILINEAR_GEOM ← prove
   r"bilinear(geom_mul)"
   (REWRITE_TAC [← REWRITE_RULE [← GSYM FUN_EQ_THM, ETA_AX] geom_mul] THEN
    MATCH_ACCEPT_TAC BILINEAR_PRODUCT)

  let GEOM_LADD ← MATCH_MP BILINEAR_LADD (← SPEC_ALL BILINEAR_GEOM)
  let GEOM_RADD ← MATCH_MP BILINEAR_RADD (← SPEC_ALL BILINEAR_GEOM)
  let GEOM_LMUL ← MATCH_MP BILINEAR_LMUL (← SPEC_ALL BILINEAR_GEOM)
  let GEOM_RMUL ← MATCH_MP BILINEAR_RMUL (← SPEC_ALL BILINEAR_GEOM)
  let GEOM_LNEG ← MATCH_MP BILINEAR_LNEG (← SPEC_ALL BILINEAR_GEOM)
  let GEOM_RNEG ← MATCH_MP BILINEAR_RNEG (← SPEC_ALL BILINEAR_GEOM)
  let GEOM_LZERO ← MATCH_MP BILINEAR_LZERO (← SPEC_ALL BILINEAR_GEOM)
  let GEOM_RZERO ← MATCH_MP BILINEAR_RZERO (← SPEC_ALL BILINEAR_GEOM)

  let GEOM_ASSOC ← prove
   r"!x y z:real^(N)multivector. x * (y * z) = (x * y) * z"
   (REWRITE_TAC [geom_mul] THEN MATCH_MP_TAC PRODUCT_ASSOCIATIVE THEN
    REPEAT (CONJ_TAC THENL [SET_TAC [], ALL_TAC]) THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM REAL_POW_ADD] THEN
    REWRITE_TAC [REAL_POW_NEG, REAL_POW_ONE] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [EVEN_ADD] THEN
    (fun gl => tactic_of (do
      let w := gl.2
      let tu ← liftExcept (funpowM 2 lhand w)
      let su := (← liftExcept (vsubst [(← q r"s:num->bool", ← q r"t:num->bool")])) tu
      let st := (← liftExcept (vsubst [(← q r"t:num->bool", ← q r"u:num->bool")])) su
      let mkEq ← ExceptT.mk (mk_eq : IO _)
      let e ← liftExcept (do mkEq (st, ← mkEq (su, tu)))
      pure (MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC e)) gl) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC (← TAUT (← q r"(x <=> y <=> z) ==> ((a <=> x) <=> (y <=> z <=> a))")),
      AP_TERM_TAC THEN CONV_TAC SYM_CONV] THEN
    MATCH_MP_TAC SYMDIFF_PARITY_LEMMA THEN
    REWRITE_TAC [FINITE_CART_SUBSET_LEMMA] THEN
    REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_ELIM_PAIR_THM,
                 IN_UNION, IN_DIFF] THEN
    CONV_TAC (fun t => (TAUT t).run))

  return { geom_mul, BILINEAR_GEOM, GEOM_LADD, GEOM_RADD, GEOM_LMUL, GEOM_RMUL, GEOM_LNEG,
           GEOM_RNEG, GEOM_LZERO, GEOM_RZERO, GEOM_ASSOC }

/- ------------------------------------------------------------------------- -/
/- Outer product; inner product.  (clifford.ml 494-583)                      -/
/- ------------------------------------------------------------------------- -/

structure OuterInner where
  outer : thm
  OUTER : thm
  BILINEAR_OUTER : thm
  OUTER_LADD : thm
  OUTER_RADD : thm
  OUTER_LMUL : thm
  OUTER_RMUL : thm
  OUTER_LNEG : thm
  OUTER_RNEG : thm
  OUTER_LZERO : thm
  OUTER_RZERO : thm
  OUTER_ASSOC : thm
  inner : thm
  BILINEAR_INNER : thm
  INNER_LADD : thm
  INNER_RADD : thm
  INNER_LMUL : thm
  INNER_RMUL : thm
  INNER_LNEG : thm
  INNER_RNEG : thm
  INNER_LZERO : thm
  INNER_RZERO : thm
  deriving Inhabited

@[nospecialize]
def setupOuterInner [HolBase] (D : CliffordDeps) (BBasics : Basics) (BProduct : Product) :
    ExceptT String IO OuterInner := do
  -- @@SCOPE BEGIN
  let { SET_RULE, SET_TAC, new_definition, parse_as_infix, .. } := D
  let { EMPTY_UNION, ETA_AX, EXTENSION, FORALL_PAIR_THM, FUN_EQ_THM, IN_ELIM_PAIR_THM,
        IN_INTER, IN_UNION, NOT_IN_EMPTY, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_POW_ADD,
        UNION_ASSOC, UNION_SUBSET, .. } := D.core
  let { BILINEAR_LADD, BILINEAR_LMUL, BILINEAR_LNEG, BILINEAR_LZERO, BILINEAR_RADD,
        BILINEAR_RMUL, BILINEAR_RNEG, BILINEAR_RZERO, VECTOR_MUL_LZERO, .. } := D.vec
  let { CARD_UNION_LEMMA, FINITE_CART_SUBSET_LEMMA, .. } := BBasics
  let { BILINEAR_PRODUCT, PRODUCT_ASSOCIATIVE, Product_DEF, .. } := BProduct
  -- @@SCOPE END
  let sr (s : String) : ExceptT String IO thm := do SET_RULE (← q s)

  parse_as_infix ("outer", (20, "right"))

  let outer ← new_definition
   r"!x y:real^(N)multivector.
    x outer y =
        Product (\s t. if ~(s INTER t = {}) then &0
                       else --(&1) pow CARD {i,j | i IN 1..dimindex(:N) /\
                                                   j IN 1..dimindex(:N) /\
                                                   i IN s /\ j IN t /\ i > j})
                (\s t. (s DIFF t) UNION (t DIFF s))
                x y"

  let OUTER ← prove
   r"!x y:real^(N)multivector.
    x outer y =
        Product (\s t. if ~(s INTER t = {}) then &0
                       else --(&1) pow CARD {i,j | i IN 1..dimindex(:N) /\
                                                   j IN 1..dimindex(:N) /\
                                                   i IN s /\ j IN t /\ i > j})
                (UNION)
                x y"
   (REPEAT GEN_TAC THEN REWRITE_TAC [outer, Product_DEF] THEN
    REPEAT (AP_TERM_TAC THEN ABS_TAC) THEN
    ASM_CASES_TAC (← q r"s INTER t :num->bool = {}") THEN
    ASM_REWRITE_TAC [REAL_MUL_RZERO, VECTOR_MUL_LZERO] THEN
    ASM_SIMP_TAC [← sr
     r"(s INTER t = {}) ==> (s DIFF t) UNION (t DIFF s) = s UNION t"])

  let BILINEAR_OUTER ← prove
   r"bilinear(outer)"
   (REWRITE_TAC [← REWRITE_RULE [← GSYM FUN_EQ_THM, ETA_AX] outer] THEN
    MATCH_ACCEPT_TAC BILINEAR_PRODUCT)

  let OUTER_LADD ← MATCH_MP BILINEAR_LADD (← SPEC_ALL BILINEAR_OUTER)
  let OUTER_RADD ← MATCH_MP BILINEAR_RADD (← SPEC_ALL BILINEAR_OUTER)
  let OUTER_LMUL ← MATCH_MP BILINEAR_LMUL (← SPEC_ALL BILINEAR_OUTER)
  let OUTER_RMUL ← MATCH_MP BILINEAR_RMUL (← SPEC_ALL BILINEAR_OUTER)
  let OUTER_LNEG ← MATCH_MP BILINEAR_LNEG (← SPEC_ALL BILINEAR_OUTER)
  let OUTER_RNEG ← MATCH_MP BILINEAR_RNEG (← SPEC_ALL BILINEAR_OUTER)
  let OUTER_LZERO ← MATCH_MP BILINEAR_LZERO (← SPEC_ALL BILINEAR_OUTER)
  let OUTER_RZERO ← MATCH_MP BILINEAR_RZERO (← SPEC_ALL BILINEAR_OUTER)

  let OUTER_ASSOC ← prove
   r"!x y z:real^(N)multivector. x outer (y outer z) = (x outer y) outer z"
   (REWRITE_TAC [OUTER] THEN MATCH_MP_TAC PRODUCT_ASSOCIATIVE THEN
    SIMP_TAC [UNION_SUBSET, UNION_ASSOC,
       ← sr r"s INTER (t UNION u) = (s INTER t) UNION (s INTER u)",
       ← sr r"(t UNION u) INTER s = (t INTER s) UNION (u INTER s)"] THEN
    REWRITE_TAC [EMPTY_UNION] THEN REPEAT GEN_TAC THEN
    MAP_EVERY ASM_CASES_TAC
     [← q r"s INTER t :num->bool = {}",
      ← q r"s INTER u :num->bool = {}",
      ← q r"t INTER u :num->bool = {}"] THEN
    ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
    REWRITE_TAC [← GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CARD_UNION_LEMMA THEN REWRITE_TAC [FINITE_CART_SUBSET_LEMMA] THEN
    SIMP_TAC [EXTENSION, FORALL_PAIR_THM, NOT_IN_EMPTY, IN_UNION, IN_INTER] THEN
    REWRITE_TAC [IN_ELIM_PAIR_THM] THEN ASM SET_TAC [])

  parse_as_infix ("inner", (20, "right"))

  let inner ← new_definition
   r"!x y:real^(N)multivector.
    x inner y =
        Product (\s t. if s = {} \/ t = {} \/
                          ~((s DIFF t) = {} /\ ~(t DIFF s = {}))
                       then &0
                       else --(&1) pow CARD {i,j | i IN 1..dimindex(:N) /\
                                                   j IN 1..dimindex(:N) /\
                                                   i IN s /\ j IN t /\ i > j})
                (\s t. (s DIFF t) UNION (t DIFF s))
                x y"

  let BILINEAR_INNER ← prove
   r"bilinear(inner)"
   (REWRITE_TAC [← REWRITE_RULE [← GSYM FUN_EQ_THM, ETA_AX] inner] THEN
    MATCH_ACCEPT_TAC BILINEAR_PRODUCT)

  let INNER_LADD ← MATCH_MP BILINEAR_LADD (← SPEC_ALL BILINEAR_INNER)
  let INNER_RADD ← MATCH_MP BILINEAR_RADD (← SPEC_ALL BILINEAR_INNER)
  let INNER_LMUL ← MATCH_MP BILINEAR_LMUL (← SPEC_ALL BILINEAR_INNER)
  let INNER_RMUL ← MATCH_MP BILINEAR_RMUL (← SPEC_ALL BILINEAR_INNER)
  let INNER_LNEG ← MATCH_MP BILINEAR_LNEG (← SPEC_ALL BILINEAR_INNER)
  let INNER_RNEG ← MATCH_MP BILINEAR_RNEG (← SPEC_ALL BILINEAR_INNER)
  let INNER_LZERO ← MATCH_MP BILINEAR_LZERO (← SPEC_ALL BILINEAR_INNER)
  let INNER_RZERO ← MATCH_MP BILINEAR_RZERO (← SPEC_ALL BILINEAR_INNER)

  return { outer, OUTER, BILINEAR_OUTER, OUTER_LADD, OUTER_RADD, OUTER_LMUL, OUTER_RMUL,
           OUTER_LNEG, OUTER_RNEG, OUTER_LZERO, OUTER_RZERO, OUTER_ASSOC, inner,
           BILINEAR_INNER, INNER_LADD, INNER_RADD, INNER_LMUL, INNER_RMUL, INNER_LNEG,
           INNER_RNEG, INNER_LZERO, INNER_RZERO }

/- ------------------------------------------------------------------------- -/
/- Actions of products on basis and singleton basis.  (clifford.ml 589-701) -/
/- ------------------------------------------------------------------------- -/

structure MbasisProd where
  PRODUCT_MBASIS : thm
  PRODUCT_MBASIS_SING : thm
  GEOM_MBASIS : thm
  GEOM_MBASIS_SING : thm
  OUTER_MBASIS : thm
  OUTER_MBASIS_SING : thm
  deriving Inhabited

@[nospecialize]
def setupMbasisProd [HolBase] (D : CliffordDeps) (BIndexing : Indexing) (BMbasis : Mbasis)
    (BProduct : Product) (BGeom : Geom) (BOuterInner : OuterInner) :
    ExceptT String IO MbasisProd := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, REAL_ARITH, SET_RULE, SET_TAC, VECTOR_ARITH_TAC, .. } := D
  let { CARD_CLAUSES, COND_ID, COND_RAND, COND_RATOR, EXTENSION, FINITE_RULES,
        FORALL_PAIR_THM, GT, IN_ELIM_PAIR_THM, IN_ELIM_THM, IN_SING, LT_REFL, NOT_IN_EMPTY,
        PAIR_EQ, SUBSET, real_pow, .. } := D.core
  let { VECTOR_MUL_LID, VECTOR_MUL_LZERO, VSUM_0, VSUM_DELTA, .. } := D.vec
  let { MULTIVECTOR_MUL_COMPONENT, .. } := BIndexing
  let { MBASIS_COMPONENT, .. } := BMbasis
  let { Product_DEF, .. } := BProduct
  let { geom_mul, .. } := BGeom
  let { OUTER, .. } := BOuterInner
  -- @@SCOPE END
  let sr (s : String) : ExceptT String IO thm := do SET_RULE (← q s)

  let PRODUCT_MBASIS ← prove
   r"!s t. Product mult op (mbasis s) (mbasis t) :real^(N)multivector =
            if s SUBSET 1..dimindex(:N) /\ t SUBSET 1..dimindex(:N)
            then mult s t % mbasis(op s t)
            else vec 0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [Product_DEF] THEN
    SIMP_TAC [MULTIVECTOR_MUL_COMPONENT, MBASIS_COMPONENT] THEN
    REWRITE_TAC [← REAL_ARITH (← q
     r"(if p then &1 else &0) * (if q then &1 else &0) * x =
    if q then if p then x else &0 else &0")] THEN
    REPEAT
     (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [COND_RAND] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [COND_RATOR] THEN
      SIMP_TAC [VECTOR_MUL_LZERO, COND_ID, VSUM_DELTA, IN_ELIM_THM, VSUM_0] THEN
      ASM_CASES_TAC (← q r"t SUBSET 1..dimindex(:N)") THEN ASM_REWRITE_TAC []))

  let PRODUCT_MBASIS_SING ← prove
   r"!i j. Product mult op (mbasis{i}) (mbasis{j}) :real^(N)multivector =
            if i IN 1..dimindex(:N) /\ j IN 1..dimindex(:N)
            then mult {i} {j} % mbasis(op {i} {j})
            else vec 0"
   (REWRITE_TAC [PRODUCT_MBASIS, ← sr r"{x} SUBSET s <=> x IN s"])

  let GEOM_MBASIS ← prove
   r"!s t. mbasis s * mbasis t :real^(N)multivector =
                if s SUBSET 1..dimindex(:N) /\ t SUBSET 1..dimindex(:N)
                then --(&1) pow CARD {i,j | i IN s /\ j IN t /\ i > j} %
                     mbasis((s DIFF t) UNION (t DIFF s))
                else vec 0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [geom_mul, PRODUCT_MBASIS] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_PAIR_THM, FORALL_PAIR_THM] THEN
    ASM_MESON_TAC [SUBSET])

  let GEOM_MBASIS_SING ← prove
   r"!i j. mbasis{i} * mbasis{j} :real^(N)multivector =
                if i IN 1..dimindex(:N) /\ j IN 1..dimindex(:N)
                then if i = j then mbasis{}
                     else if i < j then mbasis{i,j}
                     else --(mbasis{i,j})
                else vec 0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [geom_mul, PRODUCT_MBASIS_SING] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [IN_SING] THEN
    SUBGOAL_THEN
     (← q r"{i',j' | i' IN 1 .. dimindex (:N) /\
             j' IN 1 .. dimindex (:N) /\
             i' = i /\
             j' = j /\
             i' > j'} =
    if i > j then {(i,j)} else {}")
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_ELIM_PAIR_THM, IN_SING] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [IN_SING, NOT_IN_EMPTY, PAIR_EQ] THEN
      ASM_MESON_TAC [LT_REFL],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"i:num = j") THEN ASM_REWRITE_TAC [GT, LT_REFL] THENL
     [REWRITE_TAC [CARD_CLAUSES, real_pow, VECTOR_MUL_LID] THEN
      AP_TERM_TAC THEN SET_TAC [],
      ALL_TAC] THEN
    ASM_SIMP_TAC [← sr
     r"~(i = j) ==> ({i} DIFF {j}) UNION ({j} DIFF {i}) = {i,j}"] THEN
    FIRST_ASSUM (SUBST1_TAC o MATCH_MP (← ARITH_RULE (← q
     r"~(i:num = j) ==> (j < i <=> ~(i < j))"))) THEN
    ASM_CASES_TAC (← q r"i:num < j") THEN
    ASM_SIMP_TAC [CARD_CLAUSES, real_pow, VECTOR_MUL_LID, FINITE_RULES,
                  NOT_IN_EMPTY] THEN
    VECTOR_ARITH_TAC)

  let OUTER_MBASIS ← prove
   r"!s t. (mbasis s) outer (mbasis t) :real^(N)multivector =
                if s SUBSET 1..dimindex(:N) /\ t SUBSET 1..dimindex(:N) /\
                   s INTER t = {}
                then --(&1) pow CARD {i,j | i IN s /\ j IN t /\ i > j} %
                     mbasis(s UNION t)
                else vec 0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [OUTER, PRODUCT_MBASIS] THEN
    ASM_CASES_TAC (← q r"(s:num->bool) INTER t = {}") THEN
    ASM_REWRITE_TAC [VECTOR_MUL_LZERO, COND_ID] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_PAIR_THM, FORALL_PAIR_THM] THEN
    ASM_MESON_TAC [SUBSET])

  let OUTER_MBASIS_SING ← prove
   r"!i j. mbasis{i} outer mbasis{j} :real^(N)multivector =
                if i IN 1..dimindex(:N) /\ j IN 1..dimindex(:N) /\ ~(i = j)
                then if i < j then mbasis{i,j} else --(mbasis{i,j})
                else vec 0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [OUTER, PRODUCT_MBASIS_SING] THEN
    REWRITE_TAC [← sr r"{i} INTER {j} = {} <=> ~(i = j)"] THEN
    ASM_CASES_TAC (← q r"i:num = j") THEN
    ASM_REWRITE_TAC [VECTOR_MUL_LZERO, COND_ID] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [IN_SING] THEN
    SUBGOAL_THEN
     (← q r"{i',j' | i' IN 1 .. dimindex (:N) /\
             j' IN 1 .. dimindex (:N) /\
             i' = i /\
             j' = j /\
             i' > j'} =
    if i > j then {(i,j)} else {}")
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_ELIM_PAIR_THM, IN_SING] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [IN_SING, NOT_IN_EMPTY, PAIR_EQ] THEN
      ASM_MESON_TAC [LT_REFL],
      ALL_TAC] THEN
    ASM_SIMP_TAC [GT, ← sr r"{i} UNION {j} = {i,j}"] THEN
    FIRST_ASSUM (SUBST1_TAC o MATCH_MP (← ARITH_RULE (← q
     r"~(i:num = j) ==> (j < i <=> ~(i < j))"))) THEN
    ASM_CASES_TAC (← q r"i:num < j") THEN
    ASM_SIMP_TAC [CARD_CLAUSES, real_pow, VECTOR_MUL_LID, FINITE_RULES,
                  NOT_IN_EMPTY] THEN
    VECTOR_ARITH_TAC)

  return { PRODUCT_MBASIS, PRODUCT_MBASIS_SING, GEOM_MBASIS, GEOM_MBASIS_SING, OUTER_MBASIS,
           OUTER_MBASIS_SING }

/- ------------------------------------------------------------------------- -/
/- Some simple consequences.  (clifford.ml 707-750)                          -/
/- ------------------------------------------------------------------------- -/

structure MbasisCons where
  OUTER_MBASIS_SKEWSYM : thm
  OUTER_MBASIS_REFL : thm
  OUTER_MBASIS_LSCALAR : thm
  OUTER_MBASIS_RSCALAR : thm
  MBASIS_SPLIT : thm
  deriving Inhabited

@[nospecialize]
def setupMbasisCons [HolBase] (D : CliffordDeps) (BMbasis : Mbasis)
    (BOuterInner : OuterInner) (BMbasisProd : MbasisProd) : ExceptT String IO MbasisCons := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, SET_RULE, SET_TAC, VECTOR_ARITH, .. } := D
  let { CARD_CLAUSES, CONJ_ACI, EMPTY_SUBSET, EXTENSION, FORALL_PAIR_THM, INTER_EMPTY,
        IN_ELIM_PAIR_THM, IN_SING, LT_REFL, NOT_IN_EMPTY, UNION_EMPTY, real_pow, .. } := D.core
  let { VECTOR_MUL_LID, VECTOR_NEG_0, VECTOR_NEG_NEG, .. } := D.vec
  let { MBASIS_EQ_0, MBASIS_EXTENSION, .. } := BMbasis
  let { OUTER_LADD, OUTER_LMUL, OUTER_RADD, OUTER_RMUL, .. } := BOuterInner
  let { OUTER_MBASIS, OUTER_MBASIS_SING, .. } := BMbasisProd
  -- @@SCOPE END
  let sr (s : String) : ExceptT String IO thm := do SET_RULE (← q s)

  let OUTER_MBASIS_SKEWSYM ← prove
   r"!i j. mbasis{i} outer mbasis{j} = --(mbasis{j} outer mbasis{i})"
   (REPEAT GEN_TAC THEN REWRITE_TAC [OUTER_MBASIS_SING] THEN
    ASM_CASES_TAC (← q r"i:num = j") THEN ASM_REWRITE_TAC [VECTOR_NEG_0] THEN
    FIRST_ASSUM (DISJ_CASES_TAC o MATCH_MP (← ARITH_RULE (← q
     r"~(i:num = j) ==> i < j /\ ~(j < i) \/ j < i /\ ~(i < j)"))) THEN
    ASM_REWRITE_TAC [CONJ_ACI] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [VECTOR_NEG_NEG, VECTOR_NEG_0] THEN
    REPEAT AP_TERM_TAC THEN SET_TAC [])

  let OUTER_MBASIS_REFL ← prove
   r"!i. mbasis{i} outer mbasis{i} = vec 0"
   (GEN_TAC THEN MATCH_MP_TAC (← VECTOR_ARITH (← q
     r"!x:real^N. x = --x ==> x = vec 0")) THEN
    MATCH_ACCEPT_TAC OUTER_MBASIS_SKEWSYM)

  let OUTER_MBASIS_LSCALAR ← prove
   r"!x. mbasis{} outer x = x"
   (MATCH_MP_TAC MBASIS_EXTENSION THEN SIMP_TAC [OUTER_RMUL, OUTER_RADD] THEN
    SIMP_TAC [OUTER_MBASIS, EMPTY_SUBSET, INTER_EMPTY, UNION_EMPTY] THEN
    REWRITE_TAC [← sr r"{i,j | i IN {} /\ j IN s /\ i:num > j} = {}"] THEN
    REWRITE_TAC [CARD_CLAUSES, real_pow, VECTOR_MUL_LID])

  let OUTER_MBASIS_RSCALAR ← prove
   r"!x. x outer mbasis{} = x"
   (MATCH_MP_TAC MBASIS_EXTENSION THEN SIMP_TAC [OUTER_LMUL, OUTER_LADD] THEN
    SIMP_TAC [OUTER_MBASIS, EMPTY_SUBSET, INTER_EMPTY, UNION_EMPTY] THEN
    REWRITE_TAC [← sr r"{i,j | i IN s /\ j IN {} /\ i:num > j} = {}"] THEN
    REWRITE_TAC [CARD_CLAUSES, real_pow, VECTOR_MUL_LID])

  let MBASIS_SPLIT ← prove
   r"!a s. (!x. x IN s ==> a < x)
         ==> mbasis (a INSERT s) = mbasis{a} outer mbasis s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [OUTER_MBASIS] THEN
    SUBGOAL_THEN (← q r"{a:num} INTER s = {}") SUBST1_TAC THENL
     [ASM SET_TAC [LT_REFL], ALL_TAC] THEN
    SIMP_TAC [← sr r"{a} SUBSET t /\ s SUBSET t <=> (a INSERT s) SUBSET t"] THEN
    COND_CASES_TAC THENL [ALL_TAC, ASM_MESON_TAC [MBASIS_EQ_0]] THEN
    REWRITE_TAC [← sr r"{a} UNION s = a INSERT s"] THEN
    SUBGOAL_THEN (← q r"{(i:num),(j:num) | i IN {a} /\ j IN s /\ i > j} = {}")
     (fun th => SIMP_TAC [th, CARD_CLAUSES, real_pow, VECTOR_MUL_LID]) THEN
    REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_ELIM_PAIR_THM, IN_SING,
                 NOT_IN_EMPTY] THEN
    ASM_MESON_TAC [← ARITH_RULE (← q r"~(n < m /\ n:num > m)")])

  return { OUTER_MBASIS_SKEWSYM, OUTER_MBASIS_REFL, OUTER_MBASIS_LSCALAR,
           OUTER_MBASIS_RSCALAR, MBASIS_SPLIT }

/-- The recursive `conv` of `MBASIS_SPLIT_CONV` (clifford.ml 785-789), over
    the set-enumeration destructor, the side-condition conversion and the
    instantiated split theorem. -/
partial def mbasisSplitGo [HolBase] (dest_setenum : term → Except String (List term))
    (SET_CHECK_CONV : ioconv) (INST_SPLIT : term → ExceptT String IO thm) : ioconv :=
  fun tm => (do
    if (← liftExcept (dest_setenum (← liftExcept (rand tm)))).length ≤ 1 then
      pure (REFL tm)
    else
      let th ← MP_CONV SET_CHECK_CONV (← INST_SPLIT tm)
      let th' ← ExceptT.mk
        (RAND_CONV (mbasisSplitGo dest_setenum SET_CHECK_CONV INST_SPLIT)
          (← liftExcept (rand (concl th))))
      HolLight.TRANS th th' : ExceptT String IO thm).run

/- ------------------------------------------------------------------------- -/
/- Just for generality, normalize a set enumeration.  Conversion to split    -/
/- extended basis combinations; also 1-step merge from left, which can be    -/
/- DEPTH_CONV'd. In this case the order must be correct.                     -/
/- (clifford.ml 756-797)                                                      -/
/- ------------------------------------------------------------------------- -/

structure OuterConv1 where
  SETENUM_NORM_CONV : ioconv
  MBASIS_SPLIT_CONV : ioconv
  MBASIS_MERGE_CONV : ioconv
  deriving Inhabited

@[nospecialize]
def setupOuterConv1 [HolBase] (D : CliffordDeps) (BMbasisCons : MbasisCons) :
    ExceptT String IO OuterConv1 := do
  -- @@SCOPE BEGIN
  let { DISJ_ACI_RULE, NUM_REDUCE_CONV, SET_RULE, dest_setenum, is_numeral, mk_numeral,
        mk_setenum, .. } := D
  let { EXTENSION, FORALL_SIMP, IN_INSERT, IN_SING, .. } := D.core
  let { MBASIS_SPLIT, .. } := BMbasisCons
  -- @@SCOPE END

  let SETENUM_NORM_CONV : ioconv :=
    let conv :=
      GEN_REWRITE_CONV id [EXTENSION] THENC
      GEN_REWRITE_CONV TOP_SWEEP_CONV [IN_SING, IN_INSERT] THENC
      BINDER_CONV (fun t => (do EQT_INTRO (← DISJ_ACI_RULE t) : ExceptT String IO thm).run)
      THENC GEN_REWRITE_CONV id [FORALL_SIMP]
    fun tm => (do
      let nums ← liftExcept (dest_setenum tm)
      let vals ← liftExcept (nums.mapM HolCore.Basics.dest_numeral)
      let nums' ← liftExcept ((vals.mergeSort (· ≤ ·)).eraseDups.mapM mk_numeral)
      if nums' == nums then pure (REFL tm) else
      let mkEq ← ExceptT.mk (mk_eq : IO _)
      let ty := (← liftExcept (HolCore.Basics.dest_fun_ty (type_of tm))).1
      let eq ← liftExcept (mkEq (tm, ← mk_setenum (nums', ty)))
      EQT_ELIM (← ExceptT.mk (conv eq)) : ExceptT String IO thm).run

  let (MBASIS_SPLIT_CONV, MBASIS_MERGE_CONV) ← do
    let setlemma ← SET_RULE (← q
     r"((!x:num. x IN {} ==> a < x) <=> T) /\
    ((!x:num. x IN (y INSERT s) ==> a < x) <=>
              a < y /\ (!x. x IN s ==> a < x))")
    let SET_CHECK_CONV :=
      GEN_REWRITE_CONV TOP_SWEEP_CONV [setlemma] THENC NUM_REDUCE_CONV
    let INST_SPLIT := PART_MATCH (fun t => do lhs (← rand t)) MBASIS_SPLIT
    let gsplit ← GSYM MBASIS_SPLIT
    let INST_MERGE := PART_MATCH (fun t => do lhs (← rand t)) gsplit
    let conv := mbasisSplitGo dest_setenum SET_CHECK_CONV INST_SPLIT
    let split : ioconv := fun tm => (do
      tryCatch (do
          let (op, se) ← liftExcept (dest_comb tm)
          let elems ← liftExcept (dest_setenum se)
          if (← liftExcept (dest_const op)).1 == "mbasis" && elems.all is_numeral then
            ExceptT.mk ((RAND_CONV SETENUM_NORM_CONV THENC conv) tm)
          else throw "fail")
        (fun _ => throw "MBASIS_SPLIT_CONV") : ExceptT String IO thm).run
    let merge : ioconv := fun tm => (do
      tryCatch (do MP_CONV SET_CHECK_CONV (← INST_MERGE tm))
        (fun _ => throw "MBASIS_MERGE_CONV") : ExceptT String IO thm).run
    pure (split, merge)

  return { SETENUM_NORM_CONV, MBASIS_SPLIT_CONV, MBASIS_MERGE_CONV }

/- ------------------------------------------------------------------------- -/
/- Convergent (if slow) rewrite set to bubble into position; group the      -/
/- final "c1 % mbasis s1 + ... + cn % mbasis sn"; overall conversion.        -/
/- (clifford.ml 803-865)                                                      -/
/- ------------------------------------------------------------------------- -/

structure OuterConv2 where
  OUTER_ACI : thm
  MBASIS_GROUP_CONV : ioconv
  OUTER_CANON_CONV : ioconv
  deriving Inhabited

@[nospecialize]
def setupOuterConv2 [HolBase] (D : CliffordDeps) (BOuterInner : OuterInner)
    (BMbasisCons : MbasisCons) (BOuterConv1 : OuterConv1) : ExceptT String IO OuterConv2 := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, PURE_SIMP_CONV, REAL_POLY_CONV, REAL_RAT_REDUCE_CONV, VECTOR_ARITH,
        .. } := D
  let { ARITH_GE, ARITH_GT, .. } := D.core
  let { VECTOR_ADD_AC, VECTOR_ADD_ASSOC, VECTOR_ADD_LDISTRIB, VECTOR_ADD_LID,
        VECTOR_ADD_RDISTRIB, VECTOR_ADD_RID, VECTOR_MUL_ASSOC, VECTOR_MUL_LID,
        VECTOR_MUL_LZERO, VECTOR_MUL_RZERO, VECTOR_NEG_MINUS1, VECTOR_SUB, .. } := D.vec
  let { OUTER_ASSOC, OUTER_LADD, OUTER_LMUL, OUTER_LNEG, OUTER_LZERO, OUTER_RADD, OUTER_RMUL,
        OUTER_RZERO, .. } := BOuterInner
  let { OUTER_MBASIS_LSCALAR, OUTER_MBASIS_REFL, OUTER_MBASIS_RSCALAR, OUTER_MBASIS_SKEWSYM,
        .. } := BMbasisCons
  let { MBASIS_MERGE_CONV, MBASIS_SPLIT_CONV, .. } := BOuterConv1
  -- @@SCOPE END

  let OUTER_ACI ← prove
   r"(!x y z. (x outer y) outer z = x outer (y outer z)) /\
   (!i j. i > j
          ==> mbasis{i} outer mbasis{j} =
              --(&1) % (mbasis{j} outer mbasis{i})) /\
   (!i j x. i > j
            ==> mbasis{i} outer mbasis{j} outer x =
                --(&1) % (mbasis{j} outer mbasis{i} outer x)) /\
   (!i. mbasis{i} outer mbasis{i} = vec 0) /\
   (!i x. mbasis{i} outer mbasis{i} outer x = vec 0) /\
   (!x. mbasis{} outer x = x) /\
   (!x. x outer mbasis{} = x)"
   (REWRITE_TAC [OUTER_ASSOC, OUTER_LZERO, OUTER_RZERO, OUTER_LADD,
              OUTER_RADD, OUTER_LMUL, OUTER_RMUL, OUTER_LZERO, OUTER_RZERO] THEN
    REWRITE_TAC [OUTER_MBASIS_REFL, OUTER_LZERO] THEN
    REWRITE_TAC [OUTER_MBASIS_LSCALAR, OUTER_MBASIS_RSCALAR] THEN
    SIMP_TAC [← GSYM VECTOR_NEG_MINUS1, ← VECTOR_ARITH (← q r"x - y:real^N = x + --y")] THEN
    MESON_TAC [OUTER_MBASIS_SKEWSYM, OUTER_LNEG])

  let MBASIS_GROUP_CONV : ioconv := fun tm => (do
    let tms := striplist (HolCore.Basics.dest_binary "vector_add") tm
    if tms.length == 1 then ExceptT.mk (LAND_CONV REAL_POLY_CONV tm) else
    let vadd_tm ← liftExcept (do rator (← rator tm))
    let mk_vadd (a b : term) : ExceptT String IO term :=
      liftExcept (do (← HolCore.Basics.mk_binop vadd_tm a) b)
    let mbs ← liftExcept (tms.mapM (fun t => do pure (← HolCore.Basics.dest_binary "%" t).2))
    let tmbs ← liftExcept (zip mbs tms)
    let mset := setify mbs
    let grps := mset.map (fun x => (tmbs.filter (fun (x', _) => x' == x)).map (·.2))
    let tm' ← end_itlist mk_vadd (← grps.mapM (end_itlist mk_vadd))
    let mkEq ← ExceptT.mk (mk_eq : IO _)
    let th1 ← AC VECTOR_ADD_AC (← liftExcept (mkEq (tm, tm')))
    let th2 ← ExceptT.mk
     ((GEN_REWRITE_CONV DEPTH_CONV [← GSYM VECTOR_ADD_RDISTRIB] THENC
       DEPTH_BINOP_CONV vadd_tm (LAND_CONV REAL_POLY_CONV)) tm')
    HolLight.TRANS th1 th2 : ExceptT String IO thm).run

  let OUTER_CANON_CONV : ioconv :=
    ONCE_DEPTH_CONV MBASIS_SPLIT_CONV THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV
     [VECTOR_SUB, VECTOR_NEG_MINUS1,
      OUTER_LADD, OUTER_RADD, OUTER_LMUL, OUTER_RMUL, OUTER_LZERO, OUTER_RZERO,
      VECTOR_ADD_LDISTRIB, VECTOR_ADD_RDISTRIB, VECTOR_MUL_ASSOC,
      VECTOR_MUL_LZERO, VECTOR_MUL_RZERO] THENC
    REAL_RAT_REDUCE_CONV THENC
    PURE_SIMP_CONV [OUTER_ACI, ARITH_GT, ARITH_GE, OUTER_LMUL, OUTER_RMUL,
                    OUTER_LZERO, OUTER_RZERO] THENC
    PURE_REWRITE_CONV [VECTOR_MUL_LZERO, VECTOR_MUL_RZERO,
                       VECTOR_ADD_LID, VECTOR_ADD_RID, VECTOR_MUL_ASSOC] THENC
    GEN_REWRITE_CONV id [← GSYM VECTOR_MUL_LID] THENC
    PURE_REWRITE_CONV
     [VECTOR_ADD_LDISTRIB, VECTOR_ADD_RDISTRIB, VECTOR_MUL_ASSOC] THENC
    REAL_RAT_REDUCE_CONV THENC PURE_REWRITE_CONV [← GSYM VECTOR_ADD_ASSOC] THENC
    DEPTH_CONV MBASIS_MERGE_CONV THENC
    MBASIS_GROUP_CONV THENC
    GEN_REWRITE_CONV DEPTH_CONV [← GSYM VECTOR_ADD_RDISTRIB] THENC
    REAL_RAT_REDUCE_CONV

  return { OUTER_ACI, MBASIS_GROUP_CONV, OUTER_CANON_CONV }

/- ------------------------------------------------------------------------- -/
/- Iterated operation in order; in the "common" case this agrees with       -/
/- ordinary iteration; outermorphism extension; reversion operation.        -/
/- (clifford.ml 872-979)                                                      -/
/- ------------------------------------------------------------------------- -/

structure Seqiterate where
  seqiterate_EXISTS : thm
  EXISTS_SWAP : thm
  seqiterate : thm
  MINIMAL_IN_INSERT : thm
  SEQITERATE_CLAUSES : thm
  SEQITERATE_ITERATE : thm
  outermorphism : thm
  NEUTRAL_OUTER : thm
  OUTERMORPHISM_MBASIS : thm
  OUTERMORPHISM_MBASIS_EMPTY : thm
  reversion : thm
  deriving Inhabited

@[nospecialize]
def setupSeqiterate [HolBase] (D : CliffordDeps) (BMbasis : Mbasis)
    (BMbasisCons : MbasisCons) : ExceptT String IO Seqiterate := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, LET_TAC, MESON_TAC, SET_RULE, let_CONV, new_definition,
        new_specification, .. } := D
  let { CARD_DELETE, CARD_EQ_0, COND_RAND, COND_RATOR, DELETE_INSERT, DE_MORGAN_THM,
        EMPTY_SUBSET, ETA_AX, FINITE_DELETE, FINITE_INDUCT_DELETE, FINITE_INSERT,
        FINITE_RULES, IMP_CONJ, INFINITE, IN_DELETE, IN_ELIM_THM, IN_INSERT, ITERATE_CLAUSES,
        LET_DEF, LET_END_DEF, LT_ANTISYM, LT_CASES, LT_REFL, MEASURE, MEMBER_NOT_EMPTY,
        MINIMAL, MONO_EXISTS, NOT_INSERT_EMPTY, NOT_IN_EMPTY, RIGHT_FORALL_IMP_THM,
        SELECT_UNIQUE, SKOLEM_THM, WF_MEASURE, WF_REC, minimal, monoidal, neutral, num_WOP,
        .. } := D.core
  let { VECTOR_MUL_LID, VECTOR_MUL_LZERO, VSUM_DELTA, .. } := D.vec
  let { MBASIS_COMPONENT, .. } := BMbasis
  let { OUTER_MBASIS_LSCALAR, OUTER_MBASIS_RSCALAR, .. } := BMbasisCons
  -- @@SCOPE END

  let seqiterate_EXISTS ← prove
   r"!op f. ?h.
        !s. h s = if INFINITE s \/ s = {} then neutral op else
                  let i = minimal x. x IN s in
                  if s = {i} then f(i) else op (f i) (h (s DELETE i))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [INFINITE] THEN
    MATCH_MP_TAC (← MATCH_MP WF_REC (← ISPEC (← q r"CARD:(num->bool)->num") WF_MEASURE)) THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    LET_TAC THEN CONV_TAC (ONCE_DEPTH_CONV let_CONV) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [MEASURE] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [DE_MORGAN_THM]) THEN
    SUBGOAL_THEN (← q r"?i:num. i IN s") MP_TAC THENL
     [ASM_MESON_TAC [MEMBER_NOT_EMPTY], ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN
    ASM_SIMP_TAC [CARD_DELETE, CARD_EQ_0, ← ARITH_RULE (← q r"n - 1 < n <=> ~(n = 0)")])

  let EXISTS_SWAP ← prove
   r"!P. (?f. P f) <=> (?f:A->B->C. P (\b a. f a b))"
   (GEN_TAC THEN EQ_TAC THEN DISCH_THEN CHOOSE_TAC THENL
     [EXISTS_TAC (← q r"\a b. (f:B->A->C) b a") THEN ASM_REWRITE_TAC [ETA_AX],
      ASM_MESON_TAC []])

  let seqiterate ← new_specification ["seqiterate"]
   (← REWRITE_RULE [SKOLEM_THM]
     (← ONCE_REWRITE_RULE [EXISTS_SWAP]
      (← ONCE_REWRITE_RULE [SKOLEM_THM] seqiterate_EXISTS)))

  let MINIMAL_IN_INSERT ← prove
   r"!s i. (!j. j IN s ==> i < j) ==> (minimal j. j IN (i INSERT s)) = i"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [minimal] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN
    REWRITE_TAC [IN_INSERT] THEN ASM_MESON_TAC [LT_ANTISYM])

  let SEQITERATE_CLAUSES ← prove
   r"(!op f. seqiterate op {} f = neutral op) /\
   (!op f i. seqiterate op {i} f = f(i)) /\
   (!op f i s. FINITE s /\ ~(s = {}) /\ (!j. j IN s ==> i < j)
               ==> seqiterate op (i INSERT s) f =
                   op (f i) (seqiterate op s f))"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [seqiterate] THEN
    ASM_SIMP_TAC [NOT_INSERT_EMPTY, INFINITE, FINITE_INSERT, FINITE_RULES] THEN
    ASM_SIMP_TAC [MINIMAL_IN_INSERT, NOT_IN_EMPTY, LET_DEF, LET_END_DEF] THEN
    SUBGOAL_THEN (← q r"~((i:num) IN s)") ASSUME_TAC THENL
     [ASM_MESON_TAC [LT_REFL], ALL_TAC] THEN
    ASM_SIMP_TAC [DELETE_INSERT, ← SET_RULE (← q
     r"~(i IN s) /\ ~(s = {}) ==> (s DELETE i = s) /\ ~(i INSERT s = {i})")])

  let SEQITERATE_ITERATE ← prove
   r"!op f s. monoidal op /\ FINITE s ==> seqiterate op s f = iterate op s f"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_DELETE THEN
    ASM_SIMP_TAC [SEQITERATE_CLAUSES, ITERATE_CLAUSES] THEN
    GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [← GSYM MEMBER_NOT_EMPTY]) THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"i:num") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    FIRST_X_ASSUM (SUBST1_TAC o MATCH_MP (← SET_RULE (← q
     r"i IN s ==> s = i INSERT (s DELETE i)"))) THEN
    ASM_SIMP_TAC [ITERATE_CLAUSES, FINITE_DELETE, IN_DELETE] THEN
    ASM_CASES_TAC (← q r"s DELETE (i:num) = {}") THEN
    ASM_SIMP_TAC [SEQITERATE_CLAUSES, ITERATE_CLAUSES] THENL
     [ASM_MESON_TAC [monoidal], FIRST_X_ASSUM (SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC (CONJUNCTS SEQITERATE_CLAUSES).getLast! THEN
    ASM_REWRITE_TAC [FINITE_DELETE, IN_DELETE] THEN
    ASM_MESON_TAC [LT_ANTISYM, LT_CASES])

  let outermorphism ← new_definition
   r"outermorphism(f:real^N->real^P) (x:real^(N)multivector) =
        vsum {s | s SUBSET 1..dimindex(:N)}
             (\s. x$$s % seqiterate(outer) s (multivec o f o basis))"

  let NEUTRAL_OUTER ← prove
   r"neutral(outer) = mbasis{}"
   (REWRITE_TAC [neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    MESON_TAC [OUTER_MBASIS_LSCALAR, OUTER_MBASIS_RSCALAR])

  let OUTERMORPHISM_MBASIS ← prove
   r"!f:real^M->real^N s.
        s SUBSET 1..dimindex(:M)
        ==> outermorphism f (mbasis s) =
            seqiterate(outer) s (multivec o f o basis)"
   (REWRITE_TAC [outermorphism] THEN SIMP_TAC [MBASIS_COMPONENT] THEN
    ONCE_REWRITE_TAC [COND_RAND] THEN ONCE_REWRITE_TAC [COND_RATOR] THEN
    SIMP_TAC [VECTOR_MUL_LZERO, VSUM_DELTA, IN_ELIM_THM, VECTOR_MUL_LID])

  let OUTERMORPHISM_MBASIS_EMPTY ← prove
   r"!f. outermorphism f (mbasis {}) = mbasis {}"
   (SIMP_TAC [OUTERMORPHISM_MBASIS, EMPTY_SUBSET, SEQITERATE_CLAUSES] THEN
    REWRITE_TAC [NEUTRAL_OUTER])

  let reversion ← new_definition
   r"(reversion:real^(N)multivector->real^(N)multivector) x =
    lambdas s. --(&1) pow ((CARD(s) * (CARD(s) - 1)) DIV 2) * x$$s"

  return { seqiterate_EXISTS, EXISTS_SWAP, seqiterate, MINIMAL_IN_INSERT, SEQITERATE_CLAUSES,
           SEQITERATE_ITERATE, outermorphism, NEUTRAL_OUTER, OUTERMORPHISM_MBASIS,
           OUTERMORPHISM_MBASIS_EMPTY, reversion }

end HolMultiLib.Clifford
