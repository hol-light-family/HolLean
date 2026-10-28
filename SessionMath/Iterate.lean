/- File: SessionMath/Iterate.lean
iterate.ml, each layer built by `initialize` when this module is imported,
in iterate.ml order.  The file's four load-time side effects each have their
own `initialize` at their file position:

  * `parse_as_infix("..",(15,"right"))`             (iterate.ml 16)
  * `prioritize_num()`                               (iterate.ml 1286)
  * `prioritize_real()`                              (iterate.ml 1982)
  * `prioritize_num()`, restoring :num for later     (iterate.ml 3112)

`NUMSEG_CONV`, `EXPAND_NSUM_CONV` and `EXPAND_SUM_CONV` are conversions
(`ioconv`).
-/
import SessionMath.Sets
import HolMath.Iterate

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Simp HolCore.Theorems HolCore.Classic HolCore.Trivia

namespace Session

def ioOkI {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")

/- ---------------------------------------------------------------------- -/
/- Dependencies the old Session named bare but which earlier Session        -/
/- modules export under a bundle accessor.  Each becomes a plain `def`     -/
/- with the old Session's source (its line in the comment).                -/
/- ---------------------------------------------------------------------- -/

/-- `EQ_TRANS` (Session 645). -/
def EQ_TRANS : thm := T.EQ_TRANS
/-- `CONJ_ASSOC` (Session 648). -/
def CONJ_ASSOC : thm := T.CONJ_ASSOC
/-- `CONJ_SYM` (Session 649). -/
def CONJ_SYM : thm := T.CONJ_SYM
/-- `CONJ_ACI` (Session 650). -/
def CONJ_ACI : thm := T.CONJ_ACI
/-- `IMP_IMP` (Session 655). -/
def IMP_IMP : thm := T.IMP_IMP
/-- `IMP_CONJ_ALT` (Session 656). -/
def IMP_CONJ_ALT : thm := T.IMP_CONJ_ALT
/-- `LEFT_OR_DISTRIB` (Session 657). -/
def LEFT_OR_DISTRIB : thm := T.LEFT_OR_DISTRIB
/-- `EXISTS_REFL` (Session 668). -/
def EXISTS_REFL : thm := T.EXISTS_REFL
/-- `UNWIND_THM1` (Session 670). -/
def UNWIND_THM1 : thm := T.UNWIND_THM1
/-- `UNWIND_THM2` (Session 671). -/
def UNWIND_THM2 : thm := T.UNWIND_THM2
/-- `SWAP_FORALL_THM` (Session 674). -/
def SWAP_FORALL_THM : thm := T.SWAP_FORALL_THM
/-- `AND_FORALL_THM` (Session 677). -/
def AND_FORALL_THM : thm := T.AND_FORALL_THM
/-- `RIGHT_IMP_FORALL_THM` (Session 692). -/
def RIGHT_IMP_FORALL_THM : thm := T.RIGHT_IMP_FORALL_THM
/-- `RIGHT_FORALL_IMP_THM` (Session 693). -/
def RIGHT_FORALL_IMP_THM : thm := T.RIGHT_FORALL_IMP_THM
/-- `LEFT_IMP_EXISTS_THM` (Session 694). -/
def LEFT_IMP_EXISTS_THM : thm := T.LEFT_IMP_EXISTS_THM
/-- `LEFT_FORALL_IMP_THM` (Session 695). -/
def LEFT_FORALL_IMP_THM : thm := T.LEFT_FORALL_IMP_THM
/-- `MONO_FORALL` (Session 702). -/
def MONO_FORALL : thm := T.MONO_FORALL
/-- `MONO_EXISTS` (Session 703). -/
def MONO_EXISTS : thm := T.MONO_EXISTS
/-- `FUN_EQ_THM` (Session 959). -/
def FUN_EQ_THM : thm := C.FUN_EQ_THM
/-- `SELECT_UNIQUE` (Session 962). -/
def SELECT_UNIQUE : thm := C.SELECT_UNIQUE
/-- `NOT_IMP` (Session 970). -/
def NOT_IMP : thm := C.NOT_IMP
/-- `NOT_FORALL_THM` (Session 974). -/
def NOT_FORALL_THM : thm := C.NOT_FORALL_THM
/-- `COND_ID` (Session 995). -/
def COND_ID : thm := C.COND_ID
/-- `COND_RAND` (Session 996). -/
def COND_RAND : thm := C.COND_RAND
/-- `COND_RATOR` (Session 997). -/
def COND_RATOR : thm := C.COND_RATOR
/-- `COND_SWAP` (Session 999). -/
def COND_SWAP : thm := C.COND_SWAP
/-- `SKOLEM_THM` (Session 1007). -/
def SKOLEM_THM : thm := C.SKOLEM_THM
/-- `o_THM` (Session 1139: `Tv.o_THM`). -/
def o_THM : thm := Tv.o_THM

/- ====================================================================== -/
/- iterate.ml (hol_lib.ml 100).  Every bundle is an `initialize` constant   -/
/- with a plain `def` accessor, forced at import in `ensureIterate`'s EXACT  -/
/- file order (Session 10149-10178).  The four load-bearing side effects     -/
/- (`..` infix at 16; prioritize_num at 1286; prioritize_real at 1982;       -/
/- prioritize_num restore at 3112) are `initialize`d once-only actions at    -/
/- their file positions.  DO NOT REORDER.                                    -/
/- ====================================================================== -/

/-- The file's ONLY parser declaration, `parse_as_infix("..",(15,"right"))`
    (iterate.ml 16): the eager analogue of Session's `ensureIterateInfix`
    once-only guard, run by an `initialize Unit ←` (as `setupSetsInfixes` is in
    Sets.lean).  Must run BEFORE `numseg` (iterate.ml 18) and any term
    containing `..`. -/
initialize iterateInfixLayer : Unit ← HolMath.Iterate.setupIterateSegmentsInfix

/-- `IterateSegments` (iterate.ml 18-165): `numseg` and the twenty-seven
    segment theorems.  The `..` infix is in force (above). -/
initialize iterateSegmentsLayer : HolMath.Iterate.IterateSegments ←
  ioOkI "setupIterateSegments" (HolMath.Iterate.setupIterateSegments
    new_definition MESON_TAC ASM_MESON_TAC SET_TAC ARITH_RULE
    ARITH_TAC ASM_ARITH_TAC num_INDUCTION
    EXTENSION IN_UNION IN_INSERT IN_SING NOT_IN_EMPTY IN_INTER
    IN_ELIM_THM IN_IMAGE SUBSET DISJOINT FINITE_RULES CARD_CLAUSES
    HAS_SIZE FINITE_SUBSET FINITE_NUMSEG_LE FINITE_INDUCT_STRONG
    FINITE_IMAGE CARD_EQ_BIJECTIONS
    LE_0 LE_CASES LE_REFL LE_TRANS NOT_LE SUC_SUB1 ADD_CLAUSES
    LE_EXISTS LEFT_IMP_EXISTS_THM ARITH MONO_EXISTS).run

def ISeg : HolMath.Iterate.IterateSegments := iterateSegmentsLayer

/-- `NumsegConvPths` (iterate.ml 176-178): the three `MESON` lemmas of
    `NUMSEG_CONV`.  Pure over `ISeg`; `ADD1` used only here. -/
initialize numsegConvPthsLayer : HolMath.Iterate.NumsegConvPths ←
  ioOkI "setupNumsegConvPths" (HolMath.Iterate.setupNumsegConvPths MESON ISeg ADD1).run

def INConv : HolMath.Iterate.NumsegConvPths := numsegConvPthsLayer

/-- `IterateSortSeg` (iterate.ml 196-277): `TOPOLOGICAL_SORT` and
    `FINITE_INT_SEG`.  Pure over `ISeg`; `ADD_SUB` used only in
    `TOPOLOGICAL_SORT`. -/
initialize iterateSortSegLayer : HolMath.Iterate.IterateSortSeg ←
  ioOkI "setupIterateSortSeg" (HolMath.Iterate.setupIterateSortSeg MESON_TAC ASM_MESON_TAC SET_TAC
    SET_RULE ARITH_RULE
    ARITH_TAC ASM_ARITH_TAC INT_ARITH_TAC ASM_INT_ARITH_TAC
    INT_ARITH num_INDUCTION ISeg
    HAS_SIZE_0 HAS_SIZE_SUC MEMBER_NOT_EMPTY MONO_FORALL COND_RAND
    IMP_CONJ_ALT FINITE_SUBSET FINITE_IMAGE EMPTY_GSPEC FINITE_EMPTY
    IMAGE_CLAUSES NOT_IN_EMPTY IN_IMAGE SUBSET IN_ELIM_THM EXTENSION
    INT_OF_NUM_LE INT_OF_NUM_OF_INT INT_SUB_LE
    ARITH ADD_SUB SUC_SUB1 LT_REFL).run

def ISort : HolMath.Iterate.IterateSortSeg := iterateSortSegLayer

/-- `IterateGeneric` (iterate.ml 281-354): the four core `new_definition`s
    `neutral`/`monoidal`/`support`/`iterate` and the ten theorems about them.
    The `iterate` body uses `ITSET` (sets.ml); `CONJ_ACI`/`o_THM`/`COND_RAND`
    used only here. -/
initialize iterateGenericLayer : HolMath.Iterate.IterateGeneric ←
  ioOkI "setupIterateGeneric" (HolMath.Iterate.setupIterateGeneric
    new_definition MESON_TAC ASM_MESON_TAC
    EXTENSION IN_ELIM_THM NOT_IN_EMPTY SUBSET FINITE_SUBSET
    IN_INSERT IN_DELETE IN_IMAGE IN_UNION IN_INTER IN_DIFF IN_SING
    FINITE_RULES CONJ_ACI o_THM COND_RAND).run

def IGen : HolMath.Iterate.IterateGeneric := iterateGenericLayer

/-- `IterateKey1` (iterate.ml 364-539): the first eighteen key lemmas,
    `ITERATE_SUPPORT` through `ITERATE_DELETE`.  Pure over `IGen` plus the
    Sets/Theorems dependencies. -/
initialize iterateKey1Layer : HolMath.Iterate.IterateKey1 ←
  ioOkI "setupIterateKey1" (HolMath.Iterate.setupIterateKey1 MESON_TAC ASM_MESON_TAC SET_TAC
    SET_RULE IGen
    FINITE_RECURSION FINITE_INDUCT_STRONG
    IGen.FINITE_SUPPORT FINITE_INSERT FINITE_UNION FINITE_DIFF FINITE_INTER
    FINITE_DELETE FINITE_SUBSET SUBSET_DIFF INSERT_DELETE FINITE_RULES
    IN_INSERT IN_UNION IN_DELETE NOT_IN_EMPTY UNION_EMPTY
    EXTENSION FORALL_IN_INSERT NOT_INSERT_EMPTY
    REAL_ADD_RID COND_RAND COND_ID AND_FORALL_THM IMP_CONJ
    RIGHT_FORALL_IMP_THM).run

def IK1 : HolMath.Iterate.IterateKey1 := iterateKey1Layer

/-- `IterateKey2` (iterate.ml 546-703): the eleven mapping and congruence
    lemmas, `ITERATE_DELTA` through `ITERATE_OP`.  Pure over `IGen`/`IK1` plus
    the Sets/Pair/Theorems dependencies, the decision procedures, and
    `GEN_BETA_CONV` (for the paired-abstraction product lemma). -/
initialize iterateKey2Layer : HolMath.Iterate.IterateKey2 ←
  ioOkI "setupIterateKey2" (HolMath.Iterate.setupIterateKey2 MESON MESON_TAC ASM_MESON_TAC
    SET_RULE GEN_BETA_CONV IGen IK1
    FINITE_INDUCT_STRONG FINITE_IMAGE FINITE_IMAGE_INJ_EQ
    FINITE_PRODUCT_DEPENDENT FINITE_INSERT IGen.FINITE_SUPPORT
    SURJECTIVE_IFF_INJECTIVE IMAGE_CLAUSES EQ_TRANS DISJOINT CONJ_ASSOC
    IN_INSERT IN_IMAGE IN_INTER IN_ELIM_THM NOT_IN_EMPTY EXTENSION SUBSET
    o_THM o_DEF ETA_AX PAIR_EQ FORALL_PAIR_THM EXISTS_PAIR_THM
    IMP_CONJ RIGHT_FORALL_IMP_THM).run

def IK2 : HolMath.Iterate.IterateKey2 := iterateKey2Layer

/-- `IterateKey3` (iterate.ml 713-887): the ten superset/swap/image/cases
    lemmas and the four numseg-recursion clauses closing the section.  Pure
    over `IGen`, `ISeg`, and `IK1`/`IK2` plus the extra Sets/arith
    dependencies, the decision procedures, `ARITH_RULE`, `INDUCT_TAC`,
    `NUM_REDUCE_CONV` and `num_CONV`. -/
initialize iterateKey3Layer : HolMath.Iterate.IterateKey3 ←
  ioOkI "setupIterateKey3" (HolMath.Iterate.setupIterateKey3 MESON_TAC ASM_MESON_TAC SET_TAC
    SET_RULE ARITH_RULE ARITH_TAC ASM_ARITH_TAC INDUCT_TAC
    NUM_REDUCE_CONV num_CONV IGen ISeg IK1 IK2
    FINITE_INDUCT_STRONG FINITE_UNION FINITE_RESTRICT FINITE_EMPTY FINITE_IMAGE
    FINITE_NUMSEG_LT FINITE_NUMSEG_LE
    NUMSEG_CLAUSES_LT NUMSEG_CLAUSES_LE IMAGE_CLAUSES EQ_TRANS
    IN_ELIM_THM IN_IMAGE IN_INSERT IN_UNION NOT_IN_EMPTY EXTENSION SUBSET
    UNWIND_THM2 NOT_LT LT_REFL MULT_EQ_0 ARITH o_THM o_DEF
    IMP_CONJ RIGHT_FORALL_IMP_THM).run

def IK3 : HolMath.Iterate.IterateKey3 := iterateKey3Layer

/-- `IterateOrdered` (iterate.ml 896-1184): `iterato` (by `new_specification`)
    and its eleven lemmas - the ordered/non-commutative generalisation.  Pure
    over `IGen`, `IK1` and `ISeg`, plus the well-foundedness/Skolem/select
    theorems and `new_specification`/`let_CONV`/`LET_TAC`.  `new_specification`
    is a side-effecting kernel op threaded in here. -/
initialize iterateOrderedLayer : HolMath.Iterate.IterateOrdered ←
  ioOkI "setupIterateOrdered" (HolMath.Iterate.setupIterateOrdered new_specification
    MESON MESON_TAC ASM_MESON_TAC SET_TAC SET_RULE ARITH_RULE ARITH_TAC
    SELECT_RULE let_CONV LET_TAC
    IGen IK1 ISeg
    WF_REC WF_MEASURE MEASURE EXISTS_SWAP_FUN_THM SWAP_FORALL_THM SKOLEM_THM
    num_WF CARD_PSUBSET PSUBSET_ALT SELECT_UNIQUE MEMBER_NOT_EMPTY CONJ_ASSOC
    UNWIND_THM2 EMPTY_GSPEC NOT_IN_EMPTY IN_DIFF IN_SING IN_DELETE IN_ELIM_THM
    IN_INSERT IN_UNIV FINITE_SUBSET FINITE_INSERT FINITE_DELETE FINITE_RESTRICT
    CARD_DELETE CARD_EQ_0 COND_SWAP NOT_EXISTS_THM IMP_IMP RIGHT_IMP_FORALL_THM
    NOT_LE CONJ_SYM UNWIND_THM1).run

def IOrd : HolMath.Iterate.IterateOrdered := iterateOrderedLayer

/-- `IterateSpecial` (iterate.ml 1188-1282): the four iterated operations at
    three types - `nproduct` (:num), `iproduct`/`isum` (:int), `product`
    (:real).  Pure over `IGen` and `IK1`, plus the per-type neutral/monoidal
    identities and the three decision tactics. -/
initialize iterateSpecialLayer : HolMath.Iterate.IterateSpecial ←
  ioOkI "setupIterateSpecial" (HolMath.Iterate.setupIterateSpecial new_definition
    MESON_TAC ARITH_TAC INT_ARITH_TAC REAL_ARITH_TAC
    SELECT_UNIQUE SWAP_FORALL_THM MULT_CLAUSES MULT_EQ_1
    INT_MUL_LID INT_MUL_RID REAL_MUL_LID REAL_MUL_RID
    INT_ADD_LID INT_ADD_RID
    IGen IK1).run

def ISpec : HolMath.Iterate.IterateSpecial := iterateSpecialLayer

/-- `prioritize_num()` (iterate.ml 1286), immediately before `nsum` (1288): the
    eager analogue of Session's `ensureIteratePrioritizeNum` once-only guard.
    It restores `:num` as the default for overloaded symbols so the whole nsum
    half parses bare numerals as `:num`.  `:num` is already in force (int.ml
    2765 ran during the Int chain), so this is a reaffirmation, but one of the
    file's four LOAD-BEARING prioritize calls, reproduced at its true position
    for fidelity. -/
initialize iteratePrioritizeNumLayer : Unit ←
  ioOkI "iterate.ml 1286 prioritize_num" (HolMath.Int.prioritize_num prioritize_overload).run

/-- `IterateNsum1` (iterate.ml 1288-1461): the `nsum` definition,
    `NEUTRAL_ADD`/`MONOIDAL_ADD`, and the twenty-five theorems
    `NSUM_DEGENERATE` to `NSUM_SWAP`.  Runs after the 1286 prioritize_num. -/
initialize iterateNsum1Layer : HolMath.Iterate.IterateNsum1 ←
  ioOkI "setupIterateNsum1" (HolMath.Iterate.setupIterateNsum1 new_definition
    MESON_TAC ASM_MESON_TAC SET_TAC ARITH_TAC ARITH_RULE
    IGen IK1 IK2 IK3
    SELECT_UNIQUE ADD_CLAUSES MULT_CLAUSES MULT_SYM MULT_EQ_0
    LEFT_ADD_DISTRIB CARD_CLAUSES FINITE_RULES FINITE_INDUCT_STRONG
    NOT_IN_EMPTY IN_INSERT IN_DELETE FINITE_DELETE LE_REFL LE_ADD2
    LTE_ADD2 LE_0 SWAP_FORALL_THM ETA_AX MEMBER_NOT_EMPTY LT_IMP_LE
    REAL_LT_IMP_LE IMP_CONJ RIGHT_FORALL_IMP_THM).run

def IN1 : HolMath.Iterate.IterateNsum1 := iterateNsum1Layer

/-- `IterateNsum2` (iterate.ml 1462-1745): `NSUM_IMAGE` to `NSUM_CASES` - the
    image/superset/restriction lemmas, the counting lemmas, subset
    monotonicity, the transfer lemmas, and `NSUM_UNIONS_NONZERO`.  Pure over
    `IN1` and the `IterateKey*` generics. -/
initialize iterateNsum2Layer : HolMath.Iterate.IterateNsum2 ←
  ioOkI "setupIterateNsum2" (HolMath.Iterate.setupIterateNsum2 MESON_TAC ASM_MESON_TAC SET_TAC
    ARITH_TAC ARITH_RULE IGen IK2 IK3 IN1
    EQ_TRANS DISJOINT FINITE_INDUCT_STRONG MULT_CLAUSES MULT_AC
    LE_MULT_RCANCEL LE_MULT_LCANCEL LE_RDIV_EQ LE_REFL LE_TRANS
    LT_IMP_LE MEMBER_NOT_EMPTY CARD_EQ_0 SING_SUBSET IN_DIFF
    SUBSET_UNION LE LTE_TRANS FINITE_DIFF FINITE_INTER
    FINITE_RESTRICT FINITE_UNIONS FINITE_SUBSET UNION_COMM UNIONS_0
    UNIONS_INSERT IN_UNION IN_INTER IN_UNIONS IN_INSERT IN_ELIM_THM
    FORALL_IN_IMAGE SUBSET IMP_CONJ CONJ_ASSOC).run

def IN2 : HolMath.Iterate.IterateNsum2 := iterateNsum2Layer

/-- `IterateNsum3` (iterate.ml 1746-1917): closure/relation induction, the
    numeral-segment theorems, modular arithmetic, `CONG_NSUM`, and the trailing
    `extend_basic_congs` congruence registration (a side effect, iterate.ml
    1917).  Pure over `IN1`/`IN2`, `ISeg`, and `IK1`/`IK3`. -/
initialize iterateNsum3Layer : HolMath.Iterate.IterateNsum3 ←
  ioOkI "setupIterateNsum3" (HolMath.Iterate.setupIterateNsum3 MESON_TAC ASM_MESON_TAC INDUCT_TAC
    ARITH_TAC ARITH_RULE extend_basic_congs NUMBER_RULE
    IK1 IK3 ISeg IN1 IN2
    FINITE_INDUCT_STRONG ISeg.FINITE_NUMSEG ISeg.NUMSEG_SING ETA_AX MOD_ZERO
    MOD_ADD_MOD MOD_MOD_REFL SUC_SUB1 SUB_ADD ADD_CLAUSES LT_REFL
    NOT_LT LE_TRANS EQ_ADD_RCANCEL o_DEF ISeg.IN_NUMSEG IN_ELIM_THM
    IMP_CONJ RIGHT_FORALL_IMP_THM).run

def IN3 : HolMath.Iterate.IterateNsum3 := iterateNsum3Layer

/-- `IterateNsumCard` (iterate.ml 1920-1978): `CARD_UNIONS_IMAGE`,
    `CARD_UNIONS`, and `EXPAND_NSUM_CONV` (with its three proformas).  Pure
    over `IN1`/`IN3`. -/
initialize iterateNsumCardLayer : HolMath.Iterate.IterateNsumCard ←
  ioOkI "setupIterateNsumCard" (HolMath.Iterate.setupIterateNsumCard SET_TAC
    NUM_LT_CONV NUM_LE_CONV NUM_ADD_CONV IN1 IN3
    CARD_UNION_EQ FINITE_INDUCT_STRONG FINITE_IMAGE FINITE_UNIONS
    FINITE_UNION IMAGE_CLAUSES IMAGE_ID INTER_UNIONS UNIONS_0
    UNIONS_INSERT NOT_IN_EMPTY IN_INSERT CARD_CLAUSES ETA_AX
    IMP_CONJ).run

def INCard : HolMath.Iterate.IterateNsumCard := iterateNsumCardLayer

/-- `prioritize_real()` (iterate.ml 1982), immediately before `sum` (1984) -
    THE FILE'S DEFINING HAZARD, the eager analogue of Session's
    `ensureIterateSumPrioritizeReal` guard.  It makes `:real` the default for
    overloaded symbols, so from here every bare numeral parses as `:real`, not
    `:num`.  Were `sum` parsed under `:num` priority it would COLLIDE with
    `nsum`.  Runs AFTER the nsum bundles (last is `INCard`, iterate.ml 1978)
    and BEFORE any `sum` bundle. -/
initialize iterateSumPrioritizeRealLayer : Unit ← prioritize_real

/-- `IterateSum1` (iterate.ml 1984-2211): the `sum` definition,
    `NEUTRAL_REAL_ADD`/`MONOIDAL_REAL_ADD`, and the core
    algebra/ordering/bounds group `SUM_DEGENERATE` to `SUM_SWAP`.  Runs after
    the 1982 prioritize_real so bare numerals parse `:real`. -/
initialize iterateSum1Layer : HolMath.Iterate.IterateSum1 ←
  ioOkI "setupIterateSum1" (HolMath.Iterate.setupIterateSum1
    new_definition MESON_TAC ASM_MESON_TAC MESON SET_TAC SET_RULE
    REAL_ARITH3 REAL_ARITH_TAC2 IGen IK1 IK2 IK3
    SELECT_UNIQUE REAL_ADD_LID REAL_ADD_RID REAL_MUL_LZERO
    REAL_MUL_RZERO REAL_MUL_SYM REAL_ENTIRE REAL_ADD_LDISTRIB
    REAL_LE_REFL REAL_LE_ADD2 REAL_LTE_ADD2 REAL_LET_TRANS
    REAL_LE_TRANS REAL_LE_ANTISYM REAL_ABS_NUM REAL_OF_NUM_SUC
    REAL_EQ_SUB_LADD REAL_NEG_0 REAL_LT_IMP_LE real_sub
    FINITE_RULES FINITE_INDUCT_STRONG FINITE_DELETE NOT_IN_EMPTY
    IN_INSERT IN_DELETE IN_ELIM_THM MEMBER_NOT_EMPTY CARD_CLAUSES
    ETA_AX SWAP_FORALL_THM RIGHT_FORALL_IMP_THM IMP_CONJ).run

def IS1 : HolMath.Iterate.IterateSum1 := iterateSum1Layer

/-- `IterateSum2` (iterate.ml 2219-2598): the second `sum` bundle -
    image/superset/count/group/subset/product/general/closure lemmas,
    `SUM_IMAGE` to `REAL_OF_NUM_SUM_GEN`.  Pure over `IGen`/`IK1`/`IK2`/`IK3`
    and `IS1`; still under prioritize_real. -/
initialize iterateSum2Layer : HolMath.Iterate.IterateSum2 ←
  ioOkI "setupIterateSum2" (HolMath.Iterate.setupIterateSum2
    MESON_TAC ASM_MESON_TAC SET_TAC SET_RULE REAL_ARITH3 REAL_ARITH_TAC2
    IGen IK1 IK2 IK3 IS1
    IN1.NEUTRAL_ADD FINITE_INDUCT_STRONG FINITE_IMAGE FINITE_RESTRICT
    FINITE_DIFF FINITE_INTER FINITE_UNIONS FINITE_SUBSET IN_INSERT
    IN_ELIM_THM IN_DIFF IN_INTER IN_UNION IN_UNIONS FORALL_IN_IMAGE
    SING_SUBSET SUBSET SUBSET_UNION UNION_COMM UNIONS_0
    UNIONS_INSERT DELETE EQ_TRANS DISJOINT CONJ_ASSOC IMP_CONJ
    RIGHT_FORALL_IMP_THM LEFT_IMP_EXISTS_THM o_THM MEMBER_NOT_EMPTY
    REAL_LE_TRANS REAL_LTE_TRANS REAL_EQ_IMP_LE REAL_LE_RMUL
    REAL_LE_RNEG REAL_LE_REFL REAL_ADD_LID REAL_MUL_RID
    REAL_OF_NUM_ADD REAL_OF_NUM_MUL REAL_OF_NUM_EQ REAL_DIV_LMUL
    REAL_LT_IMP_LE HAS_SIZE HAS_SIZE_0 MULT_AC IN1.NSUM_CLAUSES
    IN1.NSUM_SUPPORT).run

def IS2 : HolMath.Iterate.IterateSum2 := iterateSum2Layer

/-- `IterateSum3` (iterate.ml 2599-2778): `sum` over numseg intervals
    (`SUM_ADD_NUMSEG` to `REAL_OF_NUM_SUM_NUMSEG`) and partial summation
    (`SUM_PARTIAL_SUC` to `SUM_COMBINE_L`).  Pure over `ISeg`, `IK3`, and
    `IS1`/`IS2`; still under prioritize_real. -/
initialize iterateSum3Layer : HolMath.Iterate.IterateSum3 ←
  ioOkI "setupIterateSum3" (HolMath.Iterate.setupIterateSum3
    MESON_TAC REAL_ARITH3 REAL_ARITH_TAC2 ARITH_TAC
    ASM_ARITH_TAC ARITH_RULE INDUCT_TAC IK3 ISeg IS1 IS2
    ISeg.FINITE_NUMSEG ISeg.IN_NUMSEG ISeg.NUMSEG_SING
    ISeg.NUMSEG_ADD_SPLIT ISeg.NUMSEG_OFFSET_IMAGE ISeg.NUMSEG_LREC
    ISeg.DISJOINT_NUMSEG LE LE_TRANS NOT_LT NOT_LE LT_REFL
    SUC_SUB1 SUB_ADD ADD_CLAUSES ADD1 ADD_SUB EQ_ADD_RCANCEL
    o_DEF REAL_SUB_REFL REAL_MUL_RZERO REAL_NEG_SUB REAL_NEG_0
    EXTENSION IN_INTER IN_UNION NOT_IN_EMPTY).run

def IS3 : HolMath.Iterate.IterateSum3 := iterateSum3Layer

/-- `IterateSum4` (iterate.ml 2779-2854): the `sum` congruences (`SUM_CONG`,
    registered via `extend_basic_congs` - a side effect, iterate.ml 2793),
    `EXPAND_SUM_CONV` (a conversion), and the `REAL_SUB_POW*` rearrangements.
    Pure over `IS1`/`IS2`/`IS3`; still under prioritize_real. -/
initialize iterateSum4Layer : HolMath.Iterate.IterateSum4 ←
  ioOkI "setupIterateSum4" (HolMath.Iterate.setupIterateSum4
    extend_basic_congs NUM_LT_CONV NUM_LE_CONV NUM_ADD_CONV
    REAL_ARITH3 ARITH_RULE IS1 IS2 IS3
    IN_ELIM_THM ISeg.IN_NUMSEG REAL_POW_ONE REAL_MUL_RID REAL_MUL_LID
    REAL_MUL_LNEG REAL_NEG_SUB real_pow ADD1 LE_0 SUB_0 SUB_ADD
    SUB_REFL).run

def IS4 : HolMath.Iterate.IterateSum4 := iterateSum4Layer

/-- `IterateSum5` (iterate.ml 2855-3108): real polynomial functions.  Pure over
    `IS1`/`IS2`/`IS3`/`IS4` and `ISeg`; still under prioritize_real (iterate.ml
    3112's restore is a later point). -/
initialize iterateSum5Layer : HolMath.Iterate.IterateSum5 ←
  ioOkI "setupIterateSum5" (HolMath.Iterate.setupIterateSum5
    new_definition MESON_TAC ASM_MESON_TAC MESON SET_RULE
    REAL_ARITH3 REAL_ARITH_TAC2 ARITH_RULE ARITH_TAC ASM_ARITH_TAC
    INDUCT_TAC IS1 IS2 IS3 IS4 ISeg
    ISeg.FINITE_NUMSEG FINITE_EMPTY CARD_CLAUSES FINITE_RULES
    real_INFINITE INFINITE real_pow REAL_POW_ADD REAL_POW_1
    REAL_MUL_RID REAL_MUL_LZERO REAL_MUL_ASSOC REAL_ADD_RID
    REAL_ADD_LID REAL_ADD_RDISTRIB REAL_ADD_LDISTRIB REAL_MUL_SYM
    REAL_ENTIRE REAL_SUB_0 REAL_SUB_RZERO REAL_SUB_REFL
    REAL_SUB_LDISTRIB REAL_NEG_NEG REAL_MUL_LNEG REAL_MUL_LID
    REAL_MUL_RZERO ARITH EQ_TRANS IMP_CONJ IMP_CONJ_ALT
    SWAP_FORALL_THM RIGHT_FORALL_IMP_THM LE LE_0 LE_1 LE_REFL
    NOT_FORALL_THM NOT_IMP NOT_EXISTS_THM DE_MORGAN_THM
    LEFT_OR_DISTRIB LEFT_IMP_EXISTS_THM UNWIND_THM2 IN_SING
    ISeg.IN_NUMSEG IN_ELIM_THM IN_ELIM_PAIR_THM FORALL_IN_GSPEC
    UNIV_GSPEC EMPTY_GSPEC FINITE_INSERT FINITE_INDUCT_STRONG
    FORALL_IN_INSERT COND_RAND COND_RATOR EXTENSION ETA_AX ADD1
    ADD_CLAUSES ADD_SUB ADD_EQ_0 ARITH_EQ SUC_SUB1 ADD_SYM
    I_DEF o_DEF FUN_EQ_THM EXISTS_REFL LEFT_FORALL_IMP_THM
    CONTRAPOS_THM REAL_MUL_AC MEMBER_NOT_EMPTY real_sub).run

def IS5 : HolMath.Iterate.IterateSum5 := iterateSum5Layer

/-- `prioritize_num()` (iterate.ml 3112), under the banner "Make natural
    numbers the default again": the eager analogue of Session's
    `ensureIteratePrioritizeNumRestore` guard.  Half of a pair with the 1982
    prioritize_real: between them a bare numeral parses `:real`; from here it
    parses `:num` again.  Omitting it would silently mistype every later file.
    The real-half bundles `IS1`-`IS5` are already forced, so their theorems
    keep the `:real` parse they were built with; only the default for later
    parsing flips. -/
initialize iteratePrioritizeNumRestoreLayer : Unit ←
  ioOkI "iterate.ml 3112 prioritize_num restore" (HolMath.Int.prioritize_num prioritize_overload).run

/-- `ensureIterate` (Session 10149): all of iterate.ml's load-bearing parser
    state, prioritize side effects and bundles are set up by the `initialize`s
    above, run in `ensureIterate`'s exact file order (Session 10149-10178) at
    import.  Kept as a no-op accessor. -/
def ensureIterate : IO Unit := pure ()

/- ---------------------------------------------------------------------- -/
/- iterate.ml bare theorem re-exports (same names/order as Session).       -/
/- ---------------------------------------------------------------------- -/
-- IterateSegments (iterate.ml 18-165)
def numseg                : thm := ISeg.numseg
def FINITE_NUMSEG         : thm := ISeg.FINITE_NUMSEG
def NUMSEG_COMBINE_R      : thm := ISeg.NUMSEG_COMBINE_R
def NUMSEG_COMBINE_L      : thm := ISeg.NUMSEG_COMBINE_L
def NUMSEG_LREC           : thm := ISeg.NUMSEG_LREC
def NUMSEG_RREC           : thm := ISeg.NUMSEG_RREC
def NUMSEG_REC            : thm := ISeg.NUMSEG_REC
def IN_NUMSEG             : thm := ISeg.IN_NUMSEG
def IN_NUMSEG_0           : thm := ISeg.IN_NUMSEG_0
def NUMSEG_SING           : thm := ISeg.NUMSEG_SING
def NUMSEG_EMPTY          : thm := ISeg.NUMSEG_EMPTY
def EMPTY_NUMSEG          : thm := ISeg.EMPTY_NUMSEG
def FINITE_SUBSET_NUMSEG  : thm := ISeg.FINITE_SUBSET_NUMSEG
def CARD_NUMSEG_LEMMA     : thm := ISeg.CARD_NUMSEG_LEMMA
def CARD_NUMSEG           : thm := ISeg.CARD_NUMSEG
def HAS_SIZE_NUMSEG       : thm := ISeg.HAS_SIZE_NUMSEG
def CARD_NUMSEG_1         : thm := ISeg.CARD_NUMSEG_1
def HAS_SIZE_NUMSEG_1     : thm := ISeg.HAS_SIZE_NUMSEG_1
def NUMSEG_CLAUSES        : thm := ISeg.NUMSEG_CLAUSES
def FINITE_INDEX_NUMSEG   : thm := ISeg.FINITE_INDEX_NUMSEG
def FINITE_INDEX_NUMBERS  : thm := ISeg.FINITE_INDEX_NUMBERS
def INTER_NUMSEG          : thm := ISeg.INTER_NUMSEG
def DISJOINT_NUMSEG       : thm := ISeg.DISJOINT_NUMSEG
def NUMSEG_ADD_SPLIT      : thm := ISeg.NUMSEG_ADD_SPLIT
def NUMSEG_OFFSET_IMAGE   : thm := ISeg.NUMSEG_OFFSET_IMAGE
def SUBSET_NUMSEG         : thm := ISeg.SUBSET_NUMSEG
def NUMSEG_LE             : thm := ISeg.NUMSEG_LE
def NUMSEG_LT             : thm := ISeg.NUMSEG_LT
-- NumsegConvPths (iterate.ml 176-178)
def NUMSEG_CONV_pth_0     : thm := INConv.pth_0
def NUMSEG_CONV_pth_1     : thm := INConv.pth_1
def NUMSEG_CONV_pth_2     : thm := INConv.pth_2
/-- `NUMSEG_CONV` (iterate.ml 175-190) fully applied: the CONVERSION evaluating
    `m..n` for specific numerals `m`, `n`, producing `|- m..n = {m,...,n}`.
    Assembled from the three numeral conversions and the `INConv` proformas;
    the template terms are the `INConv` fields (DERIVED from `pth_2`, not
    re-parsed, so the head constant is term-equal to the one the recursion
    destructures).  A forcing probe proves nothing about a conversion, so this
    is exposed for the test's behavioural driver. -/
def NUMSEG_CONV : ioconv :=
  HolMath.Iterate.NUMSEG_CONV NUM_LT_CONV NUM_LE_CONV NUM_SUC_CONV
    INConv INConv.ns_tm INConv.m_tm INConv.n_tm
-- IterateSortSeg (iterate.ml 196-277)
def TOPOLOGICAL_SORT      : thm := ISort.TOPOLOGICAL_SORT
def FINITE_INT_SEG        : thm := ISort.FINITE_INT_SEG
-- IterateGeneric (iterate.ml 281-354)
def neutral               : thm := IGen.neutral
def monoidal              : thm := IGen.monoidal
def MONOIDAL_AC           : thm := IGen.MONOIDAL_AC
def support               : thm := IGen.support
def iterate               : thm := IGen.iterate
def IN_SUPPORT            : thm := IGen.IN_SUPPORT
def SUPPORT_SUPPORT       : thm := IGen.SUPPORT_SUPPORT
def SUPPORT_EMPTY         : thm := IGen.SUPPORT_EMPTY
def SUPPORT_SUBSET        : thm := IGen.SUPPORT_SUBSET
def FINITE_SUPPORT        : thm := IGen.FINITE_SUPPORT
def SUPPORT_CLAUSES       : thm := IGen.SUPPORT_CLAUSES
def SUPPORT_DELTA         : thm := IGen.SUPPORT_DELTA
def FINITE_SUPPORT_DELTA  : thm := IGen.FINITE_SUPPORT_DELTA
-- IterateKey1 (iterate.ml 364-539)
def ITERATE_SUPPORT          : thm := IK1.ITERATE_SUPPORT
def ITERATE_EXPAND_CASES     : thm := IK1.ITERATE_EXPAND_CASES
def ITERATE_CLAUSES_GEN      : thm := IK1.ITERATE_CLAUSES_GEN
def ITERATE_CLAUSES          : thm := IK1.ITERATE_CLAUSES
def ITERATE_UNION            : thm := IK1.ITERATE_UNION
def ITERATE_UNION_GEN        : thm := IK1.ITERATE_UNION_GEN
def ITERATE_DIFF             : thm := IK1.ITERATE_DIFF
def ITERATE_DIFF_GEN         : thm := IK1.ITERATE_DIFF_GEN
def ITERATE_INCL_EXCL        : thm := IK1.ITERATE_INCL_EXCL
def ITERATE_CLOSED           : thm := IK1.ITERATE_CLOSED
def ITERATE_RELATED          : thm := IK1.ITERATE_RELATED
def ITERATE_EQ_NEUTRAL       : thm := IK1.ITERATE_EQ_NEUTRAL
def ITERATE_SING             : thm := IK1.ITERATE_SING
def ITERATE_CLOSED_NONEMPTY  : thm := IK1.ITERATE_CLOSED_NONEMPTY
def ITERATE_RELATED_NONEMPTY : thm := IK1.ITERATE_RELATED_NONEMPTY
def ITERATE_DELETE           : thm := IK1.ITERATE_DELETE
-- IterateKey2 (iterate.ml 546-703)
def ITERATE_DELTA                : thm := IK2.ITERATE_DELTA
def ITERATE_IMAGE                : thm := IK2.ITERATE_IMAGE
def ITERATE_BIJECTION            : thm := IK2.ITERATE_BIJECTION
def ITERATE_ITERATE_PRODUCT      : thm := IK2.ITERATE_ITERATE_PRODUCT
def ITERATE_EQ                   : thm := IK2.ITERATE_EQ
def ITERATE_RESTRICT_SET         : thm := IK2.ITERATE_RESTRICT_SET
def ITERATE_EQ_GENERAL           : thm := IK2.ITERATE_EQ_GENERAL
def ITERATE_EQ_GENERAL_INVERSES  : thm := IK2.ITERATE_EQ_GENERAL_INVERSES
def ITERATE_INJECTION            : thm := IK2.ITERATE_INJECTION
def ITERATE_UNION_NONZERO        : thm := IK2.ITERATE_UNION_NONZERO
def ITERATE_OP                   : thm := IK2.ITERATE_OP
-- IterateKey3 (iterate.ml 713-887)
def ITERATE_SUPERSET             : thm := IK3.ITERATE_SUPERSET
def ITERATE_UNIV                 : thm := IK3.ITERATE_UNIV
def ITERATE_SWAP                 : thm := IK3.ITERATE_SWAP
def ITERATE_IMAGE_NONZERO        : thm := IK3.ITERATE_IMAGE_NONZERO
def ITERATE_IMAGE_GEN            : thm := IK3.ITERATE_IMAGE_GEN
def ITERATE_CASES                : thm := IK3.ITERATE_CASES
def ITERATE_OP_GEN               : thm := IK3.ITERATE_OP_GEN
def ITERATE_CLAUSES_NUMSEG       : thm := IK3.ITERATE_CLAUSES_NUMSEG
def ITERATE_CLAUSES_NUMSEG_LT    : thm := IK3.ITERATE_CLAUSES_NUMSEG_LT
def ITERATE_CLAUSES_NUMSEG_LE    : thm := IK3.ITERATE_CLAUSES_NUMSEG_LE
def ITERATE_PAIR                 : thm := IK3.ITERATE_PAIR
def ITERATE_REFLECT              : thm := IK3.ITERATE_REFLECT
-- IterateOrdered (iterate.ml 896-1184)
def iterato                      : thm := IOrd.iterato
def ITERATO_SUPPORT              : thm := IOrd.ITERATO_SUPPORT
def ITERATO_EXPAND_CASES         : thm := IOrd.ITERATO_EXPAND_CASES
def ITERATO_CLAUSES_GEN          : thm := IOrd.ITERATO_CLAUSES_GEN
def ITERATO_CLAUSES              : thm := IOrd.ITERATO_CLAUSES
def ITERATO_CLAUSES_EXISTS       : thm := IOrd.ITERATO_CLAUSES_EXISTS
def ITERATO_EQ                   : thm := IOrd.ITERATO_EQ
def ITERATO_INDUCT               : thm := IOrd.ITERATO_INDUCT
def ITERATO_CLOSED               : thm := IOrd.ITERATO_CLOSED
def ITERATO_ITERATE              : thm := IOrd.ITERATO_ITERATE
def ITERATO_CLAUSES_NUMSEG_LEFT  : thm := IOrd.ITERATO_CLAUSES_NUMSEG_LEFT
-- IterateSpecial (iterate.ml 1188-1282)
def nproduct          : thm := ISpec.nproduct
def NEUTRAL_MUL       : thm := ISpec.NEUTRAL_MUL
def MONOIDAL_MUL      : thm := ISpec.MONOIDAL_MUL
def NPRODUCT_CLAUSES  : thm := ISpec.NPRODUCT_CLAUSES
def iproduct          : thm := ISpec.iproduct
def NEUTRAL_INT_MUL   : thm := ISpec.NEUTRAL_INT_MUL
def MONOIDAL_INT_MUL  : thm := ISpec.MONOIDAL_INT_MUL
def IPRODUCT_CLAUSES  : thm := ISpec.IPRODUCT_CLAUSES
def product           : thm := ISpec.product
def NEUTRAL_REAL_MUL  : thm := ISpec.NEUTRAL_REAL_MUL
def MONOIDAL_REAL_MUL : thm := ISpec.MONOIDAL_REAL_MUL
def PRODUCT_CLAUSES   : thm := ISpec.PRODUCT_CLAUSES
def isum              : thm := ISpec.isum
def NEUTRAL_INT_ADD   : thm := ISpec.NEUTRAL_INT_ADD
def MONOIDAL_INT_ADD  : thm := ISpec.MONOIDAL_INT_ADD
def ISUM_CLAUSES      : thm := ISpec.ISUM_CLAUSES
-- IterateNsum1 (iterate.ml 1288-1461)
def nsum                 : thm := IN1.nsum
def NEUTRAL_ADD          : thm := IN1.NEUTRAL_ADD
def MONOIDAL_ADD         : thm := IN1.MONOIDAL_ADD
def NSUM_DEGENERATE      : thm := IN1.NSUM_DEGENERATE
def NSUM_CLAUSES         : thm := IN1.NSUM_CLAUSES
def NSUM_UNION           : thm := IN1.NSUM_UNION
def NSUM_DIFF            : thm := IN1.NSUM_DIFF
def NSUM_INCL_EXCL       : thm := IN1.NSUM_INCL_EXCL
def NSUM_SUPPORT         : thm := IN1.NSUM_SUPPORT
def NSUM_ADD             : thm := IN1.NSUM_ADD
def NSUM_ADD_GEN         : thm := IN1.NSUM_ADD_GEN
def NSUM_EQ_0            : thm := IN1.NSUM_EQ_0
def NSUM_0               : thm := IN1.NSUM_0
def NSUM_LMUL            : thm := IN1.NSUM_LMUL
def NSUM_RMUL            : thm := IN1.NSUM_RMUL
def NSUM_LE              : thm := IN1.NSUM_LE
def NSUM_LT              : thm := IN1.NSUM_LT
def NSUM_LT_ALL          : thm := IN1.NSUM_LT_ALL
def NSUM_EQ              : thm := IN1.NSUM_EQ
def NSUM_CONST           : thm := IN1.NSUM_CONST
def NSUM_POS_BOUND       : thm := IN1.NSUM_POS_BOUND
def NSUM_EQ_0_IFF        : thm := IN1.NSUM_EQ_0_IFF
def NSUM_POS_LT          : thm := IN1.NSUM_POS_LT
def NSUM_POS_LT_ALL      : thm := IN1.NSUM_POS_LT_ALL
def NSUM_DELETE          : thm := IN1.NSUM_DELETE
def NSUM_SING            : thm := IN1.NSUM_SING
def NSUM_DELTA           : thm := IN1.NSUM_DELTA
def NSUM_SWAP            : thm := IN1.NSUM_SWAP
-- IterateNsum2 (iterate.ml 1462-1745)
def NSUM_IMAGE               : thm := IN2.NSUM_IMAGE
def NSUM_SUPERSET            : thm := IN2.NSUM_SUPERSET
def NSUM_UNIV                : thm := IN2.NSUM_UNIV
def NSUM_UNION_RZERO         : thm := IN2.NSUM_UNION_RZERO
def NSUM_UNION_LZERO         : thm := IN2.NSUM_UNION_LZERO
def NSUM_RESTRICT            : thm := IN2.NSUM_RESTRICT
def NSUM_BOUND               : thm := IN2.NSUM_BOUND
def NSUM_BOUND_GEN           : thm := IN2.NSUM_BOUND_GEN
def NSUM_BOUND_LT            : thm := IN2.NSUM_BOUND_LT
def NSUM_BOUND_LT_ALL        : thm := IN2.NSUM_BOUND_LT_ALL
def NSUM_BOUND_LT_GEN        : thm := IN2.NSUM_BOUND_LT_GEN
def NSUM_UNION_EQ            : thm := IN2.NSUM_UNION_EQ
def NSUM_EQ_SUPERSET         : thm := IN2.NSUM_EQ_SUPERSET
def NSUM_RESTRICT_SET        : thm := IN2.NSUM_RESTRICT_SET
def NSUM_NSUM_RESTRICT       : thm := IN2.NSUM_NSUM_RESTRICT
def CARD_EQ_NSUM             : thm := IN2.CARD_EQ_NSUM
def NSUM_MULTICOUNT_GEN      : thm := IN2.NSUM_MULTICOUNT_GEN
def NSUM_MULTICOUNT          : thm := IN2.NSUM_MULTICOUNT
def NSUM_IMAGE_GEN           : thm := IN2.NSUM_IMAGE_GEN
def NSUM_GROUP               : thm := IN2.NSUM_GROUP
def NSUM_GROUP_RELATION      : thm := IN2.NSUM_GROUP_RELATION
def NSUM_SUBSET              : thm := IN2.NSUM_SUBSET
def NSUM_SUBSET_SIMPLE       : thm := IN2.NSUM_SUBSET_SIMPLE
def NSUM_LE_GEN              : thm := IN2.NSUM_LE_GEN
def NSUM_MUL_BOUND           : thm := IN2.NSUM_MUL_BOUND
def NSUM_IMAGE_NONZERO       : thm := IN2.NSUM_IMAGE_NONZERO
def NSUM_BIJECTION           : thm := IN2.NSUM_BIJECTION
def NSUM_NSUM_PRODUCT        : thm := IN2.NSUM_NSUM_PRODUCT
def NSUM_EQ_GENERAL          : thm := IN2.NSUM_EQ_GENERAL
def NSUM_EQ_GENERAL_INVERSES : thm := IN2.NSUM_EQ_GENERAL_INVERSES
def NSUM_INJECTION           : thm := IN2.NSUM_INJECTION
def NSUM_UNION_NONZERO       : thm := IN2.NSUM_UNION_NONZERO
def NSUM_UNIONS_NONZERO      : thm := IN2.NSUM_UNIONS_NONZERO
def NSUM_CASES               : thm := IN2.NSUM_CASES
-- IterateNsum3 (iterate.ml 1746-1917)
def NSUM_CLOSED              : thm := IN3.NSUM_CLOSED
def NSUM_RELATED             : thm := IN3.NSUM_RELATED
def NSUM_CLOSED_NONEMPTY     : thm := IN3.NSUM_CLOSED_NONEMPTY
def NSUM_RELATED_NONEMPTY    : thm := IN3.NSUM_RELATED_NONEMPTY
def NSUM_ADD_NUMSEG          : thm := IN3.NSUM_ADD_NUMSEG
def NSUM_LE_NUMSEG           : thm := IN3.NSUM_LE_NUMSEG
def NSUM_EQ_NUMSEG           : thm := IN3.NSUM_EQ_NUMSEG
def NSUM_CONST_NUMSEG        : thm := IN3.NSUM_CONST_NUMSEG
def NSUM_EQ_0_NUMSEG         : thm := IN3.NSUM_EQ_0_NUMSEG
def NSUM_EQ_0_IFF_NUMSEG     : thm := IN3.NSUM_EQ_0_IFF_NUMSEG
def NSUM_TRIV_NUMSEG         : thm := IN3.NSUM_TRIV_NUMSEG
def NSUM_SING_NUMSEG         : thm := IN3.NSUM_SING_NUMSEG
def NSUM_CLAUSES_NUMSEG      : thm := IN3.NSUM_CLAUSES_NUMSEG
def NSUM_CLAUSES_NUMSEG_LT   : thm := IN3.NSUM_CLAUSES_NUMSEG_LT
def NSUM_CLAUSES_NUMSEG_LE   : thm := IN3.NSUM_CLAUSES_NUMSEG_LE
def NSUM_SWAP_NUMSEG         : thm := IN3.NSUM_SWAP_NUMSEG
def NSUM_ADD_SPLIT           : thm := IN3.NSUM_ADD_SPLIT
def NSUM_OFFSET              : thm := IN3.NSUM_OFFSET
def NSUM_OFFSET_0            : thm := IN3.NSUM_OFFSET_0
def NSUM_CLAUSES_LEFT        : thm := IN3.NSUM_CLAUSES_LEFT
def NSUM_CLAUSES_RIGHT       : thm := IN3.NSUM_CLAUSES_RIGHT
def NSUM_PAIR                : thm := IN3.NSUM_PAIR
def NSUM_REFLECT             : thm := IN3.NSUM_REFLECT
def MOD_NSUM_MOD             : thm := IN3.MOD_NSUM_MOD
def MOD_NSUM_MOD_NUMSEG      : thm := IN3.MOD_NSUM_MOD_NUMSEG
def CONG_NSUM                : thm := IN3.CONG_NSUM
def NSUM_CONG                : thm := IN3.NSUM_CONG
-- IterateNsumCard (iterate.ml 1920-1978)
def CARD_UNIONS_IMAGE        : thm := INCard.CARD_UNIONS_IMAGE
def CARD_UNIONS              : thm := INCard.CARD_UNIONS
def EXPAND_NSUM_CONV_pth_0   : thm := INCard.pth_0
def EXPAND_NSUM_CONV_pth_1   : thm := INCard.pth_1
def EXPAND_NSUM_CONV_pth_2   : thm := INCard.pth_2
def EXPAND_NSUM_CONV : ioconv := INCard.EXPAND_NSUM_CONV
-- IterateSum1 (iterate.ml 1984-2211): sum + core algebra/ordering/bounds.
def sum                 : thm := IS1.sum
def NEUTRAL_REAL_ADD    : thm := IS1.NEUTRAL_REAL_ADD
def MONOIDAL_REAL_ADD   : thm := IS1.MONOIDAL_REAL_ADD
def SUM_DEGENERATE      : thm := IS1.SUM_DEGENERATE
def SUM_CLAUSES         : thm := IS1.SUM_CLAUSES
def SUM_UNION           : thm := IS1.SUM_UNION
def SUM_DIFF            : thm := IS1.SUM_DIFF
def SUM_INCL_EXCL       : thm := IS1.SUM_INCL_EXCL
def SUM_SUPPORT         : thm := IS1.SUM_SUPPORT
def SUM_ADD             : thm := IS1.SUM_ADD
def SUM_ADD_GEN         : thm := IS1.SUM_ADD_GEN
def SUM_EQ_0            : thm := IS1.SUM_EQ_0
def SUM_0               : thm := IS1.SUM_0
def SUM_LMUL            : thm := IS1.SUM_LMUL
def SUM_RMUL            : thm := IS1.SUM_RMUL
def SUM_NEG             : thm := IS1.SUM_NEG
def SUM_SUB             : thm := IS1.SUM_SUB
def SUM_LE              : thm := IS1.SUM_LE
def SUM_LT              : thm := IS1.SUM_LT
def SUM_LT_ALL          : thm := IS1.SUM_LT_ALL
def SUM_POS_LT          : thm := IS1.SUM_POS_LT
def SUM_POS_LT_ALL      : thm := IS1.SUM_POS_LT_ALL
def SUM_EQ              : thm := IS1.SUM_EQ
def SUM_ABS            : thm := IS1.SUM_ABS
def SUM_ABS_LE          : thm := IS1.SUM_ABS_LE
def SUM_CONST           : thm := IS1.SUM_CONST
def SUM_POS_LE          : thm := IS1.SUM_POS_LE
def SUM_POS_BOUND       : thm := IS1.SUM_POS_BOUND
def SUM_POS_EQ_0        : thm := IS1.SUM_POS_EQ_0
def SUM_ZERO_EXISTS     : thm := IS1.SUM_ZERO_EXISTS
def SUM_DELETE          : thm := IS1.SUM_DELETE
def SUM_DELETE_CASES    : thm := IS1.SUM_DELETE_CASES
def SUM_SING            : thm := IS1.SUM_SING
def SUM_DELTA           : thm := IS1.SUM_DELTA
def SUM_SWAP            : thm := IS1.SUM_SWAP
-- IterateSum2 (iterate.ml 2219-2598): image/count/group/subset/general.
def SUM_IMAGE               : thm := IS2.SUM_IMAGE
def SUM_SUPERSET            : thm := IS2.SUM_SUPERSET
def SUM_UNIV                : thm := IS2.SUM_UNIV
def SUM_UNION_RZERO         : thm := IS2.SUM_UNION_RZERO
def SUM_UNION_LZERO         : thm := IS2.SUM_UNION_LZERO
def SUM_RESTRICT            : thm := IS2.SUM_RESTRICT
def SUM_BOUND               : thm := IS2.SUM_BOUND
def SUM_BOUND_GEN           : thm := IS2.SUM_BOUND_GEN
def SUM_ABS_BOUND           : thm := IS2.SUM_ABS_BOUND
def SUM_BOUND_LT            : thm := IS2.SUM_BOUND_LT
def SUM_BOUND_LT_ALL        : thm := IS2.SUM_BOUND_LT_ALL
def SUM_BOUND_LT_GEN        : thm := IS2.SUM_BOUND_LT_GEN
def SUM_UNION_EQ            : thm := IS2.SUM_UNION_EQ
def SUM_EQ_SUPERSET         : thm := IS2.SUM_EQ_SUPERSET
def SUM_RESTRICT_SET        : thm := IS2.SUM_RESTRICT_SET
def SUM_SUM_RESTRICT        : thm := IS2.SUM_SUM_RESTRICT
def CARD_EQ_SUM             : thm := IS2.CARD_EQ_SUM
def SUM_MULTICOUNT_GEN      : thm := IS2.SUM_MULTICOUNT_GEN
def SUM_MULTICOUNT          : thm := IS2.SUM_MULTICOUNT
def SUM_IMAGE_GEN           : thm := IS2.SUM_IMAGE_GEN
def SUM_GROUP               : thm := IS2.SUM_GROUP
def SUM_GROUP_RELATION      : thm := IS2.SUM_GROUP_RELATION
def REAL_OF_NUM_SUM         : thm := IS2.REAL_OF_NUM_SUM
def SUM_SUBSET              : thm := IS2.SUM_SUBSET
def SUM_SUBSET_SIMPLE       : thm := IS2.SUM_SUBSET_SIMPLE
def SUM_MUL_BOUND           : thm := IS2.SUM_MUL_BOUND
def SUM_IMAGE_NONZERO       : thm := IS2.SUM_IMAGE_NONZERO
def SUM_BIJECTION           : thm := IS2.SUM_BIJECTION
def SUM_SUM_PRODUCT         : thm := IS2.SUM_SUM_PRODUCT
def SUM_EQ_GENERAL          : thm := IS2.SUM_EQ_GENERAL
def SUM_EQ_GENERAL_INVERSES : thm := IS2.SUM_EQ_GENERAL_INVERSES
def SUM_INJECTION           : thm := IS2.SUM_INJECTION
def SUM_UNION_NONZERO       : thm := IS2.SUM_UNION_NONZERO
def SUM_UNIONS_NONZERO      : thm := IS2.SUM_UNIONS_NONZERO
def SUM_CASES               : thm := IS2.SUM_CASES
def SUM_CASES_1             : thm := IS2.SUM_CASES_1
def SUM_LE_INCLUDED         : thm := IS2.SUM_LE_INCLUDED
def SUM_IMAGE_LE            : thm := IS2.SUM_IMAGE_LE
def SUM_CLOSED              : thm := IS2.SUM_CLOSED
def SUM_RELATED             : thm := IS2.SUM_RELATED
def SUM_CLOSED_NONEMPTY     : thm := IS2.SUM_CLOSED_NONEMPTY
def SUM_RELATED_NONEMPTY    : thm := IS2.SUM_RELATED_NONEMPTY
def REAL_OF_NUM_SUM_GEN     : thm := IS2.REAL_OF_NUM_SUM_GEN
-- IterateSum3 (iterate.ml 2599-2778): numseg intervals + partial summation.
def SUM_ADD_NUMSEG          : thm := IS3.SUM_ADD_NUMSEG
def SUM_SUB_NUMSEG          : thm := IS3.SUM_SUB_NUMSEG
def SUM_LE_NUMSEG           : thm := IS3.SUM_LE_NUMSEG
def SUM_EQ_NUMSEG           : thm := IS3.SUM_EQ_NUMSEG
def SUM_ABS_NUMSEG          : thm := IS3.SUM_ABS_NUMSEG
def SUM_CONST_NUMSEG        : thm := IS3.SUM_CONST_NUMSEG
def SUM_EQ_0_NUMSEG         : thm := IS3.SUM_EQ_0_NUMSEG
def SUM_TRIV_NUMSEG         : thm := IS3.SUM_TRIV_NUMSEG
def SUM_POS_LE_NUMSEG       : thm := IS3.SUM_POS_LE_NUMSEG
def SUM_POS_EQ_0_NUMSEG     : thm := IS3.SUM_POS_EQ_0_NUMSEG
def SUM_SING_NUMSEG         : thm := IS3.SUM_SING_NUMSEG
def SUM_CLAUSES_NUMSEG      : thm := IS3.SUM_CLAUSES_NUMSEG
def SUM_CLAUSES_NUMSEG_LT   : thm := IS3.SUM_CLAUSES_NUMSEG_LT
def SUM_CLAUSES_NUMSEG_LE   : thm := IS3.SUM_CLAUSES_NUMSEG_LE
def SUM_SWAP_NUMSEG         : thm := IS3.SUM_SWAP_NUMSEG
def SUM_ADD_SPLIT           : thm := IS3.SUM_ADD_SPLIT
def SUM_OFFSET              : thm := IS3.SUM_OFFSET
def SUM_OFFSET_0            : thm := IS3.SUM_OFFSET_0
def SUM_CLAUSES_LEFT        : thm := IS3.SUM_CLAUSES_LEFT
def SUM_CLAUSES_RIGHT       : thm := IS3.SUM_CLAUSES_RIGHT
def SUM_PAIR                : thm := IS3.SUM_PAIR
def SUM_REFLECT             : thm := IS3.SUM_REFLECT
def REAL_OF_NUM_SUM_NUMSEG  : thm := IS3.REAL_OF_NUM_SUM_NUMSEG
def SUM_PARTIAL_SUC         : thm := IS3.SUM_PARTIAL_SUC
def SUM_PARTIAL_PRE         : thm := IS3.SUM_PARTIAL_PRE
def SUM_DIFFS               : thm := IS3.SUM_DIFFS
def SUM_DIFFS_ALT           : thm := IS3.SUM_DIFFS_ALT
def SUM_COMBINE_R           : thm := IS3.SUM_COMBINE_R
def SUM_COMBINE_L           : thm := IS3.SUM_COMBINE_L
-- IterateSum4 (iterate.ml 2779-2854): congruences, EXPAND_SUM_CONV, REAL_SUB_POW.
def SUM_CONG                : thm := IS4.SUM_CONG
def EXPAND_SUM_CONV_pth_0   : thm := IS4.pth_0
def EXPAND_SUM_CONV_pth_1   : thm := IS4.pth_1
def EXPAND_SUM_CONV_pth_2   : thm := IS4.pth_2
def EXPAND_SUM_CONV : ioconv := IS4.EXPAND_SUM_CONV
def REAL_SUB_POW            : thm := IS4.REAL_SUB_POW
def REAL_SUB_POW_R1         : thm := IS4.REAL_SUB_POW_R1
def REAL_SUB_POW_L1         : thm := IS4.REAL_SUB_POW_L1
-- IterateSum5 (iterate.ml 2855-3108): real polynomial functions.
def REAL_SUB_POLYFUN        : thm := IS5.REAL_SUB_POLYFUN
def REAL_SUB_POLYFUN_ALT    : thm := IS5.REAL_SUB_POLYFUN_ALT
def REAL_POLYFUN_ROOTBOUND  : thm := IS5.REAL_POLYFUN_ROOTBOUND
def REAL_POLYFUN_FINITE_ROOTS : thm := IS5.REAL_POLYFUN_FINITE_ROOTS
def REAL_POLYFUN_EQ_0       : thm := IS5.REAL_POLYFUN_EQ_0
def REAL_POLYFUN_EQ_CONST   : thm := IS5.REAL_POLYFUN_EQ_CONST
def polynomial_function     : thm := IS5.polynomial_function
def POLYNOMIAL_FUNCTION_CONST : thm := IS5.POLYNOMIAL_FUNCTION_CONST
def POLYNOMIAL_FUNCTION_ID  : thm := IS5.POLYNOMIAL_FUNCTION_ID
def POLYNOMIAL_FUNCTION_I   : thm := IS5.POLYNOMIAL_FUNCTION_I
def POLYNOMIAL_FUNCTION_ADD : thm := IS5.POLYNOMIAL_FUNCTION_ADD
def POLYNOMIAL_FUNCTION_LMUL : thm := IS5.POLYNOMIAL_FUNCTION_LMUL
def POLYNOMIAL_FUNCTION_RMUL : thm := IS5.POLYNOMIAL_FUNCTION_RMUL
def POLYNOMIAL_FUNCTION_NEG : thm := IS5.POLYNOMIAL_FUNCTION_NEG
def POLYNOMIAL_FUNCTION_SUB : thm := IS5.POLYNOMIAL_FUNCTION_SUB
def POLYNOMIAL_FUNCTION_MUL : thm := IS5.POLYNOMIAL_FUNCTION_MUL
def POLYNOMIAL_FUNCTION_SUM : thm := IS5.POLYNOMIAL_FUNCTION_SUM
def POLYNOMIAL_FUNCTION_POW : thm := IS5.POLYNOMIAL_FUNCTION_POW
def POLYNOMIAL_FUNCTION_INDUCT : thm := IS5.POLYNOMIAL_FUNCTION_INDUCT
def POLYNOMIAL_FUNCTION_o   : thm := IS5.POLYNOMIAL_FUNCTION_o
def POLYNOMIAL_FUNCTION_FINITE_ROOTS : thm := IS5.POLYNOMIAL_FUNCTION_FINITE_ROOTS

end Session
