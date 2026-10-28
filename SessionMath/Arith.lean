/- File: SessionMath/Arith.lean
arith.ml (parts 1-9): natural-number arithmetic, built by `initialize` when
this module is imported, with its load-time procedures (MOD_DOWN_CONV,
NUM_CANCEL_CONV, LE_IMP, BITS_ELIM_CONV) at the end of the file.
-/
import SessionMath.Recursion
import HolMath.Arith

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Simp HolCore.Theorems HolCore.Classic

namespace Session

private def ioOk' {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")


/- ---------------------------------------------------------------------- -/
/- arith.ml, parts 1-6                                                     -/
/- ---------------------------------------------------------------------- -/

initialize arith1 : HolMath.Arith.ArithThms1 ← do
  HolMath.Arith.setupArithInfixes
  ioOk' "setupArith1" (HolMath.Arith.setupArith1 Nm MESON_TAC new_recursive_definition).run
initialize arith2 : HolMath.Arith.ArithThms2 ←
  ioOk' "setupArith2" (HolMath.Arith.setupArith2 Nm new_definition arith1 MESON_TAC
    new_recursive_definition).run
initialize arith3 : HolMath.Arith.ArithThms3 ←
  ioOk' "setupArith3" (HolMath.Arith.setupArith3 Nm arith1 arith2 MESON_TAC).run
initialize arith4 : HolMath.Arith.ArithThms4 ←
  ioOk' "setupArith4" (HolMath.Arith.setupArith4 Nm arith1 arith2 arith3 MESON_TAC
    ASM_MESON_TAC MESON).run
initialize arith5 : HolMath.Arith.ArithThms5 ←
  ioOk' "setupArith5" (HolMath.Arith.setupArith5 Nm arith1 arith2 arith3 arith4 MESON_TAC
    ASM_MESON_TAC new_recursive_definition).run
initialize arith6 : HolMath.Arith.ArithThms6 ←
  ioOk' "setupArith6" (HolMath.Arith.setupArith6 Nm arith1 arith2 arith3 arith4
    ASM_MESON_TAC).run

-- Part 1 theorems, as Session exposes them.
def PRE              : thm := arith1.PRE
def ADD              : thm := arith1.ADD
def ADD_0            : thm := arith1.ADD_0
def ADD_SUC          : thm := arith1.ADD_SUC
def ADD_CLAUSES      : thm := arith1.ADD_CLAUSES
def ADD_SYM          : thm := arith1.ADD_SYM
def ADD_ASSOC        : thm := arith1.ADD_ASSOC
def ADD_AC           : thm := arith1.ADD_AC
def ADD_EQ_0         : thm := arith1.ADD_EQ_0
def EQ_ADD_LCANCEL   : thm := arith1.EQ_ADD_LCANCEL
def EQ_ADD_RCANCEL   : thm := arith1.EQ_ADD_RCANCEL
def EQ_ADD_LCANCEL_0 : thm := arith1.EQ_ADD_LCANCEL_0
def EQ_ADD_RCANCEL_0 : thm := arith1.EQ_ADD_RCANCEL_0
def BIT0             : thm := arith1.BIT0
def BIT1             : thm := arith1.BIT1
def BIT0_THM         : thm := arith1.BIT0_THM
def BIT1_THM         : thm := arith1.BIT1_THM
def ONE              : thm := arith1.ONE
def TWO              : thm := arith1.TWO
def ADD1             : thm := arith1.ADD1

-- Part 2 theorems.
def MULT             : thm := arith2.MULT
def MULT_0           : thm := arith2.MULT_0
def MULT_SUC         : thm := arith2.MULT_SUC
def MULT_CLAUSES     : thm := arith2.MULT_CLAUSES
def MULT_SYM         : thm := arith2.MULT_SYM
def LEFT_ADD_DISTRIB : thm := arith2.LEFT_ADD_DISTRIB
def RIGHT_ADD_DISTRIB : thm := arith2.RIGHT_ADD_DISTRIB
def MULT_ASSOC       : thm := arith2.MULT_ASSOC
def MULT_AC          : thm := arith2.MULT_AC
def MULT_EQ_0        : thm := arith2.MULT_EQ_0
def EQ_MULT_LCANCEL  : thm := arith2.EQ_MULT_LCANCEL
def EQ_MULT_RCANCEL  : thm := arith2.EQ_MULT_RCANCEL
def MULT_2           : thm := arith2.MULT_2
def MULT_EQ_1        : thm := arith2.MULT_EQ_1
def EXP              : thm := arith2.EXP
def EXP_EQ_0         : thm := arith2.EXP_EQ_0
def EXP_EQ_1         : thm := arith2.EXP_EQ_1
def EXP_ZERO         : thm := arith2.EXP_ZERO
def EXP_ADD          : thm := arith2.EXP_ADD
def EXP_ONE          : thm := arith2.EXP_ONE
def EXP_1            : thm := arith2.EXP_1
def EXP_2            : thm := arith2.EXP_2
def MULT_EXP         : thm := arith2.MULT_EXP
def EXP_MULT         : thm := arith2.EXP_MULT
def EXP_EXP          : thm := arith2.EXP_EXP
def LE               : thm := arith2.LE
def LT               : thm := arith2.LT
def GE               : thm := arith2.GE
def GT               : thm := arith2.GT
def MAX              : thm := arith2.MAX
def MIN              : thm := arith2.MIN
def LE_SUC_LT        : thm := arith2.LE_SUC_LT
def LT_SUC_LE        : thm := arith2.LT_SUC_LE
def LE_SUC           : thm := arith2.LE_SUC
def LT_SUC           : thm := arith2.LT_SUC
def LE_0             : thm := arith2.LE_0
def LT_0             : thm := arith2.LT_0

-- Part 3 theorems.
def LE_REFL          : thm := arith3.LE_REFL
def LT_REFL          : thm := arith3.LT_REFL
def LT_IMP_NE        : thm := arith3.LT_IMP_NE
def LE_ANTISYM       : thm := arith3.LE_ANTISYM
def LT_ANTISYM       : thm := arith3.LT_ANTISYM
def LET_ANTISYM      : thm := arith3.LET_ANTISYM
def LTE_ANTISYM      : thm := arith3.LTE_ANTISYM
def LE_TRANS         : thm := arith3.LE_TRANS
def LT_TRANS         : thm := arith3.LT_TRANS
def LET_TRANS        : thm := arith3.LET_TRANS
def LTE_TRANS        : thm := arith3.LTE_TRANS
def LE_CASES         : thm := arith3.LE_CASES
def LT_CASES         : thm := arith3.LT_CASES
def LET_CASES        : thm := arith3.LET_CASES
def LTE_CASES        : thm := arith3.LTE_CASES
def LE_LT            : thm := arith3.LE_LT
def LT_LE            : thm := arith3.LT_LE
def NOT_LE           : thm := arith3.NOT_LE
def NOT_LT           : thm := arith3.NOT_LT
def LT_IMP_LE        : thm := arith3.LT_IMP_LE
def EQ_IMP_LE        : thm := arith3.EQ_IMP_LE
def LT_NZ            : thm := arith3.LT_NZ
def LE_1             : thm := arith3.LE_1

-- Part 4 theorems.
def LE_EXISTS          : thm := arith4.LE_EXISTS
def LT_EXISTS          : thm := arith4.LT_EXISTS
def LE_ADD             : thm := arith4.LE_ADD
def LE_ADDR            : thm := arith4.LE_ADDR
def LT_ADD             : thm := arith4.LT_ADD
def LT_ADDR            : thm := arith4.LT_ADDR
def LE_ADD_LCANCEL     : thm := arith4.LE_ADD_LCANCEL
def LE_ADD_RCANCEL     : thm := arith4.LE_ADD_RCANCEL
def LT_ADD_LCANCEL     : thm := arith4.LT_ADD_LCANCEL
def LT_ADD_RCANCEL     : thm := arith4.LT_ADD_RCANCEL
def LE_ADD2            : thm := arith4.LE_ADD2
def LET_ADD2           : thm := arith4.LET_ADD2
def LTE_ADD2           : thm := arith4.LTE_ADD2
def LT_ADD2            : thm := arith4.LT_ADD2
def LT_MULT            : thm := arith4.LT_MULT
def LE_MULT2           : thm := arith4.LE_MULT2
def LT_LMULT           : thm := arith4.LT_LMULT
def LE_MULT_LCANCEL    : thm := arith4.LE_MULT_LCANCEL
def LE_MULT_RCANCEL    : thm := arith4.LE_MULT_RCANCEL
def LT_MULT_LCANCEL    : thm := arith4.LT_MULT_LCANCEL
def LT_MULT_RCANCEL    : thm := arith4.LT_MULT_RCANCEL
def LT_MULT2           : thm := arith4.LT_MULT2
def LE_SQUARE_REFL     : thm := arith4.LE_SQUARE_REFL
def LT_POW2_REFL       : thm := arith4.LT_POW2_REFL
def WLOG_LE            : thm := arith4.WLOG_LE
def WLOG_LT            : thm := arith4.WLOG_LT
def WLOG_LE_3          : thm := arith4.WLOG_LE_3
def num_WF             : thm := arith4.num_WF
def num_WOP            : thm := arith4.num_WOP
def num_MAX            : thm := arith4.num_MAX
def LE_INDUCT          : thm := arith4.LE_INDUCT
def num_INDUCTION_DOWN : thm := arith4.num_INDUCTION_DOWN

-- Part 5 theorems.
def EVEN                   : thm := arith5.EVEN
def ODD                    : thm := arith5.ODD
def NOT_EVEN               : thm := arith5.NOT_EVEN
def NOT_ODD                : thm := arith5.NOT_ODD
def EVEN_OR_ODD            : thm := arith5.EVEN_OR_ODD
def EVEN_AND_ODD           : thm := arith5.EVEN_AND_ODD
def EVEN_ADD               : thm := arith5.EVEN_ADD
def EVEN_MULT              : thm := arith5.EVEN_MULT
def EVEN_EXP               : thm := arith5.EVEN_EXP
def ODD_ADD                : thm := arith5.ODD_ADD
def ODD_MULT               : thm := arith5.ODD_MULT
def ODD_EXP                : thm := arith5.ODD_EXP
def EVEN_DOUBLE            : thm := arith5.EVEN_DOUBLE
def ODD_DOUBLE             : thm := arith5.ODD_DOUBLE
def EVEN_EXISTS_LEMMA      : thm := arith5.EVEN_EXISTS_LEMMA
def EVEN_EXISTS            : thm := arith5.EVEN_EXISTS
def ODD_EXISTS             : thm := arith5.ODD_EXISTS
def EVEN_ODD_DECOMPOSITION : thm := arith5.EVEN_ODD_DECOMPOSITION
def SUB                    : thm := arith5.SUB
def SUB_0                  : thm := arith5.SUB_0
def SUB_PRESUC             : thm := arith5.SUB_PRESUC
def SUB_SUC                : thm := arith5.SUB_SUC
def SUB_REFL               : thm := arith5.SUB_REFL
def ADD_SUB                : thm := arith5.ADD_SUB
def ADD_SUB2               : thm := arith5.ADD_SUB2
def SUB_EQ_0               : thm := arith5.SUB_EQ_0
def ADD_SUBR2              : thm := arith5.ADD_SUBR2
def ADD_SUBR               : thm := arith5.ADD_SUBR
def SUB_ADD                : thm := arith5.SUB_ADD
def SUB_ADD_LCANCEL        : thm := arith5.SUB_ADD_LCANCEL
def SUB_ADD_RCANCEL        : thm := arith5.SUB_ADD_RCANCEL
def LEFT_SUB_DISTRIB       : thm := arith5.LEFT_SUB_DISTRIB
def RIGHT_SUB_DISTRIB      : thm := arith5.RIGHT_SUB_DISTRIB
def SUC_SUB1               : thm := arith5.SUC_SUB1
def EVEN_SUB               : thm := arith5.EVEN_SUB
def ODD_SUB                : thm := arith5.ODD_SUB
def FACT                   : thm := arith5.FACT
def FACT_LT                : thm := arith5.FACT_LT
def FACT_LE                : thm := arith5.FACT_LE
def FACT_NZ                : thm := arith5.FACT_NZ
def FACT_MONO              : thm := arith5.FACT_MONO

-- Part 6 theorems.
def EXP_LT_0        : thm := arith6.EXP_LT_0
def LT_EXP          : thm := arith6.LT_EXP
def LE_EXP          : thm := arith6.LE_EXP
def EQ_EXP          : thm := arith6.EQ_EXP
def EXP_MONO_LE_IMP : thm := arith6.EXP_MONO_LE_IMP
def EXP_MONO_LT_IMP : thm := arith6.EXP_MONO_LT_IMP
def EXP_MONO_LE     : thm := arith6.EXP_MONO_LE
def EXP_MONO_LT     : thm := arith6.EXP_MONO_LT
def EXP_MONO_EQ     : thm := arith6.EXP_MONO_EQ


/- ---------------------------------------------------------------------- -/
/- arith.ml, parts 7-9 (need METIS and IMP_REWRITE_TAC from Provers)       -/
/- ---------------------------------------------------------------------- -/

initialize arith7 : HolMath.Arith.ArithThms7 ←
  ioOk' "setupArith7" (HolMath.Arith.setupArith7 Nm arith1 arith2 arith3 arith4 arith5
    MESON_TAC ASM_MESON_TAC MESON IMP_REWRITE_TAC new_specification).run

def DIVMOD_EXIST      : thm := arith7.DIVMOD_EXIST
def DIVMOD_EXIST_0    : thm := arith7.DIVMOD_EXIST_0
def DIVISION_0        : thm := arith7.DIVISION_0
def DIVISION          : thm := arith7.DIVISION
def DIV_ZERO          : thm := arith7.DIV_ZERO
def MOD_ZERO          : thm := arith7.MOD_ZERO
def DIVISION_SIMP     : thm := arith7.DIVISION_SIMP
def EQ_DIVMOD         : thm := arith7.EQ_DIVMOD
def MOD_LT_EQ         : thm := arith7.MOD_LT_EQ
def MOD_LT_EQ_LT      : thm := arith7.MOD_LT_EQ_LT
def DIVMOD_UNIQ_LEMMA : thm := arith7.DIVMOD_UNIQ_LEMMA
def DIVMOD_UNIQ       : thm := arith7.DIVMOD_UNIQ
def MOD_UNIQ          : thm := arith7.MOD_UNIQ
def DIV_UNIQ          : thm := arith7.DIV_UNIQ
def DIV_0             : thm := arith7.DIV_0
def MOD_0             : thm := arith7.MOD_0
def DIV_MULT          : thm := arith7.DIV_MULT
def MOD_MULT          : thm := arith7.MOD_MULT
def MOD_LT            : thm := arith7.MOD_LT
def MOD_EQ_SELF       : thm := arith7.MOD_EQ_SELF
def MOD_CASES         : thm := arith7.MOD_CASES
def MOD_ADD_CASES     : thm := arith7.MOD_ADD_CASES
def MOD_EQ            : thm := arith7.MOD_EQ
def DIV_LE            : thm := arith7.DIV_LE
def DIV_MUL_LE        : thm := arith7.DIV_MUL_LE
def MOD_LE_TWICE      : thm := arith7.MOD_LE_TWICE
def DIV_1             : thm := arith7.DIV_1
def MOD_1             : thm := arith7.MOD_1
def DIV_LT            : thm := arith7.DIV_LT
def MOD_MOD           : thm := arith7.MOD_MOD
def MOD_MOD_REFL      : thm := arith7.MOD_MOD_REFL
def MOD_MOD_LE        : thm := arith7.MOD_MOD_LE
def MOD_EVEN_2        : thm := arith7.MOD_EVEN_2
def DIV_MULT2         : thm := arith7.DIV_MULT2
def MOD_MULT2         : thm := arith7.MOD_MULT2
def MOD_EXISTS        : thm := arith7.MOD_EXISTS
def LE_RDIV_EQ        : thm := arith7.LE_RDIV_EQ
def RDIV_LT_EQ        : thm := arith7.RDIV_LT_EQ
def LE_LDIV_EQ        : thm := arith7.LE_LDIV_EQ
def LDIV_LT_EQ        : thm := arith7.LDIV_LT_EQ
def LE_LDIV           : thm := arith7.LE_LDIV
def DIV_MONO          : thm := arith7.DIV_MONO
def DIV_MONO_LT       : thm := arith7.DIV_MONO_LT
def DIV_EQ_0          : thm := arith7.DIV_EQ_0
def MOD_DIV_EQ_0      : thm := arith7.MOD_DIV_EQ_0
def MOD_EQ_0          : thm := arith7.MOD_EQ_0
def DIV_EQ_SELF       : thm := arith7.DIV_EQ_SELF
def MOD_REFL          : thm := arith7.MOD_REFL

initialize arith8 : HolMath.Arith.ArithThms8 ←
  ioOk' "setupArith8" (HolMath.Arith.setupArith8 Nm arith1 arith2 arith3 arith4 arith5 arith6 arith7
    MESON_TAC ASM_MESON_TAC MESON METIS_TAC ASM_METIS_TAC).run

def EVEN_MOD          : thm := arith8.EVEN_MOD
def ODD_MOD           : thm := arith8.ODD_MOD
def MOD_2_CASES       : thm := arith8.MOD_2_CASES
def EVEN_MOD_EVEN     : thm := arith8.EVEN_MOD_EVEN
def ODD_MOD_EVEN      : thm := arith8.ODD_MOD_EVEN
def HALF_DOUBLE       : thm := arith8.HALF_DOUBLE
def DOUBLE_HALF       : thm := arith8.DOUBLE_HALF
def MOD_MULT_RMOD     : thm := arith8.MOD_MULT_RMOD
def MOD_MULT_LMOD     : thm := arith8.MOD_MULT_LMOD
def MOD_MULT_MOD2     : thm := arith8.MOD_MULT_MOD2
def MOD_EXP_MOD       : thm := arith8.MOD_EXP_MOD
def MOD_MULT_ADD      : thm := arith8.MOD_MULT_ADD
def DIV_MULT_ADD      : thm := arith8.DIV_MULT_ADD
def MOD_ADD_MOD       : thm := arith8.MOD_ADD_MOD
def DIV_ADD_MOD       : thm := arith8.DIV_ADD_MOD
def MOD_ADD_EQ_EQ     : thm := arith8.MOD_ADD_EQ_EQ
def DIV_ADD_EQ_EQ     : thm := arith8.DIV_ADD_EQ_EQ
def DIV_ADD_EQ        : thm := arith8.DIV_ADD_EQ
def MOD_ADD_EQ        : thm := arith8.MOD_ADD_EQ
def DIV_REFL          : thm := arith8.DIV_REFL
def MOD_LE            : thm := arith8.MOD_LE
def DIV_MONO2         : thm := arith8.DIV_MONO2
def DIV_LE_EXCLUSION  : thm := arith8.DIV_LE_EXCLUSION
def DIV_EQ_EXCLUSION  : thm := arith8.DIV_EQ_EXCLUSION
def MULT_DIV_LE       : thm := arith8.MULT_DIV_LE
def DIV_DIV           : thm := arith8.DIV_DIV
def DIV_MOD           : thm := arith8.DIV_MOD
def MOD_MULT_MOD      : thm := arith8.MOD_MULT_MOD
def MOD_MOD_EXP_MIN   : thm := arith8.MOD_MOD_EXP_MIN
def DIV_EXP           : thm := arith8.DIV_EXP
def MOD_EXP           : thm := arith8.MOD_EXP
def FORALL_LT_MOD_THM : thm := arith8.FORALL_LT_MOD_THM
def FORALL_MOD_THM    : thm := arith8.FORALL_MOD_THM
def EXISTS_LT_MOD_THM : thm := arith8.EXISTS_LT_MOD_THM
def EXISTS_MOD_THM    : thm := arith8.EXISTS_MOD_THM

initialize arith9 : HolMath.Arith.ArithThms9 ← do
  -- `parse_as_binder "minimal"` must run before `minimal` is parsed.
  HolMath.Arith.setupMinimalBinder
  ioOk' "setupArith9" (HolMath.Arith.setupArith9 Nm arith1 arith2 arith3 arith4 arith5 arith7
    MESON_TAC ASM_MESON_TAC MESON SELECT_CONV
    new_definition prove_recursive_functions_exist).run

def PRE_ELIM_THM             : thm := arith9.PRE_ELIM_THM
def PRE_ELIM_THM'            : thm := arith9.PRE_ELIM_THM'
def SUB_ELIM_THM             : thm := arith9.SUB_ELIM_THM
def SUB_ELIM_THM'            : thm := arith9.SUB_ELIM_THM'
def DIVMOD_ELIM_THM          : thm := arith9.DIVMOD_ELIM_THM
def DIVMOD_ELIM_THM'         : thm := arith9.DIVMOD_ELIM_THM'
def minimal                  : thm := arith9.minimal
def MINIMAL                  : thm := arith9.MINIMAL
def MINIMAL_UNIQUE           : thm := arith9.MINIMAL_UNIQUE
def LE_MINIMAL               : thm := arith9.LE_MINIMAL
def MINIMAL_LE               : thm := arith9.MINIMAL_LE
def MINIMAL_UBOUND           : thm := arith9.MINIMAL_UBOUND
def MINIMAL_LBOUND           : thm := arith9.MINIMAL_LBOUND
def MINIMAL_MONO             : thm := arith9.MINIMAL_MONO
def TRANSITIVE_STEPWISE_LT_EQ : thm := arith9.TRANSITIVE_STEPWISE_LT_EQ
def TRANSITIVE_STEPWISE_LT   : thm := arith9.TRANSITIVE_STEPWISE_LT
def TRANSITIVE_STEPWISE_LE_EQ : thm := arith9.TRANSITIVE_STEPWISE_LE_EQ
def TRANSITIVE_STEPWISE_LE   : thm := arith9.TRANSITIVE_STEPWISE_LE
def DEPENDENT_CHOICE_FIXED   : thm := arith9.DEPENDENT_CHOICE_FIXED
def DEPENDENT_CHOICE         : thm := arith9.DEPENDENT_CHOICE

/- arith.ml's procedures `MOD_DOWN_CONV`, `NUM_CANCEL_CONV`, `LE_IMP` and
   `BITS_ELIM_CONV`.  Each is `let <proformas> in fun tm -> ...` in OCaml, so
   its proformas are built once, when arith.ml loads; here each is built
   eagerly by an `initialize` at arith.ml's position (the eager analogue of
   Session's `ensureArithProcs`). -/

/- arith.ml's procedures `MOD_DOWN_CONV`, `NUM_CANCEL_CONV`, `LE_IMP` and
   `BITS_ELIM_CONV`.  Each is `let <proformas> in fun tm -> ...` in OCaml, so
   its proformas are built once, when arith.ml loads.  Here they are built
   eagerly into plain refs by one `initialize` forcing block, in arith.ml's
   file order (the eager analogue of Session's `ensureArithProcs`); the refs
   are seeded at that point and read back by the exports.  (They are refs, not
   function-typed `initialize` constants, because a bare closure value does
   not survive separate compilation / `dlopen`.) -/
initialize theModDownConv : IO.Ref (Option ioconv) ← IO.mkRef none
initialize theNumCancelConv : IO.Ref (Option ioconv) ← IO.mkRef none
initialize theLeImp : IO.Ref (Option (thm → ExceptT String IO thm)) ← IO.mkRef none
initialize theBitsElimConv : IO.Ref (Option conv) ← IO.mkRef none

/-- Build arith.ml's procedures in file order (arith.ml 1713, 1732, 1762,
    1877), as OCaml does when arith.ml loads. -/
initialize ensureArithProcs : Unit ← do
  theModDownConv.set (some (← ioOk' "MOD_DOWN_CONV"
    (HolMath.Arith.MOD_DOWN_CONV METIS ADD1 MOD_ADD_MOD MOD_MOD_REFL
      MOD_MULT_MOD2 MOD_EXP_MOD).run))
  theNumCancelConv.set (some (← ioOk' "NUM_CANCEL_CONV"
    (HolMath.Arith.NUM_CANCEL_CONV EQ_ADD_LCANCEL EQ_ADD_LCANCEL_0 ADD_AC).run))
  theLeImp.set (some (← ioOk' "LE_IMP" (HolMath.Arith.LE_IMP T.IMP_CONJ LE_TRANS).run))
  theBitsElimConv.set (some (← ioOk' "BITS_ELIM_CONV"
    (HolMath.Arith.BITS_ELIM_CONV Nm.NUMERAL BIT0 BIT1 ADD1 EQ_ADD_RCANCEL
      MULT_2 EQ_MULT_LCANCEL TWO Nm.NOT_SUC).run))

/-- `MOD_DOWN_CONV` (arith.ml 1713-1726). -/
def MOD_DOWN_CONV : ioconv := fun tm => do
  match ← theModDownConv.get with
  | some c => c tm
  | none => throw (IO.userError "MOD_DOWN_CONV not initialized")
/-- `NUM_CANCEL_CONV` (arith.ml 1732-1756). -/
def NUM_CANCEL_CONV : ioconv := fun tm => do
  match ← theNumCancelConv.get with
  | some c => c tm
  | none => throw (IO.userError "NUM_CANCEL_CONV not initialized")
/-- `LE_IMP` (arith.ml 1762-1764). -/
def LE_IMP (th : thm) : IO (Except String thm) := do
  match ← theLeImp.get with
  | some r => (r th).run
  | none => throw (IO.userError "LE_IMP not initialized")
/-- `BITS_ELIM_CONV` (arith.ml 1877-1904). -/
def BITS_ELIM_CONV : IO (Except String conv) := do
  match ← theBitsElimConv.get with
  | some c => return .ok c
  | none => throw (IO.userError "BITS_ELIM_CONV not initialized")


end Session
