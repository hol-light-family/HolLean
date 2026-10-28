/- File: SessionMath/RealAx.lean
realax.ml: the construction of the real numbers, built by `initialize` when
this module is imported, in file order.  realax.ml's overloads come first
(`realAxOverloads`), so `===`, `<<=`, `++` and `**` parse, and from then on
`:real` is the default type for overloaded operators, as in HOL Light.
-/
import SessionMath.Lists
import HolMath.RealAx

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Simp HolCore.Theorems HolCore.Classic

namespace Session

private def ioOk' {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")


/- ---------------------------------------------------------------------- -/
/- Primitives this region is the first to need.                            -/
/- ---------------------------------------------------------------------- -/

/-- `new_definition_pair` (pair.ml): the depairing `new_definition`.  pair.ml
    rebinds `new_definition` (SessionMath/Pair.lean), so this is that function under the
    name the realax stages ask for. -/
def new_definition_pair : term → IO (Except String thm) := new_definition

/- ---------------------------------------------------------------------- -/
/- realax.ml: the overloading / interface primitives.  These live in       -/
/- HolCore.Preterm and HolCore.Printer and mutate global parser state;     -/
/- realax.ml drives them directly, so re-export them under their OCaml     -/
/- names for the `setupRealAx*` functions to consume.                      -/
/- ---------------------------------------------------------------------- -/

/-- `make_overloadable` (preterm.ml): declare a symbol overloadable at a
    generic type. -/
def make_overloadable (s : String) (ty : hol_type) :
    IO (Except String Unit) := Preterm.make_overloadable s ty

/-- `overload_interface` (preterm.ml): add a mapping for an overloaded symbol. -/
def overload_interface (s : String) (tm : term) :
    IO (Except String Unit) := Preterm.overload_interface s tm

/-- `override_interface` (preterm.ml): replace all mappings for a symbol. -/
def override_interface (s : String) (tm : term) :
    IO (Except String Unit) := Preterm.override_interface s tm

/-- `reduce_interface` (preterm.ml): remove ONE mapping for a symbol. -/
def reduce_interface (s : String) (tm : term) :
    IO (Except String Unit) := Preterm.reduce_interface s tm

/-- `remove_interface` (preterm.ml): remove ALL mappings for a symbol. -/
def remove_interface (s : String) : IO Unit := Preterm.remove_interface s

/-- `prioritize_overload` (preterm.ml): make a type the default for overloads. -/
def prioritize_overload (ty : hol_type) : IO Unit :=
  Preterm.prioritize_overload ty

/-- `parse_as_infix` (printer.ml). -/
def parse_as_infix (p : String × (Int × String)) : IO Unit :=
  Printer.parse_as_infix p

/-- `parse_as_prefix` (printer.ml). -/
def parse_as_prefix (s : String) : IO Unit := Printer.parse_as_prefix s

/-- `AC ADD_AC`: the AC-normalising rule for natural-number addition.  The
    library's `Theorems.AC` takes its AC-suite as a parameter; realax.ml uses
    both this and the multiplicative form, so name them here. -/
def AC_ADD (tm : term) : IO (Except String thm) :=
  Theorems.AC B T.REFL_CLAUSE arith1.ADD_AC tm

/-- `AC MULT_AC`: the AC-normalising rule for natural-number multiplication. -/
def AC_MULT (tm : term) : IO (Except String thm) :=
  Theorems.AC B T.REFL_CLAUSE arith2.MULT_AC tm

/- ---------------------------------------------------------------------- -/
/- realax.ml: the construction of the real numbers, in TEN stages.         -/
/-                                                                        -/
/- The stages MUST run in realax.ml's own order, because each mutates      -/
/- global state the next one depends on: `setupRealAxOverloads` installs   -/
/- the infix/overload declarations without which `x === y` will not parse, -/
/- and `setupNadd`/`setupHreal`/`setupReal` each DECLARE CONSTANTS AND A   -/
/- TYPE (`nadd`, `hreal`, `real`) so each may run only ONCE PER PROCESS.   -/
/- That ordering is reproduced by the `initialize` declaration order here  -/
/- (and reinforced structurally: every stage takes the previous stage's    -/
/- record as a parameter).                                                 -/
/- ---------------------------------------------------------------------- -/

/-- realax.ml 17-48 (the overloading head), run EAGERLY once.  It returns no
    theorems, only parser-state side effects, without which the
    `===`/`<<=`/`++`/`**` infixes would be missing and every later stage would
    fail to parse its own statements.

    realax.ml 27-41 builds the generic types of the overloadable symbols with
    `mk_type "num" []`, so the `nums.ml` layer must already have run, which
    it has (`Nm` is built at import, earlier).  Load-order fidelity
    (load-bearing): `hol_lib.ml` loads calc_num.ml and normalizer.ml BEFORE
    realax.ml, so every calc_num proforma (`CnP`) and the `SEMIRING_PTHS`
    instance (`NmzP`) were built while `:num` was still the default for the
    overloaded arithmetic symbols; those layers' `initialize`s ran before this
    module, so that order holds. -/
initialize realAxOverloads : Unit ←
  ioOk' "setupRealAxOverloads" (HolMath.RealAx.setupRealAxOverloads parse_as_infix
    make_overloadable overload_interface)

/-- `DistThms` (realax.ml 54-247): `dist` and the bounds lemmas.  NOTE
    `dist(m,n) = ...` has a PAIRED left-hand side, so this stage is given
    `new_definition_pair`, not the primitive `new_definition`. -/
initialize distLayer : HolMath.RealAx.DistThms ←
  ioOk' "setupDist" (HolMath.RealAx.setupDist Nm arith1 arith2 arith3 arith4 arith5
    SUB_ELIM_THM (Drule.HIGHER_REWRITE_CONV_ths B) NUM_CANCEL_CONV
    new_definition_pair).run

def Dst : HolMath.RealAx.DistThms := distLayer

/-- `NaddThms` (realax.ml 253-363): the `nadd` type of nearly multiplicative
    functions.  DECLARES the `nadd` type — once per process. -/
initialize naddLayer : HolMath.RealAx.NaddThms ←
  ioOk' "setupNadd" (HolMath.RealAx.setupNadd Nm arith1 arith2 arith3 arith4 Dst ETA_AX
    NUM_CANCEL_CONV CnA.ARITH
    LE_IMP new_definition
    (fun a b c d => Kernel.new_basic_type_definition a b c d)
    override_interface).run

def Nad : HolMath.RealAx.NaddThms := naddLayer

/-- `NaddOrderThms` (realax.ml 366-511): `===`, `&` and `<<=`. -/
initialize naddOrderLayer : HolMath.RealAx.NaddOrderThms ←
  ioOk' "setupNaddOrder" (HolMath.RealAx.setupNaddOrder arith1 arith2 arith3 arith4 Dst Nad
    LE_IMP new_definition override_interface).run

def NOr : HolMath.RealAx.NaddOrderThms := naddOrderLayer

/-- `NaddArithThms` (realax.ml 514-700): `++` and `**`. -/
initialize naddArithLayer : HolMath.RealAx.NaddArithThms ←
  ioOk' "setupNaddArith" (HolMath.RealAx.setupNaddArith arith1 arith2 arith3 arith4 Dst Nad NOr
    ETA_AX LE_IMP new_definition override_interface).run

def NAr : HolMath.RealAx.NaddArithThms := naddArithLayer

/-- `NaddCompleteThms` (realax.ml 703-929): the Archimedean property and
    `NADD_COMPLETE`. -/
initialize naddCompleteLayer : HolMath.RealAx.NaddCompleteThms ←
  ioOk' "setupNaddComplete" (HolMath.RealAx.setupNaddComplete arith1 arith2 arith3 arith4 Dst Nad
    NOr NAr MESON_TAC ASM_MESON_TAC).run

def NCm : HolMath.RealAx.NaddCompleteThms := naddCompleteLayer

/-- `NaddInvAuxThms` (realax.ml 933-1179): `nadd_rinv` and the eleven lemmas
    leading to the multiplicative inverse. -/
initialize naddInvAuxLayer : HolMath.RealAx.NaddInvAuxThms ←
  ioOk' "setupNaddInvAux" (HolMath.RealAx.setupNaddInvAux Nm arith1 arith2 arith3 arith4 DIVISION
    Dst Nad NOr NAr NCm CnA.ARITH ARITH_SUC new_definition).run

def NIv : HolMath.RealAx.NaddInvAuxThms := naddInvAuxLayer

/-- `HrealThms` (realax.ml 1182-1381): the SECOND type construction, `hreal` =
    `nadd` quotiented by `===`.  DECLARES the `hreal` type — once per process. -/
initialize hrealLayer : HolMath.RealAx.HrealThms ←
  ioOk' "setupHreal" (HolMath.RealAx.setupHreal arith1 arith2 arith3 arith4 Dst Nad NOr NAr NCm NIv
    ASM_MESON_TAC new_definition
    define_quotient_type lift_function lift_theorem
    override_interface overload_interface).run

def Hrl : HolMath.RealAx.HrealThms := hrealLayer

/-- `TrealThms` (realax.ml 1385-1708): the signed-real representatives on
    `hreal#hreal`.  All seven definitions here have PAIRED left-hand sides, so
    this stage takes `new_definition_pair`. -/
initialize trealLayer : HolMath.RealAx.TrealThms ←
  ioOk' "setupTreal" (HolMath.RealAx.setupTreal Pr arith1 arith2 Hrl
    new_definition_pair).run

def Trl : HolMath.RealAx.TrealThms := trealLayer

/-- `RealThms` (realax.ml 1711-1973): the THIRD AND FINAL type construction —
    `real` = `hreal#hreal` quotiented by `treal_eq` — plus the friendly
    interface, the additional definitions, and `REAL_COMPLETE` (the supremum
    property).  DECLARES the `real` type — once per process.  Its last act is
    realax.ml's own interface cleanup, which retires the `hreal` overloads and
    DELETES the nadd notations `**`, `++`, `<<=`, `===`, `fn` and `afn`; those
    no longer parse once this has run. -/
initialize realLayer : HolMath.RealAx.RealThms ←
  ioOk' "setupReal" (HolMath.RealAx.setupReal Pr Hrl Trl
    Nm.num_RECURSION new_definition
    new_recursive_definition define_quotient_type lift_function
    lift_theorem overload_interface parse_as_prefix parse_as_infix
    prioritize_overload reduce_interface remove_interface).run

def Rl : HolMath.RealAx.RealThms := realLayer

/- Public accessors for the realax.ml bundles. -/

/-- The `realax.ml` `dist` record (54-247). -/
def distThms : HolMath.RealAx.DistThms := Dst
/-- The `realax.ml` `nadd` record (253-363). -/
def naddThms : HolMath.RealAx.NaddThms := Nad
/-- The `realax.ml` nadd-ordering record (366-511). -/
def naddOrderThms : HolMath.RealAx.NaddOrderThms := NOr
/-- The `realax.ml` nadd-arithmetic record (514-700). -/
def naddArithThms : HolMath.RealAx.NaddArithThms := NAr
/-- The `realax.ml` nadd-completeness record (703-929). -/
def naddCompleteThms : HolMath.RealAx.NaddCompleteThms := NCm
/-- The `realax.ml` inverse-auxiliary record (933-1179). -/
def naddInvAuxThms : HolMath.RealAx.NaddInvAuxThms := NIv
/-- The `realax.ml` `hreal` record (1182-1381). -/
def hrealThms : HolMath.RealAx.HrealThms := Hrl
/-- The `realax.ml` signed-real record (1385-1708). -/
def trealThms : HolMath.RealAx.TrealThms := Trl
/-- The `realax.ml` `real` record (1711-1973). -/
def realThms : HolMath.RealAx.RealThms := Rl

/-- `prioritize_real` (realax.ml 1780): make `:real` the default for overloaded
    symbols. -/
def prioritize_real : IO Unit := do
  match ← (mk_type "real" []) with
  | .ok ty => prioritize_overload ty
  | .error e => throw (IO.userError s!"prioritize_real: {e}")

/- Selected `real` theorems, for convenience at the top level. -/

/-- `REAL_COMPLETE` (realax.ml 1907): the supremum property. -/
def REAL_COMPLETE     : thm := Rl.REAL_COMPLETE
/-- `REAL_ADD_LINV` (realax.ml 1738): `|- !x. --x + x = &0`. -/
def REAL_ADD_LINV     : thm := Rl.REAL_ADD_LINV
/-- `REAL_MUL_LINV` (realax.ml 1738): `|- !x. ~(x = &0) ==> inv x * x = &1`. -/
def REAL_MUL_LINV     : thm := Rl.REAL_MUL_LINV
/-- `REAL_LE_TOTAL` (realax.ml 1738): `|- !x y. x <= y \/ y <= x`. -/
def REAL_LE_TOTAL     : thm := Rl.REAL_LE_TOTAL
/-- `REAL_ADD_LDISTRIB` (realax.ml 1738). -/
def REAL_ADD_LDISTRIB : thm := Rl.REAL_ADD_LDISTRIB
/-- `real_sub` (realax.ml 1786): `|- !x y. x - y = x + --y`. -/
def real_sub          : thm := Rl.real_sub
/-- `real_abs` (realax.ml 1801). -/
def real_abs          : thm := Rl.real_abs
/-- `real_pow` (realax.ml 1804): the two recursion clauses. -/
def real_pow          : thm := Rl.real_pow


/- The realax.ml theorems as bare names, as HOL Light has them. -/
def real_tybij1           : thm := Rl.real_tybij1
def real_tybij2           : thm := Rl.real_tybij2
def real_of_num           : thm := Rl.real_of_num
def real_of_num_th        : thm := Rl.real_of_num_th
def real_neg              : thm := Rl.real_neg
def real_neg_th           : thm := Rl.real_neg_th
def real_add              : thm := Rl.real_add
def real_add_th           : thm := Rl.real_add_th
def real_mul              : thm := Rl.real_mul
def real_mul_th           : thm := Rl.real_mul_th
def real_le               : thm := Rl.real_le
def real_le_th            : thm := Rl.real_le_th
def real_inv              : thm := Rl.real_inv
def real_inv_th           : thm := Rl.real_inv_th
def REAL_ADD_SYM          : thm := Rl.REAL_ADD_SYM
def REAL_ADD_ASSOC        : thm := Rl.REAL_ADD_ASSOC
def REAL_ADD_LID          : thm := Rl.REAL_ADD_LID
def REAL_MUL_SYM          : thm := Rl.REAL_MUL_SYM
def REAL_MUL_ASSOC        : thm := Rl.REAL_MUL_ASSOC
def REAL_MUL_LID          : thm := Rl.REAL_MUL_LID
def REAL_LE_REFL          : thm := Rl.REAL_LE_REFL
def REAL_LE_ANTISYM       : thm := Rl.REAL_LE_ANTISYM
def REAL_LE_TRANS         : thm := Rl.REAL_LE_TRANS
def REAL_LE_LADD_IMP      : thm := Rl.REAL_LE_LADD_IMP
def REAL_LE_MUL           : thm := Rl.REAL_LE_MUL
def REAL_INV_0            : thm := Rl.REAL_INV_0
def REAL_OF_NUM_EQ        : thm := Rl.REAL_OF_NUM_EQ
def REAL_OF_NUM_LE        : thm := Rl.REAL_OF_NUM_LE
def REAL_OF_NUM_ADD       : thm := Rl.REAL_OF_NUM_ADD
def REAL_OF_NUM_MUL       : thm := Rl.REAL_OF_NUM_MUL
def real_lt               : thm := Rl.real_lt
def real_ge               : thm := Rl.real_ge
def real_gt               : thm := Rl.real_gt
def real_div              : thm := Rl.real_div
def real_max              : thm := Rl.real_max
def real_min              : thm := Rl.real_min
def REAL_HREAL_LEMMA1     : thm := Rl.REAL_HREAL_LEMMA1
def REAL_HREAL_LEMMA2     : thm := Rl.REAL_HREAL_LEMMA2
def REAL_COMPLETE_SOMEPOS : thm := Rl.REAL_COMPLETE_SOMEPOS


end Session
