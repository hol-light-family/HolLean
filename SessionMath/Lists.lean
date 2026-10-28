/- File: SessionMath/Lists.lean
lists.ml: the list theory, built by `initialize` when this module is imported,
in file order: the list definitions and theorems, MONO_ALL (prepended to the
monotonicity store), the evaluation conversions, the `char` type with the
`string` abbreviation, and the char/string machinery.
-/
import SessionMath.IndTypes
import HolMath.Lists

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Simp HolCore.Theorems HolCore.Classic

namespace Session

private def ioOk' {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")


/- lists.ml: the reproved list induction and the basic definitions layer.  -/
/- ---------------------------------------------------------------------- -/

/-- `list_INDUCT'` (lists.ml 18-20): the `!h t. P t ==> P (CONS h t)`-shaped
    re-proof of the stored `list_INDUCT`, used by `LIST_INDUCT_TAC`. -/
initialize listInduct' : thm ←
  ioOk' "prove_list_INDUCT'" (HolMath.Lists.prove_list_INDUCT' list_INDUCT).run

def list_INDUCT' : thm := listInduct'

/-- `LIST_INDUCT_TAC` (lists.ml 17): structural induction on lists. -/
def LIST_INDUCT_TAC : tactic := HolMath.Lists.LIST_INDUCT_TAC list_INDUCT'

/-- The `lists.ml` basic-definitions layer (the 28 recursive definitions of
    lines 28-143).  `setupListDefs` DECLARES CONSTANTS (`HD`, `TL`, `APPEND`,
    ...), so it runs exactly ONCE PER PROCESS — here an `initialize`. -/
initialize listDefsLayer : HolMath.Lists.ListDefs ← do
  let distinctness_list ← ioOk' "distinctness list" (distinctness "list")
  ioOk' "setupListDefs" (HolMath.Lists.setupListDefs list_RECURSION Nm.num_RECURSION
    distinctness_list new_recursive_definition).run

def listDefs : HolMath.Lists.ListDefs := listDefsLayer

/- ---------------------------------------------------------------------- -/
/- lists.ml: the theorem bundles and the evaluation conversions.           -/
/- ---------------------------------------------------------------------- -/

/-- `ListThms1` (lists.ml 148-400, 50 theorems). -/
initialize listThms1Layer : HolMath.Lists.ListThms1 ← do
  let dl ← ioOk' "distinctness list" (distinctness "list")
  let il ← ioOk' "injectivity list" (injectivity "list")
  ioOk' "setupListThms1" (HolMath.Lists.setupListThms1 listDefs dl il list_INDUCT'
    MESON_TAC ASM_MESON_TAC MESON Nm arith1 arith2 arith3 triviaLayer Pr).run

def listThms1 : HolMath.Lists.ListThms1 := listThms1Layer

/-- `ListThms2` (lists.ml 405-697, 51 theorems). -/
initialize listThms2Layer : HolMath.Lists.ListThms2 ←
  ioOk' "setupListThms2" (HolMath.Lists.setupListThms2 listDefs listThms1 list_INDUCT list_INDUCT'
    MESON_TAC ASM_MESON_TAC MESON Nm arith1 arith2 arith3 arith5 triviaLayer CnA o_DEF I_DEF).run

def listThms2 : HolMath.Lists.ListThms2 := listThms2Layer

/-- The `LENGTH_CONV`/`EL_CONV`/`REVERSE_CONV`/`LIST_OF_SEQ_CONV` proformas
    (lists.ml 751-876). -/
initialize listEvalConvsLayer : HolMath.Lists.ListEvalConvs ←
  ioOk' "setupListEvalConvs" (HolMath.Lists.setupListEvalConvs listDefs listThms1 arith1
    NUM_SUC_CONV num_CONV).run

private def listEvalConvs : HolMath.Lists.ListEvalConvs := listEvalConvsLayer

/-- `LENGTH_CONV` (lists.ml 751-778). -/
def LENGTH_CONV : ioconv := fun tm => listEvalConvs.LENGTH_CONV tm
/-- `EL_CONV` (lists.ml 780-807). -/
def EL_CONV : ioconv := fun tm => listEvalConvs.EL_CONV tm
/-- `REVERSE_CONV` (lists.ml 809-834). -/
def REVERSE_CONV : ioconv := fun tm => listEvalConvs.REVERSE_CONV tm
/-- `LIST_OF_SEQ_CONV` (lists.ml 836-876). -/
def LIST_OF_SEQ_CONV : ioconv := fun tm => listEvalConvs.LIST_OF_SEQ_CONV tm

/-- `LIST_CONV conv` (lists.ml 740-746): apply `conv` down a list. -/
def LIST_CONV : conv → conv := HolMath.Lists.LIST_CONV

/-- `LIST_CONV` for IO-valued conversions (e.g. `num_CONV`). -/
def LIST_CONV_IO : ioconv → ioconv := HolMath.Lists.LIST_CONV_IO

/-- `mk_cons h t` (lists.ml 702-705). -/
def mk_cons : term → term → IO (Except String term) := HolMath.Lists.mk_cons
/-- `mk_list (tms,ty)` (lists.ml 707-712). -/
def mk_list : List term → hol_type → IO (Except String term) := HolMath.Lists.mk_list
/-- `mk_flist tms` (lists.ml 714-716). -/
def mk_flist : List term → IO (Except String term) := HolMath.Lists.mk_flist

/-- The two extra monotonicity theorems `MONO_ALL`/`MONO_ALL2` (lists.ml
    722-731).  Forcing this layer performs the lists.ml 733 registration side
    effect:
      `monotonicity_theorems := [MONO_ALL; MONO_ALL2] @ !monotonicity_theorems`
    i.e. it PREPENDS both, in that order, onto the LIVE
    `theMonotonicityTheorems` ref (not a snapshot), so `MONO_TAC` /
    `prove_monotonicity_hyps`, which RE-READ the ref on every use, see the
    additions. -/
initialize listsMonoLayer : HolMath.Lists.MonoAllThms ← do
  let m ← ioOk' "setupMonoAll" (HolMath.Lists.setupMonoAll listDefs list_INDUCT' ASM_MESON_TAC).run
  -- lists.ml 733:
  --   monotonicity_theorems := [MONO_ALL; MONO_ALL2] @ !monotonicity_theorems
  let cur ← theMonotonicityTheorems.get
  theMonotonicityTheorems.set (m.MONO_ALL :: m.MONO_ALL2 :: cur)
  pure m

def listsMono : HolMath.Lists.MonoAllThms := listsMonoLayer

/-- `MONO_ALL` (lists.ml 722-725). -/
def MONO_ALL : thm := listsMono.MONO_ALL
/-- `MONO_ALL2` (lists.ml 727-731). -/
def MONO_ALL2 : thm := listsMono.MONO_ALL2

/- ---------------------------------------------------------------------- -/
/- lists.ml: the `char` type, `string` abbreviation, and the char/string  -/
/- syntax constructors + equality conversions (lines 877-998).            -/
/- ---------------------------------------------------------------------- -/

/-- `new_type_abbrev (s, ty)` (Preterm). -/
def new_type_abbrev (s : String) (ty : hol_type) : IO Unit :=
  HolCore.Preterm.new_type_abbrev s ty

/-- `(char_INDUCT, char_RECURSION)` (lists.ml 881-882):
    `define_type "char = ASCII bool bool bool bool bool bool bool bool"`.
    Forcing it also installs the `string` type abbreviation (lists.ml 884). -/
initialize charTypeLayer : thm × thm ← do
  let x ← ioOk' "define_type char"
    (define_type "char = ASCII bool bool bool bool bool bool bool bool")
  -- lists.ml 884: new_type_abbrev("string",`:char list`).
  let ty ← ioOk' "string abbrev parse" (HolCore.Parser.parse_type "char list")
  new_type_abbrev "string" ty
  pure x

/-- `char_INDUCT` (lists.ml 881). -/
def char_INDUCT : thm := charTypeLayer.1
/-- `char_RECURSION` (lists.ml 882). -/
def char_RECURSION : thm := charTypeLayer.2

/-- The `char` `hol_type`, used as `mk_string`'s element type. -/
initialize charTyLayer : hol_type ←
  ioOk' "parse char" (HolCore.Parser.parse_type "char")

def charTy : hol_type := charTyLayer

/-- The `CharStringMachinery` bundle (lists.ml 886-998): the pre-proved `ASCII`
    inequality families, the string-cons lemmas, the 256-entry `codes` array,
    and the schematic variables.  Depends on `injectivity "char"` (populated
    by `define_type "char"`) and the two `lists.ml` cons lemmas
    `CONS_11`/`NOT_CONS_NIL`. -/
initialize charStringMachineryLayer : HolMath.Lists.CharStringMachinery ← do
  let injChar ← ioOk' "injectivity char" (injectivity "char")
  ioOk' "setupCharStringMachinery"
    (HolMath.Lists.setupCharStringMachinery injChar listThms1.CONS_11
      listThms1.NOT_CONS_NIL MESON_TAC).run

private def charStringMachinery : HolMath.Lists.CharStringMachinery := charStringMachineryLayer

/-- `dest_char` (lists.ml 886, 900): `char_of_term`. -/
def dest_char : term → Except String Char := HolMath.Lists.dest_char
/-- `mk_char` (lists.ml 919): the `ASCII` term for a character. -/
def mk_char (c : Char) : Except String term := HolMath.Lists.mk_char charStringMachinery c
/-- `dest_string` (lists.ml 901-908): the (escaped) string a `char list` denotes. -/
def dest_string : term → Except String String := HolMath.Lists.dest_string
/-- `mk_string` (lists.ml 920-923): the `char list` term for a string. -/
def mk_string (s : String) : IO (Except String term) := HolMath.Lists.mk_string charStringMachinery s
/-- `CHAR_EQ_CONV` (lists.ml 980-984): decide equality of two chars. -/
def CHAR_EQ_CONV : conv := HolMath.Lists.CHAR_EQ_CONV charStringMachinery
/-- `STRING_EQ_CONV` (lists.ml 985-988): decide equality of two strings. -/
def STRING_EQ_CONV : conv := HolMath.Lists.STRING_EQ_CONV charStringMachinery

/- ---------------------------------------------------------------------- -/
/- lists.ml's bundles, touched in file order so that each load-time effect -/
/- (the monotonicity registration, the `string` abbrev, the net snapshots) -/
/- happens where it does in HOL Light:                                     -/
/-   listThms1.NOT_CONS_NIL, listThms2.ALL_APPEND, listsMono.MONO_ALL,      -/
/-   listEvalConvs (lists.ml 751-876);                                      -/
/-   char_INDUCT (lists.ml 881-884, installs the `string` abbrev),          -/
/-   charStringMachinery (lists.ml 886-998).                                -/
/- ---------------------------------------------------------------------- -/
initialize ensureIndTypesListsProcs : Unit ← do
  -- (ind_types.ml 1421-1572 ran above, in `unwindMatchLayer`.)
  -- lists.ml, in file order.
  let _ := listThms1.NOT_CONS_NIL
  let _ := listThms2.ALL_APPEND
  let _ := listsMono.MONO_ALL
  let _ := listEvalConvs
  -- lists.ml 881-884: char type + `string` abbrev, BEFORE sets.ml's
  -- `:string` annotations need it.
  let _ := char_INDUCT
  let _ := charStringMachinery


end Session
