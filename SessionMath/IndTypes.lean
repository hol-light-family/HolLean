/- File: SessionMath/IndTypes.lean
ind_types.ml: inductive types.  The define_type bootstrap, which defines the
`sum`, `option` and `list` types (possible once per process), is one
`initialize`; `UNWIND_CONV`, `MATCH_CONV` and `FORALL_UNWIND_CONV` are built
at the end of the file (`unwindMatchLayer`, which also runs MATCH_CONV's
`extend_basic_convs`).  The stores `define_type` changes
(`theBasicRectypeNet`, `theDistinctnessStore`, `theInjectivityStore`,
`theTheInductiveTypes`) are `IO.Ref`s.
-/
import SessionMath.Grobner
import HolMath.IndTypes

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Simp HolCore.Theorems HolCore.Classic

namespace Session

private def ioOk' {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")


/- ---------------------------------------------------------------------- -/
/- ind_types.ml 1022-1024: the three stateful stores.  These are genuine   -/
/- session state (`define_type` mutates them), so they stay as refs.       -/
/- ---------------------------------------------------------------------- -/

/-- `basic_rectype_net = ref empty_net` (ind_types.ml 1022). -/
initialize theBasicRectypeNet :
    IO.Ref (HolCore.Nets.net Simp.gconv) ← IO.mkRef HolCore.Nets.empty_net

/-- `distinctness_store = ref ["bool", TAUT `(T <=> F) <=> F`]` (ind_types.ml
    1023).  The seed `TAUT` is an IO computation, run here when the module
    is loaded. -/
initialize theDistinctnessStore : IO.Ref HolMath.IndTypes.RectypeStore ← do
  let boolThm ← ioOk' "distinctness seed TAUT"
    (TAUT (← ioOk' "distinctness seed parse" (Parser.parse_term "(T <=> F) <=> F")))
  IO.mkRef [("bool", boolThm)]

/-- `injectivity_store = ref []` (ind_types.ml 1024). -/
initialize theInjectivityStore : IO.Ref HolMath.IndTypes.RectypeStore ← IO.mkRef []

/-- `!distinctness_store` — the current distinctness store contents. -/
def distinctness_store : IO HolMath.IndTypes.RectypeStore := theDistinctnessStore.get

/-- `!injectivity_store` — the current injectivity store contents. -/
def injectivity_store : IO HolMath.IndTypes.RectypeStore := theInjectivityStore.get

/-- `!basic_rectype_net` — the current basic rectype net. -/
def basic_rectype_net : IO (HolCore.Nets.net Simp.gconv) := theBasicRectypeNet.get

/- ---------------------------------------------------------------------- -/
/- ind_types.ml 902-959: the two per-axiom provers whose proformas are     -/
/- built once.  They are CLOSURES (`thm → ...`), which do not survive       -/
/- separate compilation / `dlopen` as function-typed `initialize`           -/
/- constants, so — exactly as Arith's procs / CalcNum's conversion caches — -/
/- they live in plain `Option` refs, seeded by the forcing block            -/
/- `ensurePcProvers` below (which runs before the ind_types bootstrap that  -/
/- consumes them, via declaration order).                                   -/
/- ---------------------------------------------------------------------- -/

initialize thePcInjective : IO.Ref (Option (thm → ExceptT String IO thm)) ← IO.mkRef none
initialize thePcDistinct : IO.Ref (Option (thm → ExceptT String IO thm)) ← IO.mkRef none

/-- Build the two per-axiom provers' proformas once, in ind_types.ml order
    (902, 928).  Seeds the closure-holding refs before the bootstrap. -/
initialize ensurePcProvers : Unit ← do
  -- `prove_constructors_injective`'s `DEPAIR` net (ind_types.ml 902-926).
  thePcInjective.set (some (← ioOk' "prove_constructors_injective"
    (HolMath.IndTypes.prove_constructors_injective T.BETA_THM Pr.PAIR_EQ
      HolMath.Pair.mk_pair).run))
  -- `prove_constructors_distinct`'s `num_ty`/`NEGATE` tautology (ind_types.ml 928-959).
  thePcDistinct.set (some (← ioOk' "prove_constructors_distinct"
    (HolMath.IndTypes.prove_constructors_distinct T.BETA_THM Nm.numK NUM_EQ_CONV).run))

private def pcInjective (ax : thm) : ExceptT String IO thm := do
  match ← (thePcInjective.get : IO _) with
  | some f => f ax
  | none => throw "prove_constructors_injective not initialized"

private def pcDistinct (ax : thm) : ExceptT String IO thm := do
  match ← (thePcDistinct.get : IO _) with
  | some f => f ax
  | none => throw "prove_constructors_distinct not initialized"


/-- `extend_rectype_net (tyname,(_,_,rth))` (ind_types.ml 1026-1033): reads the
    current three store contents from their refs, calls the pure library
    `extend_rectype_net`, and writes the updated contents back. -/
def extend_rectype_net (entry : String × (Int × thm × thm)) :
    IO (Except String Unit) := do
  let curNet ← theBasicRectypeNet.get
  let curDist ← theDistinctnessStore.get
  let curInj ← theInjectivityStore.get
  match ← (HolMath.IndTypes.extend_rectype_net pcDistinct pcInjective
            entry curNet curDist curInj).run with
  | .error e => return .error e
  | .ok (net', dist', inj') => do
      theBasicRectypeNet.set net'
      theDistinctnessStore.set dist'
      theInjectivityStore.set inj'
      return .ok ()

/-- `ISO`, `ISO_REFL`, `ISO_FUN`, `ISO_USAGE` (ind_types.ml 1061-1080). -/
def setupISO : IO (Except String (thm × thm × thm × thm)) :=
  HolMath.IndTypes.setupISO new_definition MESON_TAC

/- ---------------------------------------------------------------------- -/
/- ind_types.ml 1390-1394: `the_inductive_types`, keyed by the RAW SPEC    -/
/- STRING.  Genuine session state (`define_type` mutates it); seeded by the -/
/- bootstrap with the `list`/`option`/`sum` entries, in OCaml order.        -/
/- ---------------------------------------------------------------------- -/

initialize theTheInductiveTypes :
    IO.Ref (List (String × (thm × thm))) ← IO.mkRef []

/-- `!the_inductive_types` — the current contents. -/
def the_inductive_types : IO (List (String × (thm × thm))) := theTheInductiveTypes.get

/- ---------------------------------------------------------------------- -/
/- ind_types.ml: the once-per-process bootstrap.                           -/
/-                                                                        -/
/- OCaml runs ALL of ind_types.ml EAGERLY at load, so `buildRaw3Ctx` (which -/
/- DEFINES the `sum`/`option`/`list` types and declares the injection       -/
/- infrastructure, each once-per-process) becomes a single eager            -/
/- `initialize`.  The `IndTypesThms` injection bundle and the two           -/
/- `FORALL_OPTION`/`EXISTS_OPTION` theorems are captured out of it.         -/
/- ---------------------------------------------------------------------- -/

/-- The whole ind_types.ml bootstrap result: the nested-type capability
    bundle `DefTypeRaw3`, the injection-infrastructure `IndTypesThms`, the two
    option theorems, and the `list`/`option`/`sum` induction/recursion
    theorems. -/
structure IndTypesBootstrap where
  R : HolMath.IndTypes.DefTypeRaw3
  K : HolMath.IndTypes.IndTypesThms
  forallOption : thm
  existsOption : thm
  list_INDUCT : thm
  list_RECURSION : thm
  option_INDUCT : thm
  option_RECURSION : thm
  sum_INDUCT : thm
  sum_RECURSION : thm
  option_DISTINCT : thm
  option_INJ : thm

deriving instance Inhabited for IndTypesBootstrap

/-- Build the ind_types.ml bootstrap (ind_types.ml 13-1394), EAGERLY.  Runs,
    in order: `setupIndTypes` (the injection infrastructure), `mkRawCtx`
    (`setupDefTypeRaw`), the `sum` type and `OUTL`/`OUTR`, `setupDefTypeRaw2`,
    `option` and `list`, `FORALL_OPTION_THM`/`EXISTS_OPTION_THM`, the
    `inductive_type_store` registration + `do_list extend_rectype_net`,
    `option_DISTINCT`/`option_INJ`, `setupISO`, `setupDefTypeRaw3`, and finally
    seeds `the_inductive_types` with the three spec-string entries.  Every type
    definition is once-per-process, so this is a strict one-shot — here an
    `initialize`, which runs exactly once at import. -/
private def buildIndTypesBootstrap : IO (Except String IndTypesBootstrap) :=
  ExceptT.run do
  let nbtd := fun a b c d => Kernel.new_basic_type_definition a b c d
  let dnir := derive_nonschematic_inductive_relations
  let pmh  := prove_monotonicity_hyps
  -- ind_types.ml 13-300: the injection infrastructure.
  let K ← (HolMath.IndTypes.setupIndTypes Nm arith1 arith2
             arith5 CnA triviaLayer ETA_AX new_definition
             new_specification new_inductive_definition new_recursive_definition
             prove_inductive_relations_exist : IO (Except String _))
  -- ind_types.ml 302-738: the first define_type_raw.
  let D ← HolMath.IndTypes.setupDefTypeRaw Pr.FST Pr.SND K.FCONS T.BETA_THM K.CONSTR_REC indAux.1
            HolMath.Pair.mk_pair dnir pmh new_definition nbtd
  -- ind_types.ml 768-774: the sum type, then OUTL/OUTR.
  let (sumI, sumR) ← HolMath.IndTypes.sum_INDUCT_RECURSION D
  let outl ← HolMath.IndTypes.defineOUTL new_recursive_definition sumR
  let outr ← HolMath.IndTypes.defineOUTR new_recursive_definition sumR
  -- ind_types.ml 785-886: the second define_type_raw; option and list.
  let D2 ← HolMath.IndTypes.setupDefTypeRaw2 D outl outr
  let (optI, optR) ← HolMath.IndTypes.option_INDUCT_RECURSION D2
  let (lstI, lstR) ← HolMath.IndTypes.list_INDUCT_RECURSION D2
  -- ind_types.ml 889-896: FORALL_OPTION_THM and EXISTS_OPTION_THM.
  let fa ← HolMath.IndTypes.prove_FORALL_OPTION_THM optI
  let ex ← HolMath.IndTypes.prove_EXISTS_OPTION_THM fa MESON MESON_TAC
  -- ind_types.ml 1009-1013: add list/option/sum to `inductive_type_store`, in
  -- OCaml order, ahead of whatever is already there (`num`, `prod`, `1`, `bool`).
  let existing ← (theInductiveTypeStore.get : IO _)
  let seeded := [("list", (2, lstI, lstR)), ("option", (2, optI, optR)),
                 ("sum", (2, sumI, sumR))] ++ existing
  theInductiveTypeStore.set seeded
  -- ind_types.ml 1035: `do_list extend_rectype_net (!inductive_type_store)`.
  for entry in seeded do
    let _ ← ExceptT.mk (extend_rectype_net entry)
  -- ind_types.ml 1049-1055: option_DISTINCT and option_INJ.
  let optDist ← ExceptT.mk (do
    match HolMath.IndTypes.distinctness (← theDistinctnessStore.get) "option" with
    | .error e => return .error e
    | .ok th => (HolMath.IndTypes.prove_option_DISTINCT th).run)
  let optInj ← ExceptT.mk (do
    match HolMath.IndTypes.injectivity (← theInjectivityStore.get) "option" with
    | .error e => return .error e
    | .ok th => (HolMath.IndTypes.prove_option_INJ th).run)
  -- ind_types.ml 1061: ISO is defined after sum, option and list (1009-1035).
  let (iso, isoRefl, isoFun, isoUsage) ← (setupISO : IO (Except String _))
  -- ind_types.ml 1084-1281: the third define_type_raw.  `getStore` and
  -- `addEntries` act on the live `theInductiveTypeStore` ref; `addEntries` does
  -- both of ind_types.ml 1385-1386's side effects, in order.
  let R ← HolMath.IndTypes.setupDefTypeRaw3 D2 iso isoRefl isoFun isoUsage
    ETA_AX SELECT_AX C.FUN_EQ_THM
    (theInductiveTypeStore.get)
    (fun es => do
      let cur ← theInductiveTypeStore.get
      theInductiveTypeStore.set (es ++ cur)
      -- `do_list extend_rectype_net newentries` (ind_types.ml 1386) is part of
      -- a `;`-sequence, so its failure propagates.
      for e in es do
        match ← extend_rectype_net e with
        | .error err => return .error err
        | .ok _ => pure ()
      return .ok ())
  -- ind_types.ml 1390-1394: seed the spec-string keyed store, in OCaml order.
  theTheInductiveTypes.set [
    ("list = NIL | CONS A list", (lstI, lstR)),
    ("option = NONE | SOME A", (optI, optR)),
    ("sum = INL A | INR B", (sumI, sumR))]
  return { R, K, forallOption := fa, existsOption := ex,
           list_INDUCT := lstI, list_RECURSION := lstR,
           option_INDUCT := optI, option_RECURSION := optR,
           sum_INDUCT := sumI, sum_RECURSION := sumR,
           option_DISTINCT := optDist, option_INJ := optInj }

/-- The ind_types.ml bootstrap, run eagerly at import (once per process). -/
initialize indTypesBoot : IndTypesBootstrap ←
  ioOk' "buildIndTypesBootstrap" buildIndTypesBootstrap

/-- The nested-type capability bundle, built once per process. -/
def raw3Ctx : HolMath.IndTypes.DefTypeRaw3 := indTypesBoot.R

/-- `do_list extend_rectype_net (!inductive_type_store)` (ind_types.ml 1035):
    run `extend_rectype_net` over every type currently in the inductive type
    store. -/
def do_extend_rectype_net : IO (Except String Unit) := do
  let rec go : List (String × (Int × thm × thm)) → IO (Except String Unit)
    | [] => return .ok ()
    | e :: es => do
      match ← extend_rectype_net e with
      | .error err => return .error err
      | .ok _ => go es
  go (← theInductiveTypeStore.get)

/-- `option_DISTINCT` (ind_types.ml 1049-1051):
    `prove (`!a:A. ~(SOME a = NONE)`, REWRITE_TAC[distinctness "option"])`,
    proved by the bootstrap. -/
def option_DISTINCT : IO (Except String thm) := pure (.ok indTypesBoot.option_DISTINCT)

/-- `option_INJ` (ind_types.ml 1053-1055):
    `prove (`!a b:A. SOME a = SOME b <=> a = b`, REWRITE_TAC[injectivity "option"])`,
    proved by the bootstrap. -/
def option_INJ : IO (Except String thm) := pure (.ok indTypesBoot.option_INJ)

/- Layer-record accessors (Session 3709-3740), for consumers that build
   `setupIndTypes` / `define_type_raw3` themselves. -/
/-- The `theorems.ml` layer record. -/
def theoremThms : TheoremThms := T
/-- The `class.ml` layer record. -/
def classThms : ClassThms := C
/-- The `nums.ml` layer record. -/
def numsThms : HolMath.Nums.NumsThms := Nm
/-- The `arith.ml` part-1 record. -/
def arith1Thms : HolMath.Arith.ArithThms1 := arith1
/-- The `arith.ml` part-2 record. -/
def arith2Thms : HolMath.Arith.ArithThms2 := arith2
/-- The `arith.ml` part-5 record. -/
def arith5Thms : HolMath.Arith.ArithThms5 := arith5
/-- The `arith.ml` part-3 record. -/
def arith3Thms : HolMath.Arith.ArithThms3 := arith3
/-- The `arith.ml` part-4 record. -/
def arith4Thms : HolMath.Arith.ArithThms4 := arith4
/-- The `pair.ml` theorem record. -/
def pairThms : HolMath.Pair.PairThms := Pr
/-- The `calc_num.ml` `ARITH_*` rewrites record. -/
def calcNumArith : HolMath.CalcNum.ArithRewrites := CnA
/-- The `trivia.ml` layer record. -/
def triviaThms : HolCore.Trivia.TriviaThms := triviaLayer

/- ---------------------------------------------------------------------- -/
/- The three derived-theorem provers (ind_types.ml 902-1006).             -/
/- ---------------------------------------------------------------------- -/

/-- `prove_constructors_injective ax` (ind_types.ml 902-926). -/
def prove_constructors_injective (ax : thm) : IO (Except String thm) :=
  (pcInjective ax).run

/-- `prove_constructors_distinct ax` (ind_types.ml 929-959).  The OCaml returns
    `end_itlist CONJ` of the pairwise inequalities; the library conjoins them. -/
def prove_constructors_distinct (ax : thm) : IO (Except String thm) :=
  (pcDistinct ax).run

/-- `prove_cases_thm th` (ind_types.ml 964-1006). -/
def prove_cases_thm (th : thm) : IO (Except String thm) :=
  (HolMath.IndTypes.prove_cases_thm indAux.1 th).run

/- ---------------------------------------------------------------------- -/
/- The store readers.  The define_type bootstrap ran at import, as         -/
/- ind_types.ml runs at load in HOL Light, so these read the refs directly.-/
/- ---------------------------------------------------------------------- -/

/-- `distinctness ty = assoc ty (!distinctness_store)` (ind_types.ml 1041). -/
def distinctness (ty : String) : IO (Except String thm) := do
  return HolMath.IndTypes.distinctness (← theDistinctnessStore.get) ty

/-- `injectivity ty = assoc ty (!injectivity_store)` (ind_types.ml 1043). -/
def injectivity (ty : String) : IO (Except String thm) := do
  return HolMath.IndTypes.injectivity (← theInjectivityStore.get) ty

/-- `cases ty` (ind_types.ml 1045-1047). -/
def cases (ty : String) : IO (Except String thm) := do
  let store ← theInductiveTypeStore.get
  (HolMath.IndTypes.cases indAux.1 Nm.num_CASES store ty).run

/-- Read a `list`/`option`/`sum` entry out of the inductive type store. -/
private def storeEntry (ty : String) : IO (Int × thm × thm) := do
  let store ← theInductiveTypeStore.get
  match HolCore.Lib.assoc ty store with
  | Except.ok e => pure e
  | Except.error _ => throw (IO.userError s!"storeEntry: no entry for {ty}")

/-- `list_INDUCT` / `list_RECURSION` (ind_types.ml 884-886): what `lists.ml`
    threads into its ~28 `new_recursive_definition list_RECURSION` calls and
    into `LIST_INDUCT_TAC`. -/
def list_INDUCT : thm := indTypesBoot.list_INDUCT
def list_RECURSION : thm := indTypesBoot.list_RECURSION
def option_INDUCT : thm := indTypesBoot.option_INDUCT
def option_RECURSION : thm := indTypesBoot.option_RECURSION
def sum_INDUCT : thm := indTypesBoot.sum_INDUCT
def sum_RECURSION : thm := indTypesBoot.sum_RECURSION

/-- The ind_types.ml 13-300 injection infrastructure. -/
def IndK : HolMath.IndTypes.IndTypesThms := indTypesBoot.K

def NUMPAIR : thm := IndK.NUMPAIR
def NUMPAIR_INJ_LEMMA : thm := IndK.NUMPAIR_INJ_LEMMA
def NUMPAIR_INJ : thm := IndK.NUMPAIR_INJ
def NUMPAIR_DEST : thm := IndK.NUMPAIR_DEST
def NUMSUM : thm := IndK.NUMSUM
def NUMSUM_INJ : thm := IndK.NUMSUM_INJ
def NUMSUM_DEST : thm := IndK.NUMSUM_DEST
def INJN : thm := IndK.INJN
def INJN_INJ : thm := IndK.INJN_INJ
def INJA : thm := IndK.INJA
def INJA_INJ : thm := IndK.INJA_INJ
def INJF : thm := IndK.INJF
def INJF_INJ : thm := IndK.INJF_INJ
def INJP : thm := IndK.INJP
def INJP_INJ : thm := IndK.INJP_INJ
def ZCONSTR : thm := IndK.ZCONSTR
def ZBOT : thm := IndK.ZBOT
def ZCONSTR_ZBOT : thm := IndK.ZCONSTR_ZBOT
def ZRECSPACE_RULES : thm := IndK.ZRECSPACE_RULES
def ZRECSPACE_INDUCT : thm := IndK.ZRECSPACE_INDUCT
def ZRECSPACE_CASES : thm := IndK.ZRECSPACE_CASES
def BOTTOM : thm := IndK.BOTTOM
def CONSTR : thm := IndK.CONSTR
def MK_REC_INJ : thm := IndK.MK_REC_INJ
def DEST_REC_INJ : thm := IndK.DEST_REC_INJ
def CONSTR_BOT : thm := IndK.CONSTR_BOT
def CONSTR_INJ : thm := IndK.CONSTR_INJ
def CONSTR_IND : thm := IndK.CONSTR_IND
def FCONS_UNDO : thm := IndK.FCONS_UNDO
def FNIL : thm := IndK.FNIL
def INJ_INVERSE2 : thm := IndK.INJ_INVERSE2

/-- `FORALL_OPTION_THM` (ind_types.ml 889). -/
def FORALL_OPTION_THM : thm := indTypesBoot.forallOption
/-- `EXISTS_OPTION_THM` (ind_types.ml 893). -/
def EXISTS_OPTION_THM : thm := indTypesBoot.existsOption

/-- `define_type s` (ind_types.ml 1396-1414), the stateful Session wrapper.
    Reads the current `the_inductive_types` contents, calls the pure-ish library
    `define_type` (the crude RAW-STRING benignity check, the four validation
    checks, and `define_type_raw3` on a miss), then writes back the (possibly)
    updated store. -/
def define_type_with (X : HolMath.IndTypes.DefTypeRaw3) (s : String) :
    IO (Except String (thm × thm)) := do
  let store ← the_inductive_types
  match ← (HolMath.IndTypes.define_type X store s).run with
  | .error e => return .error e
  | .ok (retval, store') => do
      theTheInductiveTypes.set store'
      return .ok retval

/-- `define_type s` (ind_types.ml 1396-1414) — the USER-FACING entry point, with
    the `Raw3Ctx` supplied automatically from the eager bootstrap. -/
def define_type (s : String) : IO (Except String (thm × thm)) :=
  define_type_with raw3Ctx s

/- ---------------------------------------------------------------------- -/
/- ind_types.ml: UNWIND_CONV / MATCH_CONV / FORALL_UNWIND_CONV            -/
/- (lines 1421-1572).  Built eagerly; `MATCH_CONV`'s setup performs the    -/
/- `do_list extend_basic_convs` side effect, and `BREAK_CONS_CONV`'s        -/
/- `!basic_rectype_net` is threaded in as `theBasicRectypeNet.get`, an IO   -/
/- action RE-READ on every application (NOT a snapshot), so rewrites for    -/
/- types defined after this layer are seen.                                -/
/- ---------------------------------------------------------------------- -/

/-- Caches for the `(UNWIND_CONV, MATCH_CONV)` pair (ind_types.ml 1421-1539)
    and `FORALL_UNWIND_CONV` (ind_types.ml 1540-1572).  These hold CLOSURES
    (ioconv), which do not survive separate compilation / `dlopen` as
    function-typed `initialize` constants (same reason as Arith's procs and
    CalcNum's conversion caches), so they are plain `Option` refs seeded in
    file order by the forcing block `ensureIndTypesListsProcs` below. -/
initialize theUnwindMatch : IO.Ref (Option (ioconv × ioconv)) ← IO.mkRef none
initialize theForallUnwind : IO.Ref (Option ioconv) ← IO.mkRef none

private def unwindMatchIO : IO (Except String (ioconv × ioconv)) := do
  match ← theUnwindMatch.get with
  | some p => return .ok p
  | none =>
    -- Built after the bootstrap (whose third define_type_raw's
    -- REWRITE_FUN_EQ_RULE net is made from `basic_net ()` before these basic
    -- convs are added — the bootstrap `initialize indTypesBoot` already ran).
    let P := pairAux
    match ← (HolMath.IndTypes.setupUnwindMatch
               P.MATCH P.SEQPATTERN P.FUNCTION P.UNGUARDED_PATTERN P.GUARDED_PATTERN
               P.GEQ_DEF C.COND_ID C.COND_CLAUSES T.CONJ_ASSOC
               MESON_TAC theBasicRectypeNet.get (Simp.extend_basic_convs B)).run with
    | .error e => return .error e
    | .ok p => do theUnwindMatch.set (some p); return .ok p

private def forallUnwindIO : IO (Except String ioconv) := do
  match ← theForallUnwind.get with
  | some c => return .ok c
  | none =>
    match ← (HolMath.IndTypes.setupForallUnwind MESON).run with
    | .error e => return .error e
    | .ok c => do theForallUnwind.set (some c); return .ok c

/-- `UNWIND_CONV` (ind_types.ml 1421-1539): `CHANGED_CONV UNWIND_CONV`. -/
def UNWIND_CONV : ioconv := fun tm => do
  match ← unwindMatchIO with
  | .ok p => p.1 tm
  | .error e => return .error e

/-- `MATCH_CONV` (ind_types.ml 1421-1539):
    `MATCH_SEQPATTERN_CONV_GEN ORELSEC MATCH_ONEPATTERN_CONV_GEN`. -/
def MATCH_CONV : ioconv := fun tm => do
  match ← unwindMatchIO with
  | .ok p => p.2 tm
  | .error e => return .error e

/-- `FORALL_UNWIND_CONV` (ind_types.ml 1540-1572). -/
def FORALL_UNWIND_CONV : ioconv := fun tm => do
  match ← forallUnwindIO with
  | .ok c => c tm
  | .error e => return .error e

/-- ind_types.ml 1421-1572, run here, at the end of ind_types.ml and before
    lists.ml (hol_lib.ml 91-92): build `UNWIND_CONV`/`MATCH_CONV` (which runs
    its `do_list extend_basic_convs`, so lists.ml's proofs see the new basic
    conversions) and `FORALL_UNWIND_CONV`. -/
initialize unwindMatchLayer : Unit ← do
  match ← unwindMatchIO with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"UNWIND_CONV/MATCH_CONV setup: {e}")
  match ← forallUnwindIO with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"FORALL_UNWIND_CONV setup: {e}")

/- ---------------------------------------------------------------------- -/

end Session
