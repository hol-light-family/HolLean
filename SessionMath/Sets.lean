/- File: SessionMath/Sets.lean
sets.ml (hol_lib.ml 99), basic set theory (predicates as sets), each layer
built by `initialize` when this module is imported, in sets.ml order.
sets.ml's four groups of `parse_as_infix` declarations each have their own
`initialize` at their file position: the fourteen head infixes (sets.ml
18-32), `CROSS` (2732), `UNION_OF`/`INTERSECTION_OF` (4001-4002) and
`has_inf`/`has_sup` (5030-5031).  int.ml's closing `prioritize_num` has
already run, as in HOL Light.

`HYP_TAC` takes a pure `rule`, so it needs one bridge from `IO` to a pure
value: `runExceptThm`, a safe `opaque` with an `implemented_by`
implementation.
-/
import SessionMath.Int
import HolMath.Sets

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Simp HolCore.Theorems HolCore.Classic HolCore.Trivia

namespace Session

private def ioOk' {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")

private def pt (s : String) : IO term := ioOk' s!"parse {s}" (HolCore.Parser.parse_term s)

/- ---------------------------------------------------------------------- -/
/- Dependencies that are not exported bare by an earlier Session module,   -/
/- as plain `def`s with the old Session's bodies                           -/
/- (Session 354/412/583/716-718/1002/1025/1122).                           -/
/- ---------------------------------------------------------------------- -/

/-- `Tv` (Session 1122): the trivia.ml bundle (`one`, `one_axiom`, ...). -/
def Tv : TriviaThms := triviaLayer

/-- `COND_ELIM_CONV` (Session 1002). -/
def COND_ELIM_CONV : term → IO (Except String thm) :=
  Classic.COND_ELIM_CONV B C.COND_ELIM_THM
/-- `REFUTE_THEN ttac` (Session 1025): classical refutation tactic. -/
def REFUTE_THEN (ttac : thm_tactic) : tactic :=
  Classic.REFUTE_THEN B (Simp.REWR_CONV B C.refuteThenPth) C.refuteF ttac

/-- `IMP_CONJ` (Session 2529 uses `T.IMP_CONJ` bare as `IMP_CONJ`). -/
def IMP_CONJ : thm := T.IMP_CONJ

/- The single IO->pure bridge sets.ml needs.  `HYP_TAC`'s `rule` argument is a
   PURE `thm -> Except String thm`, but `REWRITE_RULE`/`MATCH_MP` build a
   rewrite net in `IO`.  So this is a safe `opaque` with an
   `@[implemented_by]` implementation, like SessionCore/Base.lean's `runString`/`runTerm`.  The
   computation is deterministic over fixed theorem inputs, so forcing it is
   referentially transparent. -/
private unsafe def runExceptThmImpl (a : IO (Except String thm)) : Except String thm :=
  match unsafeIO a with
  | .ok r => r
  | .error _ => .error "runExceptThm: IO failure"
@[implemented_by runExceptThmImpl] opaque runExceptThm
  (a : IO (Except String thm)) : Except String thm

/- ---------------------------------------------------------------------- -/
/- sets.ml (hol_lib.ml 99).  Every structural stage is an `initialize`     -/
/- constant, forced at import in `ensureSets`'s EXACT file order           -/
/- (Session 8676-8723).  The four `parse_as_infix` groups are run by their -/
/- own `initialize Unit ←` at their file positions - the eager analogue of -/
/- Session's once-only `IO.Ref Bool` guards.  Getting the order wrong      -/
/- parses set terms at the wrong type, so do not reorder.                  -/
/- ---------------------------------------------------------------------- -/

/-- The FOURTEEN head infixes (sets.ml 18-32): IN/SUBSET/PSUBSET/INTER/UNION/
    DIFF/INSERT/DELETE/HAS_SIZE and the five cardinal comparisons.  Must run
    BEFORE `setupSetsCore`, whose bodies parse `x IN s`/`s UNION t`/... as
    those operators. -/
initialize setsInfixesLayer : Unit ← HolMath.Sets.setupSetsInfixes

/-- `SetsCore` (sets.ml 34-170): IN, EXTENSION, GSPEC, SETSPEC, IN_ELIM_THM,
    EMPTY, INSERT_DEF, UNIV, the operators, SUBSET/PSUBSET/DISJOINT/SING, the
    FINITE inductive triple, INFINITE, IMAGE, INJ/SURJ/BIJ, CHOICE, REST.  Each
    `new_definition`/`new_inductive_definition` CREATES a constant.  Forced
    after the head infixes so the bodies parse the operators and `{a,b,c}`/
    `{x|P}` desugar onto the freshly-real EMPTY/INSERT_DEF/GSPEC/SETSPEC. -/
initialize setsCoreLayer : HolMath.Sets.SetsCore ← do
  let _ := setsInfixesLayer
  ioOk' "setupSetsCore" (HolMath.Sets.setupSetsCore MESON_TAC
    new_definition new_inductive_definition).run
def SC : HolMath.Sets.SetsCore := setsCoreLayer

/-- `SetsProps` (sets.ml 171-308): the twenty-four basic membership lemmas,
    SET_TAC's raw material. -/
initialize setsPropsLayer : HolMath.Sets.SetsProps ←
  ioOk' "setupSetsProps" (HolMath.Sets.setupSetsProps SC MESON_TAC).run
def SP : HolMath.Sets.SetsProps := setsPropsLayer

/-- `SetsTactics` (sets.ml 309-355): `CHOICE_DEF` and the first SET_TAC
    consumers `NOT_EQUAL_SETS`, `INSERT_RESTRICT`, `UNIV_1`. -/
initialize setsTacticsLayer : HolMath.Sets.SetsTactics ←
  ioOk' "setupSetsTactics" (HolMath.Sets.setupSetsTactics SC SP Tv MESON_TAC).run
def STc : HolMath.Sets.SetsTactics := setsTacticsLayer

/-- `SetsInclusion` (sets.ml 356-475): emptiness/universality/subset/psubset. -/
initialize setsInclusionLayer : HolMath.Sets.SetsInclusion ←
  ioOk' "setupSetsInclusion" (HolMath.Sets.setupSetsInclusion SC SP MESON_TAC).run
def SIn : HolMath.Sets.SetsInclusion := setsInclusionLayer

/-- `SetsOperators` (sets.ml 476-855): union/intersection/disjoint/difference. -/
initialize setsOperatorsLayer : HolMath.Sets.SetsOperators ←
  ioOk' "setupSetsOperators" (HolMath.Sets.setupSetsOperators SC SP MESON_TAC MESON).run
def SOp : HolMath.Sets.SetsOperators := setsOperatorsLayer

/-- `SetsInsertDelete` (sets.ml 856-950): the insert/delete algebra. -/
initialize setsInsertDeleteLayer : HolMath.Sets.SetsInsertDelete ←
  ioOk' "setupSetsInsertDelete" (HolMath.Sets.setupSetsInsertDelete SC SP SIn MESON_TAC).run
def SID : HolMath.Sets.SetsInsertDelete := setsInsertDeleteLayer

/-- `SetsUnions` (sets.ml UNIONS block): the `UNIONS` clauses. -/
initialize setsUnionsLayer : HolMath.Sets.SetsUnions ←
  ioOk' "setupSetsUnions" (HolMath.Sets.setupSetsUnions SC SP MESON_TAC).run
def SUn : HolMath.Sets.SetsUnions := setsUnionsLayer

/-- `SetsInters` (sets.ml INTERS block): the `INTERS` clauses. -/
initialize setsIntersLayer : HolMath.Sets.SetsInters ←
  ioOk' "setupSetsInters" (HolMath.Sets.setupSetsInters SC SP MESON_TAC).run
def SIt : HolMath.Sets.SetsInters := setsIntersLayer

/-- `SetsImage` (sets.ml 951-1150 IMAGE block): the `IMAGE` algebra; threads
    the `I` combinator definition `I_DEF`. -/
initialize setsImageLayer : HolMath.Sets.SetsImage ←
  ioOk' "setupSetsImage" (HolMath.Sets.setupSetsImage SC SP SIn Tv I_DEF
    MESON_TAC ASM_MESON_TAC).run
def SIm : HolMath.Sets.SetsImage := setsImageLayer

/-- `SetsMisc` (sets.ml GSPEC/saturated-image block): the `EMPTY_GSPEC`/
    `IN_GSPEC`/`SET_PAIR_THM`/saturated-image family. -/
initialize setsMiscLayer : HolMath.Sets.SetsMisc ←
  ioOk' "setupSetsMisc" (HolMath.Sets.setupSetsMisc SC SP SIn SOp SIt SID SIm
    Pr MESON_TAC).run
def SMi : HolMath.Sets.SetsMisc := setsMiscLayer

/-- `SetsInduct` (sets.ml stronger-induction block): `FINITE_INDUCT_STRONG`. -/
initialize setsInductLayer : HolMath.Sets.SetsInduct ←
  ioOk' "setupSetsInduct" (HolMath.Sets.setupSetsInduct SC SP MESON_TAC).run
def SInd : HolMath.Sets.SetsInduct := setsInductLayer

/-- `SetsFunctions` (sets.ml 951-1382 function block): injectivity/surjectivity/
    bijection and factoring lemmas. -/
initialize setsFunctionsLayer : HolMath.Sets.SetsFunctions ←
  ioOk' "setupSetsFunctions" (HolMath.Sets.setupSetsFunctions SC SP Tv
    MESON_TAC ASM_MESON_TAC MESON).run
def SFn : HolMath.Sets.SetsFunctions := setsFunctionsLayer

/-- `SetsFinite` (sets.ml 1383-1796): the finite-set combining theorems. -/
initialize setsFiniteLayer : HolMath.Sets.SetsFinite ←
  ioOk' "setupSetsFinite" (HolMath.Sets.setupSetsFinite SC SP SIn SOp SID SUn SIt SIm SMi
    SFn SInd MESON_TAC ASM_MESON_TAC MESON ASM_METIS_TAC).run
def SFin : HolMath.Sets.SetsFinite := setsFiniteLayer

/-- `SetsRecursion` (sets.ml 1799-1988): the finite-set fold machinery
    `FINREC`/`ITSET`/`FINITE_RECURSION`.  The `FINREC` `new_recursive_def` and
    the `ITSET` `new_definition` are injected. -/
initialize setsRecursionLayer : HolMath.Sets.SetsRecursion ←
  ioOk' "setupSetsRecursion" (HolMath.Sets.setupSetsRecursion SC SP SID SFin SInd Nm
    MESON_TAC ASM_MESON_TAC SELECT_CONV
    new_recursive_definition new_definition).run
def SRec : HolMath.Sets.SetsRecursion := setsRecursionLayer

/-- `SetsCard` (sets.ml 1991-2243): finite cardinality (`CARD`, `CARD_CLAUSES`,
    `CARD_UNION`, ...), `FINITE_INDUCT_DELETE`, `HAS_SIZE`/`HAS_SIZE_CLAUSES`
    and the `HAS_SIZE_CONV` numeral-expansion conversion.  `CARD`/`HAS_SIZE`
    are injected `new_definition`s. -/
initialize setsCardLayer : HolMath.Sets.SetsCard ←
  ioOk' "setupSetsCard" (HolMath.Sets.setupSetsCard SC SP SIn SOp SID SUn SFin SInd
    SRec MESON_TAC ASM_MESON_TAC
    new_definition ADD_CLAUSES MULT_CLAUSES Nm.SUC_INJ Nm.NOT_SUC
    SUC_SUB1 ARITH ARITH_RULE ARITH_TAC WF_INDUCT_TAC
    num_CONV).run
def SCard : HolMath.Sets.SetsCard := setsCardLayer

/-- `SetsCard2` (sets.ml 2244-2652): cardinality of unions and images, choosing
    a smaller subset of a given size, and the parity of the fixed-point set of
    an involution. -/
initialize setsCard2Layer : HolMath.Sets.SetsCard2 ←
  ioOk' "setupSetsCard2" (HolMath.Sets.setupSetsCard2 SC SP SIn SOp SUn SIm SMi
    SFin SInd SFn SCard MESON_TAC ASM_MESON_TAC MESON
    LE_TRANS LET_TRANS LE_ANTISYM LE_REFL LT_REFL LT_LE LE_SUC
    LE_0 LE_ADD2 LE_ADD_LCANCEL EQ_IMP_LE ADD_EQ_0
    SUC_SUB1 num_WF EVEN_ADD EVEN_SUB ARITH
    ARITH_RULE ARITH_TAC ASM_ARITH_TAC INDUCT_TAC).run
def SCard2 : HolMath.Sets.SetsCard2 := setsCard2Layer

/-- The FIFTEENTH `parse_as_infix`: `CROSS 22 right` (sets.ml 2732), forced
    (Session `ensureSetsCrossInfix`) just before `SCross`. -/
initialize setsCrossInfixLayer : Unit ← HolMath.Sets.setupSetsCrossInfix

/-- `SetsCross` (sets.ml 2653-2924): the cardinality-of-product theorems and
    the Cartesian product operator `CROSS` with its algebra.  The `CROSS`
    `new_definition` CREATES a constant (its infix fixity set above). -/
initialize setsCrossLayer : HolMath.Sets.SetsCross ← do
  let _ := setsCrossInfixLayer
  ioOk' "setupSetsCross" (HolMath.Sets.setupSetsCross SC SP SIn SIm SMi SFin SInd
    SCard SCard2 Pr MESON_TAC ASM_MESON_TAC
    new_definition MULT_CLAUSES).run
def SCross : HolMath.Sets.SetsCross := setsCrossLayer

/-- `SetsFunspace` (sets.ml 2925-3324): extensional functions, restriction, the
    dependent function space / Cartesian product, the product of a family of
    maps, and the disjoint-union construction.  Its `ARB`/`EXTENSIONAL`/
    `RESTRICTION`/`cartesian_product`/`product_map`/`disjoint_union`
    `new_definition`s CREATE constants. -/
initialize setsFunspaceLayer : HolMath.Sets.SetsFunspace ←
  ioOk' "setupSetsFunspace" (HolMath.Sets.setupSetsFunspace SC SP SIn SIm SMi Pr Tv
    o_DEF MESON_TAC ASM_MESON_TAC new_definition).run
def SFun : HolMath.Sets.SetsFunspace := setsFunspaceLayer

/-- `SetsFunspace2` (sets.ml 3325-3548): cardinality of bounded-support function
    spaces, of type `bool`, and hence of the powerset.  Pure `prove`s. -/
initialize setsFunspace2Layer : HolMath.Sets.SetsFunspace2 ←
  ioOk' "setupSetsFunspace2" (HolMath.Sets.setupSetsFunspace2 SC SP SIn SOp SID SIm SMi
    SFin SCard SCard2 SCross Pr MESON_TAC ASM_MESON_TAC
    GEN_BETA_CONV INDUCT_TAC
    EXP LE_TRANS LE_MULT_RCANCEL LE_1 ARITH).run
def SFun2 : HolMath.Sets.SetsFunspace2 := setsFunspace2Layer

/-- `SetsInfinite` (sets.ml 3554-3697): the infinitude of the numbers, of
    strings, and of non-trivial real intervals.  `string_INFINITE` mentions
    `(:string)`, so before the proofs the char/string layer is forced
    (`char_INDUCT`, already forced by the Int import chain) and the lists.ml
    884 `new_type_abbrev("string",`:char list`)` is (re)installed so the parser
    expands `string` to `char list`. -/
initialize setsInfiniteLayer : HolMath.Sets.SetsInfinite ← do
  let _ := concl char_INDUCT
  match ← HolCore.Parser.parse_type "char list" with
  | .error e => throw (IO.userError s!"SInf: string abbrev parse: {e}")
  | .ok ty => new_type_abbrev "string" ty
  ioOk' "setupSetsInfinite" (HolMath.Sets.setupSetsInfinite SC SP SIn SMi SFin SCard SInd
    MESON_TAC INDUCT_TAC
    REAL_ARITH2 REAL_FIELD REAL_ARITH_TAC
    arith2.LT arith2.LE arith1.ADD1 arith2.LT_SUC_LE arith3.NOT_LT arith3.LT_REFL
    arith3.LE_CASES arith3.LE_TRANS arith3.NOT_LE arith3.LT_IMP_LE arith2.LE_SUC_LT
    listThms1.LENGTH_REPLICATE
    RaL.REAL_NOT_LT RT3.REAL_LT_ADDR RT8.REAL_LT_DIV RaL.REAL_SUB_LT
    RT7.REAL_LT_LDIV_EQ RT1.REAL_LT_MUL Rl.REAL_OF_NUM_EQ
    Rl.REAL_LE_ANTISYM Rl.REAL_LE_REFL).run
def SInf : HolMath.Sets.SetsInfinite := setsInfiniteLayer

/-- `SetsList` (sets.ml 3697-3997): finite-set indexing and enumeration of
    subsets of N, the mapping between finite sets and lists (`set_of_list`/
    `list_of_set` INTRODUCED HERE), and `pairwise`. -/
initialize setsListLayer : HolMath.Sets.SetsList ←
  ioOk' "setupSetsList" (HolMath.Sets.setupSetsList SC SP SIn SUn SIm SID SInd SFin
    SCard SInf Nm arith4 Wf MESON_TAC ASM_MESON_TAC
    INDUCT_TAC
    list_INDUCT list_INDUCT' list_RECURSION
    listDefs.LENGTH listDefs.MEM listDefs.MAP
    listThms1.NOT_CONS_NIL listThms1.CONS_11
    listThms1.LENGTH_EQ_NIL listThms1.MEM_APPEND
    arith2.LT arith3.LT_IMP_LE arith3.LE_LT arith3.LE_ANTISYM arith3.NOT_LT
    arith3.NOT_LE arith2.LE_0 arith3.LT_REFL Nm.SUC_INJ Nm.NOT_SUC
    ARITH_RULE prove_recursive_functions_exist
    COND_ELIM_CONV SELECT_CONV
    new_recursive_definition new_definition).run
def SL : HolMath.Sets.SetsList := setsListLayer

/-- The SIXTEENTH/SEVENTEENTH `parse_as_infix`: `UNION_OF`/`INTERSECTION_OF 20
    right` (sets.ml 4001-4002), forced just before `SUO`. -/
initialize setsUnionOfInfixLayer : Unit ← HolMath.Sets.setupSetsUnionOfInfix

/-- `SetsUnionOf` (sets.ml 3998-4364): the `UNION_OF`/`INTERSECTION_OF`
    combinators and their ARBITRARY and FINITE cases.  The two operators' infix
    fixity is set above. -/
initialize setsUnionOfLayer : HolMath.Sets.SetsUnionOf ← do
  let _ := setsUnionOfInfixLayer
  ioOk' "setupSetsUnionOf" (HolMath.Sets.setupSetsUnionOf SC SP SOp SUn SIt SIm SMi
    SFin SCross ETA_AX MESON_TAC MESON
    new_definition).run
def SUO : HolMath.Sets.SetsUnionOf := setsUnionOfLayer

/-- `SetsCardComp` (sets.ml 4365-4695): the finish of the set_of_list
    cardinality section, the classic finite injectivity/surjectivity/bijection
    theorems, `WF_FINITE`/`WF_PSUBSET`, and the cardinal-comparison definitions
    `le_c`/`lt_c`/`eq_c`/`ge_c`/`gt_c` with `LE_C`/`GE_C`/`COUNTABLE`.
    Registers NO new infix (the five cardinal comparisons were declared with
    the head infixes). -/
initialize setsCardCompLayer : HolMath.Sets.SetsCardComp ←
  ioOk' "setupSetsCardComp" (HolMath.Sets.setupSetsCardComp SC SP SIn SIm SInd SFin
    SCard SCard2 SFun2 SFn SL SInf Nm arith2 arith3 arith9 Wf
    MESON_TAC ASM_MESON_TAC
    (HolMath.Lists.LIST_INDUCT_TAC list_INDUCT')
    ASM_ARITH_TAC ARITH_RULE
    listDefs.ALL listDefs.PAIRWISE listThms1.ALL_MEM
    listDefs.LENGTH new_definition).run
def SCC : HolMath.Sets.SetsCardComp := setsCardCompLayer

/-- `SetsSup` (sets.ml 4698-5027): the `sup`/`inf` definitions and their 49
    surrounding `prove`s.  Registers NO new infix. -/
initialize setsSupLayer : HolMath.Sets.SetsSup ←
  ioOk' "setupSetsSup" (HolMath.Sets.setupSetsSup SC SP
    MESON_TAC ASM_MESON_TAC REFUTE_THEN
    INTRO_TAC SELECT_CONV
    REAL_ARITH2 REAL_ARITH_TAC IMP_CONJ
    SIn.MEMBER_NOT_EMPTY SP.IN_IMAGE SFin.FINITE_INSERT
    SFin.FINITE_EMPTY SID.NOT_INSERT_EMPTY
    SP.NOT_IN_EMPTY SP.IN_INSERT SP.IN_SING SP.FORALL_IN_INSERT
    SP.FORALL_IN_UNION
    SC.FINITE_RULES SInd.FINITE_INDUCT_STRONG
    Rl.REAL_COMPLETE Rl.REAL_LE_TOTAL Rl.REAL_LE_TRANS
    Rl.REAL_LE_ANTISYM Rl.REAL_LE_REFL
    RaL.REAL_LTE_TRANS RaL.REAL_LET_TRANS realThms2.REAL_NOT_LE
    RaL.REAL_NOT_LT
    CiT.REAL_LE_NEG2 CiT.REAL_NEG_NEG Rl.real_max Rl.real_min
    realThms5.REAL_MAX_LE realThms5.REAL_LE_MAX
    realThms5.REAL_MIN_LE realThms5.REAL_LE_MIN
    realThms4.REAL_BOUNDS_LE realThms4.REAL_ABS_BOUNDS
    new_definition).run
def SSup : HolMath.Sets.SetsSup := setsSupLayer

/-- The EIGHTEENTH/NINETEENTH (and LAST) `parse_as_infix`: `has_inf`/`has_sup
    12 right` (sets.ml 5030-5031), forced just before `SISup`. -/
initialize setsHasInfSupInfixLayer : Unit ← HolMath.Sets.setupSetsHasInfSupInfix

/-- `SetsHasInfSup` (sets.ml 5028-5182): the relational `has_inf`/`has_sup`
    definitions and their 12 surrounding `prove`s.  `HYP_TAC`'s `rule` argument
    is a pure `thm -> Except String thm`; `REWRITE_RULE`/`MATCH_MP` are `IO`, so
    they are bridged through the safe `runExceptThm` opaque (Session used
    `unsafeIO` here, 9000-9007). -/
initialize setsHasInfSupLayer : HolMath.Sets.SetsHasInfSup ← do
  let _ := setsHasInfSupInfixLayer
  let rwPure : List thm → thm → Except String thm := fun thl th =>
    runExceptThm (REWRITE_RULE thl th)
  let mmPure : thm → thm → Except String thm := fun th1 th2 =>
    runExceptThm (MATCH_MP th1 th2)
  ioOk' "setupSetsHasInfSup" (HolMath.Sets.setupSetsHasInfSup SSup
    MESON_TAC ASM_MESON_TAC REFUTE_THEN INTRO_TAC HYP_TAC CLAIM_TAC
    rwPure mmPure REAL_ARITH_TAC ASM_REAL_ARITH_TAC
    SP.NOT_IN_EMPTY C.NOT_FORALL_THM Rl.REAL_LE_REFL
    Rl.REAL_LE_TRANS RaL.REAL_NOT_LT realThms2.REAL_NOT_LE
    new_definition).run
def SISup : HolMath.Sets.SetsHasInfSup := setsHasInfSupLayer

/- ---------------------------------------------------------------------- -/
/- SET_PRESET_CONV, SET_TAC, SET_RULE (sets.ml 320-335), with Session's    -/
/- dependency bundles pre-applied; plus new_inductive_set and the set-enum  -/
/- term helpers.                                                            -/
/- ---------------------------------------------------------------------- -/

/-- `SET_PRESET_CONV` (sets.ml 321-327), the local `PRESET_CONV` of SET_TAC. -/
def SET_PRESET_CONV : IO (Except String ioconv) :=
  pure (.ok (HolMath.Sets.SET_PRESET_CONV SC SP))

/-- `SET_TAC ths` (sets.ml 320-333): rewrite with the membership lemmas, then
    MESON. -/
def SET_TAC (ths : List thm) : tactic :=
  HolMath.Sets.SET_TAC SC SP MESON_TAC ths

/-- `SET_RULE tm = prove(tm, SET_TAC[])` (sets.ml 335). -/
def SET_RULE (tm : term) : IO (Except String thm) :=
  (HolMath.Sets.SET_RULE SC SP MESON_TAC tm).run

/-- new_inductive_set's `(/\)` (sets.ml 5209), parsed once at its file
    position. -/
initialize newIndSetAndTm : term ← pt "(/\\)"

/-- `new_inductive_set tm` (sets.ml 5183-5217): reduce an inductive SET
    definition to an inductive RELATION and return `(rules, induct, cases)`. -/
def new_inductive_set (tm : term) :
    IO (Except String (thm × thm × thm)) := do
  HolMath.Sets.new_inductive_set SC.IN newIndSetAndTm new_inductive_definition tm

/-- `dest_setenum` (sets.ml 3872). -/
def dest_setenum : term → Except String (List term) := HolMath.Sets.dest_setenum
/-- `is_setenum` (sets.ml 3878). -/
def is_setenum : term → Bool := HolMath.Sets.is_setenum
/-- `mk_setenum` (sets.ml 3880). -/
def mk_setenum : List term × hol_type → IO (Except String term) :=
  HolMath.Sets.mk_setenum SL.insert_atm SL.nil_atm
/-- `mk_fset` (sets.ml 3886). -/
def mk_fset : List term → IO (Except String term) :=
  HolMath.Sets.mk_fset SL.insert_atm SL.nil_atm

/-- `ensureSets` (Session 8666): all of sets.ml's load-bearing parser state and
    bundles are set up by the `initialize`s above, run in `ensureSets`'s exact
    file order.  Kept as a no-op accessor for callers that referenced the
    Session name. -/
def ensureSets : IO Unit := pure ()

/- ---------------------------------------------------------------------- -/
/- sets.ml bare theorem re-exports.  In HOL Light every theorem is a       -/
/- global name; the bundle records are a translation artefact, so each     -/
/- field is re-exported bare here as a plain `def`.                        -/
/- ---------------------------------------------------------------------- -/
-- SetsCore (sets.ml 34-170)
def IN                : thm := SC.IN
def EXTENSION         : thm := SC.EXTENSION
def GSPEC             : thm := SC.GSPEC
def SETSPEC           : thm := SC.SETSPEC
def IN_ELIM_THM       : thm := SC.IN_ELIM_THM
def EMPTY             : thm := SC.EMPTY
def INSERT_DEF        : thm := SC.INSERT_DEF
def UNIV              : thm := SC.UNIV
def UNION             : thm := SC.UNION
def UNIONS            : thm := SC.UNIONS
def INTER             : thm := SC.INTER
def INTERS            : thm := SC.INTERS
def DIFF              : thm := SC.DIFF
def INSERT            : thm := SC.INSERT
def DELETE            : thm := SC.DELETE
def SUBSET            : thm := SC.SUBSET
def PSUBSET           : thm := SC.PSUBSET
def DISJOINT          : thm := SC.DISJOINT
def SING              : thm := SC.SING
def FINITE_RULES      : thm := SC.FINITE_RULES
def FINITE_INDUCT     : thm := SC.FINITE_INDUCT
def FINITE_CASES      : thm := SC.FINITE_CASES
def INFINITE          : thm := SC.INFINITE
def IMAGE             : thm := SC.IMAGE
def INJ               : thm := SC.INJ
def SURJ              : thm := SC.SURJ
def BIJ               : thm := SC.BIJ
def CHOICE            : thm := SC.CHOICE
def REST              : thm := SC.REST
-- SetsProps (sets.ml 171-308)
def NOT_IN_EMPTY      : thm := SP.NOT_IN_EMPTY
def IN_UNIV           : thm := SP.IN_UNIV
def IN_UNION          : thm := SP.IN_UNION
def IN_UNIONS         : thm := SP.IN_UNIONS
def IN_INTER          : thm := SP.IN_INTER
def IN_INTERS         : thm := SP.IN_INTERS
def IN_DIFF           : thm := SP.IN_DIFF
def IN_INSERT         : thm := SP.IN_INSERT
def IN_DELETE         : thm := SP.IN_DELETE
def IN_SING           : thm := SP.IN_SING
def IN_IMAGE          : thm := SP.IN_IMAGE
def IN_REST           : thm := SP.IN_REST
def FORALL_IN_INSERT  : thm := SP.FORALL_IN_INSERT
def EXISTS_IN_INSERT  : thm := SP.EXISTS_IN_INSERT
def FORALL_IN_UNION   : thm := SP.FORALL_IN_UNION
def EXISTS_IN_UNION   : thm := SP.EXISTS_IN_UNION
def FORALL_IN_IMAGE   : thm := SP.FORALL_IN_IMAGE
def EXISTS_IN_IMAGE   : thm := SP.EXISTS_IN_IMAGE
def FORALL_IN_GSPEC   : thm := SP.FORALL_IN_GSPEC
def EXISTS_IN_GSPEC   : thm := SP.EXISTS_IN_GSPEC
def UNIONS_IMAGE      : thm := SP.UNIONS_IMAGE
def INTERS_IMAGE      : thm := SP.INTERS_IMAGE
def UNIONS_GSPEC      : thm := SP.UNIONS_GSPEC
def INTERS_GSPEC      : thm := SP.INTERS_GSPEC
-- SetsTactics (sets.ml 309-355)
def CHOICE_DEF        : thm := STc.CHOICE_DEF
def NOT_EQUAL_SETS    : thm := STc.NOT_EQUAL_SETS
def INSERT_RESTRICT   : thm := STc.INSERT_RESTRICT
def UNIV_1            : thm := STc.UNIV_1
-- SetsInclusion (sets.ml 356-475)
def MEMBER_NOT_EMPTY      : thm := SIn.MEMBER_NOT_EMPTY
def UNIV_NOT_EMPTY        : thm := SIn.UNIV_NOT_EMPTY
def EMPTY_NOT_UNIV        : thm := SIn.EMPTY_NOT_UNIV
def EQ_UNIV               : thm := SIn.EQ_UNIV
def SUBSET_TRANS          : thm := SIn.SUBSET_TRANS
def SUBSET_REFL           : thm := SIn.SUBSET_REFL
def SUBSET_ANTISYM        : thm := SIn.SUBSET_ANTISYM
def SUBSET_ANTISYM_EQ     : thm := SIn.SUBSET_ANTISYM_EQ
def EMPTY_SUBSET          : thm := SIn.EMPTY_SUBSET
def SUBSET_EMPTY          : thm := SIn.SUBSET_EMPTY
def SUBSET_UNIV           : thm := SIn.SUBSET_UNIV
def UNIV_SUBSET           : thm := SIn.UNIV_SUBSET
def SING_SUBSET           : thm := SIn.SING_SUBSET
def SUBSET_RESTRICT       : thm := SIn.SUBSET_RESTRICT
def PSUBSET_TRANS         : thm := SIn.PSUBSET_TRANS
def PSUBSET_SUBSET_TRANS  : thm := SIn.PSUBSET_SUBSET_TRANS
def SUBSET_PSUBSET_TRANS  : thm := SIn.SUBSET_PSUBSET_TRANS
def PSUBSET_IRREFL        : thm := SIn.PSUBSET_IRREFL
def NOT_PSUBSET_EMPTY     : thm := SIn.NOT_PSUBSET_EMPTY
def NOT_UNIV_PSUBSET      : thm := SIn.NOT_UNIV_PSUBSET
def PSUBSET_UNIV          : thm := SIn.PSUBSET_UNIV
def PSUBSET_ALT           : thm := SIn.PSUBSET_ALT
-- SetsOperators (sets.ml 476-855)
def UNION_ASSOC             : thm := SOp.UNION_ASSOC
def UNION_IDEMPOT           : thm := SOp.UNION_IDEMPOT
def UNION_COMM              : thm := SOp.UNION_COMM
def SUBSET_UNION            : thm := SOp.SUBSET_UNION
def SUBSET_UNION_ABSORPTION : thm := SOp.SUBSET_UNION_ABSORPTION
def UNION_EMPTY             : thm := SOp.UNION_EMPTY
def UNION_UNIV              : thm := SOp.UNION_UNIV
def EMPTY_UNION             : thm := SOp.EMPTY_UNION
def UNION_SUBSET            : thm := SOp.UNION_SUBSET
def UNION_RESTRICT          : thm := SOp.UNION_RESTRICT
def FORALL_SUBSET_UNION     : thm := SOp.FORALL_SUBSET_UNION
def EXISTS_SUBSET_UNION     : thm := SOp.EXISTS_SUBSET_UNION
def FORALL_SUBSET_INSERT    : thm := SOp.FORALL_SUBSET_INSERT
def EXISTS_SUBSET_INSERT    : thm := SOp.EXISTS_SUBSET_INSERT
def INTER_ASSOC             : thm := SOp.INTER_ASSOC
def INTER_IDEMPOT           : thm := SOp.INTER_IDEMPOT
def INTER_COMM              : thm := SOp.INTER_COMM
def INTER_SUBSET            : thm := SOp.INTER_SUBSET
def SUBSET_INTER_ABSORPTION : thm := SOp.SUBSET_INTER_ABSORPTION
def INTER_EMPTY             : thm := SOp.INTER_EMPTY
def INTER_UNIV              : thm := SOp.INTER_UNIV
def SUBSET_INTER            : thm := SOp.SUBSET_INTER
def INTER_RESTRICT          : thm := SOp.INTER_RESTRICT
def UNION_OVER_INTER        : thm := SOp.UNION_OVER_INTER
def INTER_OVER_UNION        : thm := SOp.INTER_OVER_UNION
def IN_DISJOINT             : thm := SOp.IN_DISJOINT
def DISJOINT_SYM            : thm := SOp.DISJOINT_SYM
def DISJOINT_EMPTY          : thm := SOp.DISJOINT_EMPTY
def DISJOINT_EMPTY_REFL     : thm := SOp.DISJOINT_EMPTY_REFL
def DISJOINT_UNION          : thm := SOp.DISJOINT_UNION
def DISJOINT_SING           : thm := SOp.DISJOINT_SING
def DIFF_EMPTY              : thm := SOp.DIFF_EMPTY
def EMPTY_DIFF              : thm := SOp.EMPTY_DIFF
def DIFF_UNIV               : thm := SOp.DIFF_UNIV
def DIFF_DIFF               : thm := SOp.DIFF_DIFF
def DIFF_EQ_EMPTY           : thm := SOp.DIFF_EQ_EMPTY
def SUBSET_DIFF             : thm := SOp.SUBSET_DIFF
def COMPL_COMPL             : thm := SOp.COMPL_COMPL
def DIFF_RESTRICT           : thm := SOp.DIFF_RESTRICT
-- SetsInsertDelete (sets.ml 856-950)
def COMPONENT             : thm := SID.COMPONENT
def DECOMPOSITION         : thm := SID.DECOMPOSITION
def SET_CASES             : thm := SID.SET_CASES
def ABSORPTION            : thm := SID.ABSORPTION
def INSERT_INSERT         : thm := SID.INSERT_INSERT
def INSERT_COMM           : thm := SID.INSERT_COMM
def INSERT_UNIV           : thm := SID.INSERT_UNIV
def NOT_INSERT_EMPTY      : thm := SID.NOT_INSERT_EMPTY
def NOT_EMPTY_INSERT      : thm := SID.NOT_EMPTY_INSERT
def INSERT_UNION          : thm := SID.INSERT_UNION
def INSERT_UNION_EQ       : thm := SID.INSERT_UNION_EQ
def INSERT_INTER          : thm := SID.INSERT_INTER
def DISJOINT_INSERT       : thm := SID.DISJOINT_INSERT
def INSERT_SUBSET         : thm := SID.INSERT_SUBSET
def SUBSET_INSERT         : thm := SID.SUBSET_INSERT
def INSERT_DIFF           : thm := SID.INSERT_DIFF
def INSERT_AC             : thm := SID.INSERT_AC
def INTER_ACI             : thm := SID.INTER_ACI
def UNION_ACI             : thm := SID.UNION_ACI
def DELETE_NON_ELEMENT    : thm := SID.DELETE_NON_ELEMENT
def IN_DELETE_EQ          : thm := SID.IN_DELETE_EQ
def EMPTY_DELETE          : thm := SID.EMPTY_DELETE
def DELETE_DELETE         : thm := SID.DELETE_DELETE
def DELETE_COMM           : thm := SID.DELETE_COMM
def DELETE_SUBSET         : thm := SID.DELETE_SUBSET
def SUBSET_DELETE         : thm := SID.SUBSET_DELETE
def SUBSET_INSERT_DELETE  : thm := SID.SUBSET_INSERT_DELETE
def DIFF_INSERT           : thm := SID.DIFF_INSERT
def PSUBSET_INSERT_SUBSET : thm := SID.PSUBSET_INSERT_SUBSET
def DELETE_INSERT         : thm := SID.DELETE_INSERT
def INSERT_DELETE         : thm := SID.INSERT_DELETE
def DELETE_INTER          : thm := SID.DELETE_INTER
def DISJOINT_DELETE_SYM   : thm := SID.DISJOINT_DELETE_SYM
-- SetsUnions
def UNIONS_0             : thm := SUn.UNIONS_0
def UNIONS_1             : thm := SUn.UNIONS_1
def UNIONS_2             : thm := SUn.UNIONS_2
def UNIONS_INSERT        : thm := SUn.UNIONS_INSERT
def FORALL_IN_UNIONS     : thm := SUn.FORALL_IN_UNIONS
def EXISTS_IN_UNIONS     : thm := SUn.EXISTS_IN_UNIONS
def EMPTY_UNIONS         : thm := SUn.EMPTY_UNIONS
def INTER_UNIONS         : thm := SUn.INTER_UNIONS
def UNIONS_SUBSET        : thm := SUn.UNIONS_SUBSET
def SUBSET_UNIONS        : thm := SUn.SUBSET_UNIONS
def UNIONS_UNION         : thm := SUn.UNIONS_UNION
def INTERS_UNION         : thm := SUn.INTERS_UNION
def UNIONS_MONO          : thm := SUn.UNIONS_MONO
def UNIONS_MONO_IMAGE    : thm := SUn.UNIONS_MONO_IMAGE
def UNIONS_UNIV          : thm := SUn.UNIONS_UNIV
def UNIONS_INSERT_EMPTY  : thm := SUn.UNIONS_INSERT_EMPTY
def UNIONS_DELETE_EMPTY  : thm := SUn.UNIONS_DELETE_EMPTY
-- SetsInters
def INTERS_0             : thm := SIt.INTERS_0
def INTERS_1             : thm := SIt.INTERS_1
def INTERS_2             : thm := SIt.INTERS_2
def INTERS_INSERT        : thm := SIt.INTERS_INSERT
def SUBSET_INTERS        : thm := SIt.SUBSET_INTERS
def INTERS_SUBSET        : thm := SIt.INTERS_SUBSET
def INTERS_SUBSET_STRONG : thm := SIt.INTERS_SUBSET_STRONG
def INTERS_ANTIMONO      : thm := SIt.INTERS_ANTIMONO
def INTERS_EQ_UNIV       : thm := SIt.INTERS_EQ_UNIV
def INTERS_ANTIMONO_GEN  : thm := SIt.INTERS_ANTIMONO_GEN
-- SetsImage (sets.ml 951-1150)
def IMAGE_CLAUSES        : thm := SIm.IMAGE_CLAUSES
def IMAGE_UNION          : thm := SIm.IMAGE_UNION
def IMAGE_ID             : thm := SIm.IMAGE_ID
def IMAGE_I              : thm := SIm.IMAGE_I
def IMAGE_o              : thm := SIm.IMAGE_o
def IMAGE_SUBSET         : thm := SIm.IMAGE_SUBSET
def IMAGE_INTER_INJ      : thm := SIm.IMAGE_INTER_INJ
def IMAGE_DIFF_INJ       : thm := SIm.IMAGE_DIFF_INJ
def IMAGE_DIFF_INJ_ALT   : thm := SIm.IMAGE_DIFF_INJ_ALT
def IMAGE_DELETE_INJ     : thm := SIm.IMAGE_DELETE_INJ
def IMAGE_DELETE_INJ_ALT : thm := SIm.IMAGE_DELETE_INJ_ALT
def IMAGE_EQ_EMPTY       : thm := SIm.IMAGE_EQ_EMPTY
def FORALL_IN_IMAGE_2    : thm := SIm.FORALL_IN_IMAGE_2
def IMAGE_CONST          : thm := SIm.IMAGE_CONST
def SIMPLE_IMAGE         : thm := SIm.SIMPLE_IMAGE
def SIMPLE_IMAGE_GEN     : thm := SIm.SIMPLE_IMAGE_GEN
def IMAGE_UNIONS         : thm := SIm.IMAGE_UNIONS
def FUN_IN_IMAGE         : thm := SIm.FUN_IN_IMAGE
def SURJECTIVE_IMAGE_EQ  : thm := SIm.SURJECTIVE_IMAGE_EQ
def IMAGE_EQ             : thm := SIm.IMAGE_EQ
-- SetsMisc (sets.ml GSPEC/saturated-image block)
def EMPTY_GSPEC                    : thm := SMi.EMPTY_GSPEC
def UNIV_GSPEC                     : thm := SMi.UNIV_GSPEC
def SING_GSPEC                     : thm := SMi.SING_GSPEC
def SING_ALT                       : thm := SMi.SING_ALT
def IN_GSPEC                       : thm := SMi.IN_GSPEC
def IN_ELIM_PAIR_THM               : thm := SMi.IN_ELIM_PAIR_THM
def IN_ELIM_TRIPLE_THM             : thm := SMi.IN_ELIM_TRIPLE_THM
def IN_ELIM_QUAD_THM               : thm := SMi.IN_ELIM_QUAD_THM
def SET_PAIR_THM                   : thm := SMi.SET_PAIR_THM
def SET_PROVE_CASES                : thm := SMi.SET_PROVE_CASES
def UNIONS_SINGS_GEN               : thm := SMi.UNIONS_SINGS_GEN
def UNIONS_SINGS                   : thm := SMi.UNIONS_SINGS
def IMAGE_INTERS                   : thm := SMi.IMAGE_INTERS
def DIFF_INTERS                    : thm := SMi.DIFF_INTERS
def INTERS_UNIONS                  : thm := SMi.INTERS_UNIONS
def UNIONS_INTERS                  : thm := SMi.UNIONS_INTERS
def UNIONS_DIFF                    : thm := SMi.UNIONS_DIFF
def DIFF_UNIONS                    : thm := SMi.DIFF_UNIONS
def DIFF_UNIONS_NONEMPTY           : thm := SMi.DIFF_UNIONS_NONEMPTY
def INTERS_OVER_UNIONS             : thm := SMi.INTERS_OVER_UNIONS
def INTER_INTERS                   : thm := SMi.INTER_INTERS
def UNIONS_OVER_INTERS             : thm := SMi.UNIONS_OVER_INTERS
def UNIONS_EQ_INTERS               : thm := SMi.UNIONS_EQ_INTERS
def EXISTS_UNIQUE_UNIONS_INTERS    : thm := SMi.EXISTS_UNIQUE_UNIONS_INTERS
def IMAGE_INTERS_SUBSET            : thm := SMi.IMAGE_INTERS_SUBSET
def IMAGE_INTER_SUBSET             : thm := SMi.IMAGE_INTER_SUBSET
def IMAGE_INTER_SATURATED_GEN      : thm := SMi.IMAGE_INTER_SATURATED_GEN
def IMAGE_INTERS_SATURATED_GEN     : thm := SMi.IMAGE_INTERS_SATURATED_GEN
def IMAGE_INTER_SATURATED          : thm := SMi.IMAGE_INTER_SATURATED
def IMAGE_INTERS_SATURATED         : thm := SMi.IMAGE_INTERS_SATURATED
-- SetsInduct
def FINITE_INDUCT_STRONG : thm := SInd.FINITE_INDUCT_STRONG
-- SetsFunctions (sets.ml 951-1382 function block)
def INJECTIVE_ON_ALT                 : thm := SFn.INJECTIVE_ON_ALT
def INJECTIVE_ALT                     : thm := SFn.INJECTIVE_ALT
def SURJECTIVE_ON_RIGHT_INVERSE       : thm := SFn.SURJECTIVE_ON_RIGHT_INVERSE
def INJECTIVE_ON_LEFT_INVERSE         : thm := SFn.INJECTIVE_ON_LEFT_INVERSE
def BIJECTIVE_ON_LEFT_RIGHT_INVERSE   : thm := SFn.BIJECTIVE_ON_LEFT_RIGHT_INVERSE
def SURJECTIVE_RIGHT_INVERSE          : thm := SFn.SURJECTIVE_RIGHT_INVERSE
def INJECTIVE_LEFT_INVERSE            : thm := SFn.INJECTIVE_LEFT_INVERSE
def BIJECTIVE_LEFT_RIGHT_INVERSE      : thm := SFn.BIJECTIVE_LEFT_RIGHT_INVERSE
def FUNCTION_FACTORS_LEFT_GEN         : thm := SFn.FUNCTION_FACTORS_LEFT_GEN
def FUNCTION_FACTORS_LEFT             : thm := SFn.FUNCTION_FACTORS_LEFT
def FUNCTION_FACTORS_RIGHT_GEN        : thm := SFn.FUNCTION_FACTORS_RIGHT_GEN
def FUNCTION_FACTORS_RIGHT            : thm := SFn.FUNCTION_FACTORS_RIGHT
def SURJECTIVE_FORALL_THM             : thm := SFn.SURJECTIVE_FORALL_THM
def SURJECTIVE_EXISTS_THM             : thm := SFn.SURJECTIVE_EXISTS_THM
def SURJECTIVE_IMAGE_THM              : thm := SFn.SURJECTIVE_IMAGE_THM
def IMAGE_INJECTIVE_IMAGE_OF_SUBSET   : thm := SFn.IMAGE_INJECTIVE_IMAGE_OF_SUBSET
-- SetsFinite (sets.ml 1383-1796)
def FINITE_EMPTY                    : thm := SFin.FINITE_EMPTY
def FINITE_SUBSET                   : thm := SFin.FINITE_SUBSET
def FINITE_RESTRICT                 : thm := SFin.FINITE_RESTRICT
def FINITE_UNION_IMP                : thm := SFin.FINITE_UNION_IMP
def FINITE_UNION                    : thm := SFin.FINITE_UNION
def FINITE_INTER                    : thm := SFin.FINITE_INTER
def FINITE_INSERT                   : thm := SFin.FINITE_INSERT
def FINITE_SING                     : thm := SFin.FINITE_SING
def FINITE_DELETE_IMP               : thm := SFin.FINITE_DELETE_IMP
def FINITE_DELETE                   : thm := SFin.FINITE_DELETE
def FINITE_FINITE_UNIONS            : thm := SFin.FINITE_FINITE_UNIONS
def FINITE_IMAGE_EXPAND             : thm := SFin.FINITE_IMAGE_EXPAND
def FINITE_IMAGE                    : thm := SFin.FINITE_IMAGE
def FINITE_IMAGE_INJ_GENERAL        : thm := SFin.FINITE_IMAGE_INJ_GENERAL
def FINITE_FINITE_PREIMAGE_GENERAL  : thm := SFin.FINITE_FINITE_PREIMAGE_GENERAL
def FINITE_FINITE_PREIMAGE          : thm := SFin.FINITE_FINITE_PREIMAGE
def FINITE_IMAGE_INJ_EQ             : thm := SFin.FINITE_IMAGE_INJ_EQ
def FINITE_IMAGE_INJ                : thm := SFin.FINITE_IMAGE_INJ
def FINITE_IMAGE_GEN                : thm := SFin.FINITE_IMAGE_GEN
def INFINITE_IMAGE                  : thm := SFin.INFINITE_IMAGE
def INFINITE_IMAGE_INJ              : thm := SFin.INFINITE_IMAGE_INJ
def INFINITE_NONEMPTY               : thm := SFin.INFINITE_NONEMPTY
def INFINITE_DIFF_FINITE            : thm := SFin.INFINITE_DIFF_FINITE
def SUBSET_IMAGE_INJ                : thm := SFin.SUBSET_IMAGE_INJ
def SUBSET_IMAGE                    : thm := SFin.SUBSET_IMAGE
def EXISTS_SUBSET_IMAGE             : thm := SFin.EXISTS_SUBSET_IMAGE
def FORALL_SUBSET_IMAGE             : thm := SFin.FORALL_SUBSET_IMAGE
def EXISTS_SUBSET_IMAGE_INJ         : thm := SFin.EXISTS_SUBSET_IMAGE_INJ
def FORALL_SUBSET_IMAGE_INJ         : thm := SFin.FORALL_SUBSET_IMAGE_INJ
def EXISTS_FINITE_SUBSET_IMAGE_INJ  : thm := SFin.EXISTS_FINITE_SUBSET_IMAGE_INJ
def FORALL_FINITE_SUBSET_IMAGE_INJ  : thm := SFin.FORALL_FINITE_SUBSET_IMAGE_INJ
def EXISTS_FINITE_SUBSET_IMAGE      : thm := SFin.EXISTS_FINITE_SUBSET_IMAGE
def FORALL_FINITE_SUBSET_IMAGE      : thm := SFin.FORALL_FINITE_SUBSET_IMAGE
def FINITE_SUBSET_IMAGE             : thm := SFin.FINITE_SUBSET_IMAGE
def FINITE_SUBSET_IMAGE_IMP         : thm := SFin.FINITE_SUBSET_IMAGE_IMP
def FINITE_IMAGE_EQ                 : thm := SFin.FINITE_IMAGE_EQ
def FINITE_IMAGE_EQ_INJ             : thm := SFin.FINITE_IMAGE_EQ_INJ
def FINITE_DIFF                     : thm := SFin.FINITE_DIFF
def INFINITE_SUPERSET               : thm := SFin.INFINITE_SUPERSET
def FINITE_TRANSITIVITY_CHAIN       : thm := SFin.FINITE_TRANSITIVITY_CHAIN
def UNIONS_MAXIMAL_SETS             : thm := SFin.UNIONS_MAXIMAL_SETS
def FINITE_SUBSET_UNIONS            : thm := SFin.FINITE_SUBSET_UNIONS
def UNIONS_IN_CHAIN                 : thm := SFin.UNIONS_IN_CHAIN
def INTERS_IN_CHAIN                 : thm := SFin.INTERS_IN_CHAIN
def FINITE_SUBSET_UNIONS_DIRECTED_EQ : thm := SFin.FINITE_SUBSET_UNIONS_DIRECTED_EQ
def FINITE_SUBSET_UNIONS_CHAIN_EQ   : thm := SFin.FINITE_SUBSET_UNIONS_CHAIN_EQ
def FINITE_SUBSET_UNIONS_CHAIN      : thm := SFin.FINITE_SUBSET_UNIONS_CHAIN
-- SetsRecursion (sets.ml 1799-1988)
def FINREC                   : thm := SRec.FINREC
def FINREC_1_LEMMA           : thm := SRec.FINREC_1_LEMMA
def FINREC_SUC_LEMMA         : thm := SRec.FINREC_SUC_LEMMA
def FINREC_UNIQUE_LEMMA      : thm := SRec.FINREC_UNIQUE_LEMMA
def FINREC_EXISTS_LEMMA      : thm := SRec.FINREC_EXISTS_LEMMA
def FINREC_FUN_LEMMA         : thm := SRec.FINREC_FUN_LEMMA
def FINREC_FUN               : thm := SRec.FINREC_FUN
def SET_RECURSION_LEMMA      : thm := SRec.SET_RECURSION_LEMMA
def ITSET                    : thm := SRec.ITSET
def FINITE_RECURSION         : thm := SRec.FINITE_RECURSION
def FINITE_RECURSION_DELETE  : thm := SRec.FINITE_RECURSION_DELETE
def ITSET_EQ                 : thm := SRec.ITSET_EQ
-- SetsCard (sets.ml 1991-2243)
def CARD                     : thm := SCard.CARD
def CARD_CLAUSES             : thm := SCard.CARD_CLAUSES
def CARD_UNION               : thm := SCard.CARD_UNION
def CARD_DELETE              : thm := SCard.CARD_DELETE
def CARD_UNION_EQ            : thm := SCard.CARD_UNION_EQ
def CARD_DIFF                : thm := SCard.CARD_DIFF
def CARD_EQ_0                : thm := SCard.CARD_EQ_0
def CARD_SING                : thm := SCard.CARD_SING
def CARD_LE_2                : thm := SCard.CARD_LE_2
def CARD_LE_3                : thm := SCard.CARD_LE_3
def CARD_LE_4                : thm := SCard.CARD_LE_4
def FINITE_INDUCT_DELETE     : thm := SCard.FINITE_INDUCT_DELETE
def HAS_SIZE                  : thm := SCard.HAS_SIZE
def HAS_SIZE_CARD            : thm := SCard.HAS_SIZE_CARD
def HAS_SIZE_0               : thm := SCard.HAS_SIZE_0
def HAS_SIZE_SUC             : thm := SCard.HAS_SIZE_SUC
def HAS_SIZE_UNION           : thm := SCard.HAS_SIZE_UNION
def HAS_SIZE_DIFF            : thm := SCard.HAS_SIZE_DIFF
def HAS_SIZE_UNIONS          : thm := SCard.HAS_SIZE_UNIONS
def FINITE_HAS_SIZE          : thm := SCard.FINITE_HAS_SIZE
def HAS_SIZE_CLAUSES         : thm := SCard.HAS_SIZE_CLAUSES
def HAS_SIZE_CONV            : ioconv := SCard.HAS_SIZE_CONV
-- SetsCard2 (sets.ml 2244-2652)
def CARD_SUBSET_EQ           : thm := SCard2.CARD_SUBSET_EQ
def CARD_SUBSET              : thm := SCard2.CARD_SUBSET
def CARD_SUBSET_LE           : thm := SCard2.CARD_SUBSET_LE
def SUBSET_CARD_EQ           : thm := SCard2.SUBSET_CARD_EQ
def FINITE_CARD_LE_SUBSET    : thm := SCard2.FINITE_CARD_LE_SUBSET
def CARD_PSUBSET             : thm := SCard2.CARD_PSUBSET
def CARD_PSUBSET_IMP         : thm := SCard2.CARD_PSUBSET_IMP
def CARD_PSUBSET_EQ          : thm := SCard2.CARD_PSUBSET_EQ
def CARD_UNION_LE            : thm := SCard2.CARD_UNION_LE
def FINITE_CARD_LE_UNION     : thm := SCard2.FINITE_CARD_LE_UNION
def CARD_UNIONS_LE           : thm := SCard2.CARD_UNIONS_LE
def CARD_UNION_GEN           : thm := SCard2.CARD_UNION_GEN
def CARD_UNION_OVERLAP_EQ    : thm := SCard2.CARD_UNION_OVERLAP_EQ
def CARD_UNION_OVERLAP       : thm := SCard2.CARD_UNION_OVERLAP
def CARD_IMAGE_INJ           : thm := SCard2.CARD_IMAGE_INJ
def HAS_SIZE_IMAGE_INJ       : thm := SCard2.HAS_SIZE_IMAGE_INJ
def CARD_IMAGE_LE            : thm := SCard2.CARD_IMAGE_LE
def FINITE_CARD_LE_IMAGE     : thm := SCard2.FINITE_CARD_LE_IMAGE
def CARD_IMAGE_INJ_EQ        : thm := SCard2.CARD_IMAGE_INJ_EQ
def CARD_SUBSET_IMAGE        : thm := SCard2.CARD_SUBSET_IMAGE
def HAS_SIZE_IMAGE_INJ_EQ    : thm := SCard2.HAS_SIZE_IMAGE_INJ_EQ
def CARD_IMAGE_EQ_INJ        : thm := SCard2.CARD_IMAGE_EQ_INJ
def EXISTS_SMALL_SUBSET_IMAGE_INJ : thm :=
  SCard2.EXISTS_SMALL_SUBSET_IMAGE_INJ
def FORALL_SMALL_SUBSET_IMAGE_INJ : thm :=
  SCard2.FORALL_SMALL_SUBSET_IMAGE_INJ
def EXISTS_SMALL_SUBSET_IMAGE : thm := SCard2.EXISTS_SMALL_SUBSET_IMAGE
def FORALL_SMALL_SUBSET_IMAGE : thm := SCard2.FORALL_SMALL_SUBSET_IMAGE
def CARD_IMAGE_LE2           : thm := SCard2.CARD_IMAGE_LE2
def CARD_IMAGE_LT2           : thm := SCard2.CARD_IMAGE_LT2
def CHOOSE_SUBSET_STRONG     : thm := SCard2.CHOOSE_SUBSET_STRONG
def CHOOSE_SUBSET_EQ         : thm := SCard2.CHOOSE_SUBSET_EQ
def CHOOSE_SUBSET            : thm := SCard2.CHOOSE_SUBSET
def CHOOSE_SUBSET_BETWEEN    : thm := SCard2.CHOOSE_SUBSET_BETWEEN
def CARD_LE_UNIONS_CHAIN     : thm := SCard2.CARD_LE_UNIONS_CHAIN
def CARD_LE_1                : thm := SCard2.CARD_LE_1
def INVOLUTION_EVEN_NOFIXPOINTS : thm :=
  SCard2.INVOLUTION_EVEN_NOFIXPOINTS
def INVOLUTION_EVEN_FIXPOINTS : thm := SCard2.INVOLUTION_EVEN_FIXPOINTS
-- SetsCross (sets.ml 2653-2924): product cardinality and the CROSS operator.
def HAS_SIZE_PRODUCT_DEPENDENT : thm := SCross.HAS_SIZE_PRODUCT_DEPENDENT
def FINITE_PRODUCT_DEPENDENT : thm := SCross.FINITE_PRODUCT_DEPENDENT
def FINITE_PRODUCT           : thm := SCross.FINITE_PRODUCT
def CARD_PRODUCT             : thm := SCross.CARD_PRODUCT
def HAS_SIZE_PRODUCT         : thm := SCross.HAS_SIZE_PRODUCT
def CROSS                    : thm := SCross.CROSS
def IN_CROSS                 : thm := SCross.IN_CROSS
def HAS_SIZE_CROSS           : thm := SCross.HAS_SIZE_CROSS
def FINITE_CROSS             : thm := SCross.FINITE_CROSS
def CARD_CROSS               : thm := SCross.CARD_CROSS
def CROSS_EQ_EMPTY           : thm := SCross.CROSS_EQ_EMPTY
def CROSS_EMPTY              : thm := SCross.CROSS_EMPTY
def CROSS_SING               : thm := SCross.CROSS_SING
def CROSS_UNIV               : thm := SCross.CROSS_UNIV
def FINITE_CROSS_EQ          : thm := SCross.FINITE_CROSS_EQ
def INFINITE_CROSS_EQ        : thm := SCross.INFINITE_CROSS_EQ
def FINITE_CROSS_UNIV        : thm := SCross.FINITE_CROSS_UNIV
def INFINITE_CROSS_UNIV      : thm := SCross.INFINITE_CROSS_UNIV
def FINITE_UNIV_PAIR         : thm := SCross.FINITE_UNIV_PAIR
def INFINITE_UNIV_PAIR       : thm := SCross.INFINITE_UNIV_PAIR
def FORALL_IN_CROSS          : thm := SCross.FORALL_IN_CROSS
def EXISTS_IN_CROSS          : thm := SCross.EXISTS_IN_CROSS
def SUBSET_CROSS             : thm := SCross.SUBSET_CROSS
def CROSS_MONO               : thm := SCross.CROSS_MONO
def CROSS_EQ                 : thm := SCross.CROSS_EQ
def IMAGE_FST_CROSS          : thm := SCross.IMAGE_FST_CROSS
def IMAGE_SND_CROSS          : thm := SCross.IMAGE_SND_CROSS
def IMAGE_PAIRED_CROSS       : thm := SCross.IMAGE_PAIRED_CROSS
def CROSS_INTER              : thm := SCross.CROSS_INTER
def CROSS_UNION              : thm := SCross.CROSS_UNION
def CROSS_DIFF               : thm := SCross.CROSS_DIFF
def INTER_CROSS              : thm := SCross.INTER_CROSS
def CROSS_UNIONS_UNIONS      : thm := SCross.CROSS_UNIONS_UNIONS
def CROSS_UNIONS             : thm := SCross.CROSS_UNIONS
def CROSS_INTERS_INTERS      : thm := SCross.CROSS_INTERS_INTERS
def CROSS_INTERS             : thm := SCross.CROSS_INTERS
def DISJOINT_CROSS           : thm := SCross.DISJOINT_CROSS
-- SetsFunspace (sets.ml 2925-3324)
def ARB                                : thm := SFun.ARB
def EXTENSIONAL                        : thm := SFun.EXTENSIONAL
def IN_EXTENSIONAL                     : thm := SFun.IN_EXTENSIONAL
def IN_EXTENSIONAL_UNDEFINED           : thm := SFun.IN_EXTENSIONAL_UNDEFINED
def EXTENSIONAL_EMPTY                  : thm := SFun.EXTENSIONAL_EMPTY
def EXTENSIONAL_UNIV                   : thm := SFun.EXTENSIONAL_UNIV
def EXTENSIONAL_EQ                     : thm := SFun.EXTENSIONAL_EQ
def RESTRICTION                        : thm := SFun.RESTRICTION
def RESTRICTION_THM                    : thm := SFun.RESTRICTION_THM
def RESTRICTION_DEFINED                : thm := SFun.RESTRICTION_DEFINED
def RESTRICTION_UNDEFINED              : thm := SFun.RESTRICTION_UNDEFINED
def RESTRICTION_EQ                     : thm := SFun.RESTRICTION_EQ
def RESTRICTION_IN_EXTENSIONAL         : thm := SFun.RESTRICTION_IN_EXTENSIONAL
def RESTRICTION_EXTENSION              : thm := SFun.RESTRICTION_EXTENSION
def RESTRICTION_FIXPOINT               : thm := SFun.RESTRICTION_FIXPOINT
def RESTRICTION_UNIV                   : thm := SFun.RESTRICTION_UNIV
def RESTRICTION_RESTRICTION            : thm := SFun.RESTRICTION_RESTRICTION
def RESTRICTION_IDEMP                  : thm := SFun.RESTRICTION_IDEMP
def IMAGE_RESTRICTION                  : thm := SFun.IMAGE_RESTRICTION
def RESTRICTION_COMPOSE_RIGHT          : thm := SFun.RESTRICTION_COMPOSE_RIGHT
def RESTRICTION_COMPOSE_LEFT           : thm := SFun.RESTRICTION_COMPOSE_LEFT
def RESTRICTION_COMPOSE                : thm := SFun.RESTRICTION_COMPOSE
def RESTRICTION_UNIQUE                 : thm := SFun.RESTRICTION_UNIQUE
def RESTRICTION_UNIQUE_ALT             : thm := SFun.RESTRICTION_UNIQUE_ALT
def cartesian_product                  : thm := SFun.cartesian_product
def IN_CARTESIAN_PRODUCT               : thm := SFun.IN_CARTESIAN_PRODUCT
def CARTESIAN_PRODUCT                   : thm := SFun.CARTESIAN_PRODUCT
def RESTRICTION_IN_CARTESIAN_PRODUCT   : thm := SFun.RESTRICTION_IN_CARTESIAN_PRODUCT
def CARTESIAN_PRODUCT_AS_RESTRICTIONS  : thm := SFun.CARTESIAN_PRODUCT_AS_RESTRICTIONS
def CARTESIAN_PRODUCT_EQ_EMPTY         : thm := SFun.CARTESIAN_PRODUCT_EQ_EMPTY
def CARTESIAN_PRODUCT_EMPTY            : thm := SFun.CARTESIAN_PRODUCT_EMPTY
def CARTESIAN_PRODUCT_EQ_MEMBERS       : thm := SFun.CARTESIAN_PRODUCT_EQ_MEMBERS
def CARTESIAN_PRODUCT_EQ_MEMBERS_EQ    : thm := SFun.CARTESIAN_PRODUCT_EQ_MEMBERS_EQ
def SUBSET_CARTESIAN_PRODUCT           : thm := SFun.SUBSET_CARTESIAN_PRODUCT
def CARTESIAN_PRODUCT_EQ               : thm := SFun.CARTESIAN_PRODUCT_EQ
def INTER_CARTESIAN_PRODUCT            : thm := SFun.INTER_CARTESIAN_PRODUCT
def CARTESIAN_PRODUCT_UNIV             : thm := SFun.CARTESIAN_PRODUCT_UNIV
def CARTESIAN_PRODUCT_SINGS            : thm := SFun.CARTESIAN_PRODUCT_SINGS
def CARTESIAN_PRODUCT_SINGS_GEN        : thm := SFun.CARTESIAN_PRODUCT_SINGS_GEN
def IMAGE_PROJECTION_CARTESIAN_PRODUCT : thm := SFun.IMAGE_PROJECTION_CARTESIAN_PRODUCT
def FORALL_CARTESIAN_PRODUCT_ELEMENTS  : thm := SFun.FORALL_CARTESIAN_PRODUCT_ELEMENTS
def FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ : thm := SFun.FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ
def EXISTS_CARTESIAN_PRODUCT_ELEMENT   : thm := SFun.EXISTS_CARTESIAN_PRODUCT_ELEMENT
def product_map                        : thm := SFun.product_map
def PRODUCT_MAP_RESTRICTION            : thm := SFun.PRODUCT_MAP_RESTRICTION
def IMAGE_PRODUCT_MAP                  : thm := SFun.IMAGE_PRODUCT_MAP
def disjoint_union                     : thm := SFun.disjoint_union
def SUBSET_DISJOINT_UNION              : thm := SFun.SUBSET_DISJOINT_UNION
def DISJOINT_UNION_EQ                  : thm := SFun.DISJOINT_UNION_EQ
def SUBSET_DISJOINT_UNION_EXISTS       : thm := SFun.SUBSET_DISJOINT_UNION_EXISTS
def INTER_DISJOINT_UNION               : thm := SFun.INTER_DISJOINT_UNION
def UNION_DISJOINT_UNION               : thm := SFun.UNION_DISJOINT_UNION
def DISJOINT_UNION_EQ_EMPTY            : thm := SFun.DISJOINT_UNION_EQ_EMPTY
def DISJOINT_DISJOINT_UNION            : thm := SFun.DISJOINT_DISJOINT_UNION
-- SetsFunspace2 (sets.ml 3325-3548)
def HAS_SIZE_FUNSPACE          : thm := SFun2.HAS_SIZE_FUNSPACE
def CARD_FUNSPACE              : thm := SFun2.CARD_FUNSPACE
def FINITE_FUNSPACE            : thm := SFun2.FINITE_FUNSPACE
def HAS_SIZE_FUNSPACE_UNIV     : thm := SFun2.HAS_SIZE_FUNSPACE_UNIV
def CARD_FUNSPACE_UNIV         : thm := SFun2.CARD_FUNSPACE_UNIV
def FINITE_FUNSPACE_UNIV       : thm := SFun2.FINITE_FUNSPACE_UNIV
def HAS_SIZE_BOOL              : thm := SFun2.HAS_SIZE_BOOL
def CARD_BOOL                  : thm := SFun2.CARD_BOOL
def FINITE_BOOL                : thm := SFun2.FINITE_BOOL
def HAS_SIZE_POWERSET          : thm := SFun2.HAS_SIZE_POWERSET
def CARD_POWERSET              : thm := SFun2.CARD_POWERSET
def FINITE_POWERSET            : thm := SFun2.FINITE_POWERSET
def FINITE_POWERSET_EQ         : thm := SFun2.FINITE_POWERSET_EQ
def FINITE_RESTRICTED_SUBSETS  : thm := SFun2.FINITE_RESTRICTED_SUBSETS
def FINITE_UNIONS              : thm := SFun2.FINITE_UNIONS
def FINITE_CARD_LE_UNIONS      : thm := SFun2.FINITE_CARD_LE_UNIONS
def POWERSET_CLAUSES           : thm := SFun2.POWERSET_CLAUSES
def FINITE_IMAGE_INFINITE      : thm := SFun2.FINITE_IMAGE_INFINITE
def FINITE_RESTRICTED_POWERSET : thm := SFun2.FINITE_RESTRICTED_POWERSET
def FINITE_RESTRICTED_FUNSPACE : thm := SFun2.FINITE_RESTRICTED_FUNSPACE
def NUMSEG_CLAUSES_LT          : thm := SInf.NUMSEG_CLAUSES_LT
def HAS_SIZE_NUMSEG_LT         : thm := SInf.HAS_SIZE_NUMSEG_LT
def CARD_NUMSEG_LT             : thm := SInf.CARD_NUMSEG_LT
def FINITE_NUMSEG_LT           : thm := SInf.FINITE_NUMSEG_LT
def NUMSEG_CLAUSES_LE          : thm := SInf.NUMSEG_CLAUSES_LE
def HAS_SIZE_NUMSEG_LE         : thm := SInf.HAS_SIZE_NUMSEG_LE
def FINITE_NUMSEG_LE           : thm := SInf.FINITE_NUMSEG_LE
def CARD_NUMSEG_LE             : thm := SInf.CARD_NUMSEG_LE
def num_FINITE                 : thm := SInf.num_FINITE
def num_FINITE_AVOID           : thm := SInf.num_FINITE_AVOID
def num_INFINITE_EQ            : thm := SInf.num_INFINITE_EQ
def num_INFINITE               : thm := SInf.num_INFINITE
def string_INFINITE            : thm := SInf.string_INFINITE
def FINITE_REAL_INTERVAL       : thm := SInf.FINITE_REAL_INTERVAL
def real_INFINITE              : thm := SInf.real_INFINITE
-- SetsList (sets.ml 3697-3997)
def HAS_SIZE_INDEX             : thm := SL.HAS_SIZE_INDEX
def INFINITE_ENUMERATE         : thm := SL.INFINITE_ENUMERATE
def INFINITE_ENUMERATE_EQ      : thm := SL.INFINITE_ENUMERATE_EQ
def INFINITE_ENUMERATE_SUBSET  : thm := SL.INFINITE_ENUMERATE_SUBSET
def set_of_list                : thm := SL.set_of_list
def list_of_set                : thm := SL.list_of_set
def LIST_OF_SET_PROPERTIES     : thm := SL.LIST_OF_SET_PROPERTIES
def SET_OF_LIST_OF_SET         : thm := SL.SET_OF_LIST_OF_SET
def LENGTH_LIST_OF_SET         : thm := SL.LENGTH_LIST_OF_SET
def MEM_LIST_OF_SET            : thm := SL.MEM_LIST_OF_SET
def FINITE_SET_OF_LIST         : thm := SL.FINITE_SET_OF_LIST
def IN_SET_OF_LIST             : thm := SL.IN_SET_OF_LIST
def SET_OF_LIST_APPEND         : thm := SL.SET_OF_LIST_APPEND
def SET_OF_LIST_MAP            : thm := SL.SET_OF_LIST_MAP
def SET_OF_LIST_EQ_EMPTY       : thm := SL.SET_OF_LIST_EQ_EMPTY
def LIST_OF_SET_EMPTY          : thm := SL.LIST_OF_SET_EMPTY
def LIST_OF_SET_SING           : thm := SL.LIST_OF_SET_SING
def pairwise                   : thm := SL.pairwise
def PAIRWISE_EMPTY             : thm := SL.PAIRWISE_EMPTY
def PAIRWISE_SING              : thm := SL.PAIRWISE_SING
def PAIRWISE_IMP               : thm := SL.PAIRWISE_IMP
def PAIRWISE_MONO              : thm := SL.PAIRWISE_MONO
def PAIRWISE_AND               : thm := SL.PAIRWISE_AND
def PAIRWISE_INSERT            : thm := SL.PAIRWISE_INSERT
def PAIRWISE_INSERT_SYMMETRIC  : thm := SL.PAIRWISE_INSERT_SYMMETRIC
def PAIRWISE_IMAGE             : thm := SL.PAIRWISE_IMAGE
def PAIRWISE_UNION             : thm := SL.PAIRWISE_UNION
def PAIRWISE_CHAIN_UNIONS      : thm := SL.PAIRWISE_CHAIN_UNIONS
def DIFF_UNIONS_PAIRWISE_DISJOINT : thm := SL.DIFF_UNIONS_PAIRWISE_DISJOINT
def INTER_UNIONS_PAIRWISE_DISJOINT : thm := SL.INTER_UNIONS_PAIRWISE_DISJOINT
def PSUBSET_UNIONS_PAIRWISE_DISJOINT : thm := SL.PSUBSET_UNIONS_PAIRWISE_DISJOINT
-- SetsUnionOf (sets.ml 3998-4364)
def UNION_OF                        : thm := SUO.UNION_OF
def INTERSECTION_OF                 : thm := SUO.INTERSECTION_OF
def UNION_OF_INC                    : thm := SUO.UNION_OF_INC
def INTERSECTION_OF_INC             : thm := SUO.INTERSECTION_OF_INC
def UNION_OF_MONO                   : thm := SUO.UNION_OF_MONO
def INTERSECTION_OF_MONO            : thm := SUO.INTERSECTION_OF_MONO
def FORALL_UNION_OF                 : thm := SUO.FORALL_UNION_OF
def FORALL_INTERSECTION_OF          : thm := SUO.FORALL_INTERSECTION_OF
def UNION_OF_EMPTY                  : thm := SUO.UNION_OF_EMPTY
def INTERSECTION_OF_EMPTY           : thm := SUO.INTERSECTION_OF_EMPTY
def ARBITRARY                       : thm := SUO.ARBITRARY
def ARBITRARY_UNION_OF_ALT          : thm := SUO.ARBITRARY_UNION_OF_ALT
def ARBITRARY_UNION_OF_EMPTY        : thm := SUO.ARBITRARY_UNION_OF_EMPTY
def ARBITRARY_INTERSECTION_OF_EMPTY : thm := SUO.ARBITRARY_INTERSECTION_OF_EMPTY
def ARBITRARY_UNION_OF_INC          : thm := SUO.ARBITRARY_UNION_OF_INC
def ARBITRARY_INTERSECTION_OF_INC   : thm := SUO.ARBITRARY_INTERSECTION_OF_INC
def ARBITRARY_UNION_OF_COMPLEMENT   : thm := SUO.ARBITRARY_UNION_OF_COMPLEMENT
def ARBITRARY_INTERSECTION_OF_COMPLEMENT : thm := SUO.ARBITRARY_INTERSECTION_OF_COMPLEMENT
def ARBITRARY_UNION_OF_IDEMPOT      : thm := SUO.ARBITRARY_UNION_OF_IDEMPOT
def ARBITRARY_INTERSECTION_OF_IDEMPOT : thm := SUO.ARBITRARY_INTERSECTION_OF_IDEMPOT
def ARBITRARY_UNION_OF_UNIONS       : thm := SUO.ARBITRARY_UNION_OF_UNIONS
def ARBITRARY_UNION_OF_UNION        : thm := SUO.ARBITRARY_UNION_OF_UNION
def ARBITRARY_INTERSECTION_OF_INTERS : thm := SUO.ARBITRARY_INTERSECTION_OF_INTERS
def ARBITRARY_INTERSECTION_OF_INTER : thm := SUO.ARBITRARY_INTERSECTION_OF_INTER
def ARBITRARY_UNION_OF_INTER_EQ     : thm := SUO.ARBITRARY_UNION_OF_INTER_EQ
def ARBITRARY_UNION_OF_INTER        : thm := SUO.ARBITRARY_UNION_OF_INTER
def ARBITRARY_INTERSECTION_OF_UNION_EQ : thm := SUO.ARBITRARY_INTERSECTION_OF_UNION_EQ
def ARBITRARY_INTERSECTION_OF_UNION : thm := SUO.ARBITRARY_INTERSECTION_OF_UNION
def FINITE_UNION_OF_EMPTY           : thm := SUO.FINITE_UNION_OF_EMPTY
def FINITE_INTERSECTION_OF_EMPTY    : thm := SUO.FINITE_INTERSECTION_OF_EMPTY
def FINITE_UNION_OF_INC             : thm := SUO.FINITE_UNION_OF_INC
def FINITE_INTERSECTION_OF_INC      : thm := SUO.FINITE_INTERSECTION_OF_INC
def FINITE_UNION_OF_COMPLEMENT      : thm := SUO.FINITE_UNION_OF_COMPLEMENT
def FINITE_INTERSECTION_OF_COMPLEMENT : thm := SUO.FINITE_INTERSECTION_OF_COMPLEMENT
def FINITE_UNION_OF_IDEMPOT         : thm := SUO.FINITE_UNION_OF_IDEMPOT
def FINITE_INTERSECTION_OF_IDEMPOT  : thm := SUO.FINITE_INTERSECTION_OF_IDEMPOT
def FINITE_UNION_OF_UNIONS          : thm := SUO.FINITE_UNION_OF_UNIONS
def FINITE_UNION_OF_UNION           : thm := SUO.FINITE_UNION_OF_UNION
def FINITE_INTERSECTION_OF_INTERS   : thm := SUO.FINITE_INTERSECTION_OF_INTERS
def FINITE_INTERSECTION_OF_INTER    : thm := SUO.FINITE_INTERSECTION_OF_INTER
def FINITE_UNION_OF_INTER_EQ        : thm := SUO.FINITE_UNION_OF_INTER_EQ
def FINITE_UNION_OF_INTER           : thm := SUO.FINITE_UNION_OF_INTER
def FINITE_INTERSECTION_OF_UNION_EQ : thm := SUO.FINITE_INTERSECTION_OF_UNION_EQ
def FINITE_INTERSECTION_OF_UNION    : thm := SUO.FINITE_INTERSECTION_OF_UNION
-- SetsCardComp (sets.ml 4365-4695)
def CARD_SET_OF_LIST_LE          : thm := SCC.CARD_SET_OF_LIST_LE
def HAS_SIZE_SET_OF_LIST         : thm := SCC.HAS_SIZE_SET_OF_LIST
def SURJECTIVE_IFF_INJECTIVE_GEN : thm := SCC.SURJECTIVE_IFF_INJECTIVE_GEN
def SURJECTIVE_IFF_INJECTIVE     : thm := SCC.SURJECTIVE_IFF_INJECTIVE
def IMAGE_IMP_INJECTIVE_GEN      : thm := SCC.IMAGE_IMP_INJECTIVE_GEN
def IMAGE_IMP_INJECTIVE          : thm := SCC.IMAGE_IMP_INJECTIVE
def HAS_SIZE_IMAGE_INJ_RESTRICT  : thm := SCC.HAS_SIZE_IMAGE_INJ_RESTRICT
def CARD_LE_INJ                  : thm := SCC.CARD_LE_INJ
def FORALL_IN_CLAUSES            : thm := SCC.FORALL_IN_CLAUSES
def EXISTS_IN_CLAUSES            : thm := SCC.EXISTS_IN_CLAUSES
def INJECTIVE_ON_IMAGE           : thm := SCC.INJECTIVE_ON_IMAGE
def INJECTIVE_IMAGE              : thm := SCC.INJECTIVE_IMAGE
def SURJECTIVE_ON_IMAGE          : thm := SCC.SURJECTIVE_ON_IMAGE
def SURJECTIVE_IMAGE             : thm := SCC.SURJECTIVE_IMAGE
def INJECTIVE_ON_PREIMAGE        : thm := SCC.INJECTIVE_ON_PREIMAGE
def SURJECTIVE_ON_PREIMAGE       : thm := SCC.SURJECTIVE_ON_PREIMAGE
def INJECTIVE_PREIMAGE           : thm := SCC.INJECTIVE_PREIMAGE
def SURJECTIVE_PREIMAGE          : thm := SCC.SURJECTIVE_PREIMAGE
def CARD_EQ_BIJECTION            : thm := SCC.CARD_EQ_BIJECTION
def CARD_EQ_BIJECTIONS           : thm := SCC.CARD_EQ_BIJECTIONS
def CARD_EQ_BIJECTIONS_SPECIAL   : thm := SCC.CARD_EQ_BIJECTIONS_SPECIAL
def BIJECTIONS_HAS_SIZE          : thm := SCC.BIJECTIONS_HAS_SIZE
def BIJECTIONS_HAS_SIZE_EQ       : thm := SCC.BIJECTIONS_HAS_SIZE_EQ
def BIJECTIONS_CARD_EQ           : thm := SCC.BIJECTIONS_CARD_EQ
def WF_FINITE                    : thm := SCC.WF_FINITE
def WF_PSUBSET                   : thm := SCC.WF_PSUBSET
def le_c                         : thm := SCC.le_c
def lt_c                         : thm := SCC.lt_c
def eq_c                         : thm := SCC.eq_c
def ge_c                         : thm := SCC.ge_c
def gt_c                         : thm := SCC.gt_c
def LE_C                         : thm := SCC.LE_C
def GE_C                         : thm := SCC.GE_C
def COUNTABLE                    : thm := SCC.COUNTABLE
-- SetsSup (sets.ml 4698-5027)
def sup                          : thm := SSup.sup
def SUP_EQ                       : thm := SSup.SUP_EQ
def SUP                          : thm := SSup.SUP
def SUP_FINITE_LEMMA             : thm := SSup.SUP_FINITE_LEMMA
def SUP_FINITE                   : thm := SSup.SUP_FINITE
def REAL_LE_SUP_FINITE           : thm := SSup.REAL_LE_SUP_FINITE
def REAL_SUP_LE_FINITE           : thm := SSup.REAL_SUP_LE_FINITE
def REAL_LT_SUP_FINITE           : thm := SSup.REAL_LT_SUP_FINITE
def REAL_SUP_LT_FINITE           : thm := SSup.REAL_SUP_LT_FINITE
def REAL_SUP_UNIQUE              : thm := SSup.REAL_SUP_UNIQUE
def REAL_SUP_LE                  : thm := SSup.REAL_SUP_LE
def REAL_SUP_LE_SUBSET           : thm := SSup.REAL_SUP_LE_SUBSET
def REAL_SUP_BOUNDS              : thm := SSup.REAL_SUP_BOUNDS
def REAL_ABS_SUP_LE              : thm := SSup.REAL_ABS_SUP_LE
def REAL_SUP_ASCLOSE             : thm := SSup.REAL_SUP_ASCLOSE
def SUP_UNIQUE_FINITE            : thm := SSup.SUP_UNIQUE_FINITE
def SUP_INSERT_FINITE            : thm := SSup.SUP_INSERT_FINITE
def SUP_SING                     : thm := SSup.SUP_SING
def SUP_INSERT_INSERT            : thm := SSup.SUP_INSERT_INSERT
def REAL_LE_SUP                  : thm := SSup.REAL_LE_SUP
def REAL_SUP_LE_EQ               : thm := SSup.REAL_SUP_LE_EQ
def SUP_UNIQUE                    : thm := SSup.SUP_UNIQUE
def SUP_UNION                    : thm := SSup.SUP_UNION
def ELEMENT_LE_SUP               : thm := SSup.ELEMENT_LE_SUP
def SUP_APPROACH                 : thm := SSup.SUP_APPROACH
def REAL_MAX_SUP                 : thm := SSup.REAL_MAX_SUP
def inf                          : thm := SSup.inf
def INF_EQ                       : thm := SSup.INF_EQ
def INF                          : thm := SSup.INF
def INF_FINITE_LEMMA             : thm := SSup.INF_FINITE_LEMMA
def INF_FINITE                   : thm := SSup.INF_FINITE
def REAL_LE_INF_FINITE           : thm := SSup.REAL_LE_INF_FINITE
def REAL_INF_LE_FINITE           : thm := SSup.REAL_INF_LE_FINITE
def REAL_LT_INF_FINITE           : thm := SSup.REAL_LT_INF_FINITE
def REAL_INF_LT_FINITE           : thm := SSup.REAL_INF_LT_FINITE
def REAL_INF_UNIQUE              : thm := SSup.REAL_INF_UNIQUE
def REAL_LE_INF                  : thm := SSup.REAL_LE_INF
def REAL_LE_INF_SUBSET           : thm := SSup.REAL_LE_INF_SUBSET
def REAL_INF_BOUNDS              : thm := SSup.REAL_INF_BOUNDS
def REAL_ABS_INF_LE              : thm := SSup.REAL_ABS_INF_LE
def REAL_INF_ASCLOSE             : thm := SSup.REAL_INF_ASCLOSE
def INF_UNIQUE_FINITE            : thm := SSup.INF_UNIQUE_FINITE
def INF_INSERT_FINITE            : thm := SSup.INF_INSERT_FINITE
def INF_SING                     : thm := SSup.INF_SING
def INF_INSERT_INSERT            : thm := SSup.INF_INSERT_INSERT
def REAL_SUP_EQ_INF              : thm := SSup.REAL_SUP_EQ_INF
def REAL_INF_LE                  : thm := SSup.REAL_INF_LE
def REAL_LE_INF_EQ               : thm := SSup.REAL_LE_INF_EQ
def INF_UNIQUE                    : thm := SSup.INF_UNIQUE
def INF_UNION                    : thm := SSup.INF_UNION
def INF_LE_ELEMENT               : thm := SSup.INF_LE_ELEMENT
def INF_APPROACH                 : thm := SSup.INF_APPROACH
def REAL_MIN_INF                 : thm := SSup.REAL_MIN_INF
-- SetsHasInfSup (sets.ml 5028-5182)
def has_inf                      : thm := SISup.has_inf
def has_sup                      : thm := SISup.has_sup
def HAS_INF_LBOUND               : thm := SISup.HAS_INF_LBOUND
def HAS_SUP_UBOUND               : thm := SISup.HAS_SUP_UBOUND
def HAS_INF_INF                  : thm := SISup.HAS_INF_INF
def HAS_SUP_SUP                  : thm := SISup.HAS_SUP_SUP
def INF_EXISTS                   : thm := SISup.INF_EXISTS
def SUP_EXISTS                   : thm := SISup.SUP_EXISTS
def HAS_INF_APPROACH             : thm := SISup.HAS_INF_APPROACH
def HAS_SUP_APPROACH             : thm := SISup.HAS_SUP_APPROACH
def HAS_INF                      : thm := SISup.HAS_INF
def HAS_SUP                      : thm := SISup.HAS_SUP
def HAS_INF_LE                   : thm := SISup.HAS_INF_LE
def HAS_SUP_LE                   : thm := SISup.HAS_SUP_LE

end Session
