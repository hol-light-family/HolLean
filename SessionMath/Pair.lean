/- File: SessionMath/Pair.lean
pair.ml: ordered pairs, paired abstractions and the paired
`new_definition` (with `the_definitions`), built by `initialize` when this
module is imported, and its names as top-level names.  Also the `HolBase`
instance over the core bundles, which HolMath's setups take.
-/
import SessionCore.ImpConv
import HolMath.Pair

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Simp HolCore.Theorems HolCore.Classic

namespace Session


/-- The core bundles, for HolMath's setups (safe: plain constants now). -/
instance sessionHolBase : HolLight.HolBase := ⟨B, C, T⟩

deriving instance Inhabited for HolMath.Pair.PairDefs
deriving instance Inhabited for HolMath.Pair.PairThms

private def ioOk' {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")

private def pt (s : String) : IO term := ioOk' s!"parse {s}" (HolCore.Parser.parse_term s)

private def pairDef (label s : String) : IO thm := do
  ioOk' label (do Drule.new_definition B (← pt s))

initialize pairAux : HolMath.Pair.PairDefs ← do
  let LET_DEF ← pairDef "LET_DEF" "LET (f:A->B) x = f x"
  let LET_END_DEF ← pairDef "LET_END_DEF" "LET_END (t:A) = t"
  let GABS_DEF ← pairDef "GABS_DEF" "GABS (P:A->bool) = (@) P"
  let GEQ_DEF ← pairDef "GEQ_DEF" "GEQ a b = (a:A = b)"
  let _SEQPATTERN ← pairDef "_SEQPATTERN"
    "_SEQPATTERN = \\(r:A->B->bool) s x. if ?y. r x y then r x else s x"
  let _UNGUARDED_PATTERN ← pairDef "_UNGUARDED_PATTERN" "_UNGUARDED_PATTERN = \\p r. p /\\ r"
  let _GUARDED_PATTERN ← pairDef "_GUARDED_PATTERN" "_GUARDED_PATTERN = \\p g r. p /\\ g /\\ r"
  let _MATCH ← pairDef "_MATCH"
    "_MATCH =  \\e (r:A->B->bool). if (?!) (r e) then (@) (r e) else @z. F"
  let _FUNCTION ← pairDef "_FUNCTION"
    "_FUNCTION = \\(r:A->B->bool) x. if (?!) (r x) then (@) (r x) else @z. F"
  let mk_pair_def ← pairDef "mk_pair_def" "mk_pair (x:A) (y:B) = \\a b. (a = x) /\\ (b = y)"
  let PAIR_EXISTS_THM ← ioOk' "PAIR_EXISTS_THM" (MESON [] (← pt "?x. ?(a:A) (b:B). x = mk_pair a b"))
  let prod_tybij ← ioOk' "prod_tybij" (new_type_definition "prod" "ABS_prod" "REP_prod" PAIR_EXISTS_THM)
  HolCore.Printer.parse_as_infix (",", (14, "right"))
  let COMMA_DEF ← pairDef "COMMA_DEF" "(x:A),(y:B) = ABS_prod(mk_pair x y)"
  let FST_DEF ← pairDef "FST_DEF" "FST (p:A#B) = @x. ?y. p = x,y"
  let SND_DEF ← pairDef "SND_DEF" "SND (p:A#B) = @y. ?x. p = x,y"
  pure { LET_DEF, LET_END_DEF, GABS_DEF, GEQ_DEF
         SEQPATTERN := _SEQPATTERN, UNGUARDED_PATTERN := _UNGUARDED_PATTERN
         GUARDED_PATTERN := _GUARDED_PATTERN, MATCH := _MATCH, FUNCTION := _FUNCTION
         mk_pair_def, PAIR_EXISTS_THM, prod_tybij, COMMA_DEF, FST_DEF, SND_DEF }

initialize theProjectionCache : IO.Ref (List (String × List thm)) ← IO.mkRef []
/-- The `GABS_RULE` lemma, proved while pair.ml's setup installs GEN_BETA_CONV. -/
initialize theGabsRulePth : IO.Ref (Option thm) ← IO.mkRef none

private def genBetaDepsWith (gabs : thm) : HolMath.Pair.GenBetaDeps :=
  { cache := theProjectionCache
    store := theInductiveTypeStore.get
    GEQ_DEF := pairAux.GEQ_DEF
    gabsRulePth := gabs }

private def installGenBeta (fstT sndT pairT indT recT : thm) : IO (Except String Unit) :=
  ExceptT.run do
    let _ ← ExceptT.mk (Simp.extend_basic_rewrites B [fstT, sndT, pairT])
    theInductiveTypeStore.modify (("prod", (1, indT, recT)) :: ·)
    let gabs ← ExceptT.mk (Tactics.prove B (← ExceptT.mk (HolCore.Parser.parse_term "(?) P ==> P (GABS P)"))
      (Simp.SIMP_TAC B [pairAux.GABS_DEF, SELECT_AX, ETA_AX]))
    theGabsRulePth.set (some gabs)
    let pat ← ExceptT.mk (HolCore.Parser.parse_term "GABS (\\a. b) c")
    ExceptT.mk (Simp.extend_basic_convs B "GEN_BETA_CONV"
      (pat, HolMath.Pair.GEN_BETA_CONV (genBetaDepsWith gabs)))

initialize pairLayer : HolMath.Pair.PairThms ← do
  let P := pairAux
  ioOk' "setupPair" (HolMath.Pair.setupPair DSL ETA_AX
    P.PAIR_EXISTS_THM P.prod_tybij P.mk_pair_def P.COMMA_DEF P.FST_DEF P.SND_DEF
    o_DEF MESON_TAC ASM_MESON_TAC MESON SELECT_ELIM_TAC installGenBeta).run

initialize gabsRulePth : thm ← do
  match ← theGabsRulePth.get with
  | some t => pure t
  | none => throw (IO.userError "GABS_RULE lemma not proved by setupPair")

def Pr : HolMath.Pair.PairThms := pairLayer
/-- `GEN_BETA_CONV` (pair.ml), applied to the session state. -/
def GEN_BETA_CONV : ioconv := HolMath.Pair.GEN_BETA_CONV (genBetaDepsWith gabsRulePth)

-- Expose the pair.ml definitions.
def LET_DEF : thm := pairAux.LET_DEF
def LET_END_DEF : thm := pairAux.LET_END_DEF
def GABS_DEF : thm := pairAux.GABS_DEF
/-- The pair.ml syntactic-sugar definitions (`_SEQPATTERN`, `_MATCH`, ...),
    whose OCaml names begin with `_`; `Database.lean` names them. -/
def pairSugarDefs : HolMath.Pair.PairDefs := pairAux
def GEQ_DEF : thm := pairAux.GEQ_DEF
def mk_pair_def : thm := pairAux.mk_pair_def
def prod_tybij : thm := pairAux.prod_tybij
def COMMA_DEF : thm := pairAux.COMMA_DEF
def FST_DEF : thm := pairAux.FST_DEF
def SND_DEF : thm := pairAux.SND_DEF

-- Expose the pair.ml theorems.
def PAIR_EXISTS_THM := Pr.PAIR_EXISTS_THM
def REP_ABS_PAIR := Pr.REP_ABS_PAIR
def PAIR_EQ := Pr.PAIR_EQ
def PAIR_SURJECTIVE := Pr.PAIR_SURJECTIVE
def FST := Pr.FST
def SND := Pr.SND
def PAIR := Pr.PAIR
def pair_INDUCT := Pr.pair_INDUCT
def pair_RECURSION := Pr.pair_RECURSION
def FORALL_PAIR_THM := Pr.FORALL_PAIR_THM
def EXISTS_PAIR_THM := Pr.EXISTS_PAIR_THM
def LAMBDA_PAIR_THM := Pr.LAMBDA_PAIR_THM
def LAMBDA_PAIR := Pr.LAMBDA_PAIR
def LAMBDA_TRIPLE_THM := Pr.LAMBDA_TRIPLE_THM
def LAMBDA_TRIPLE := Pr.LAMBDA_TRIPLE
def PAIRED_ETA_THM := Pr.PAIRED_ETA_THM
def FORALL_UNCURRY := Pr.FORALL_UNCURRY
def EXISTS_UNCURRY := Pr.EXISTS_UNCURRY
def EXISTS_CURRY := Pr.EXISTS_CURRY
def FORALL_CURRY := Pr.FORALL_CURRY
def FORALL_UNPAIR_THM := Pr.FORALL_UNPAIR_THM
def EXISTS_UNPAIR_THM := Pr.EXISTS_UNPAIR_THM
def FORALL_PAIR_FUN_THM := Pr.FORALL_PAIR_FUN_THM
def EXISTS_PAIR_FUN_THM := Pr.EXISTS_PAIR_FUN_THM
def FORALL_UNPAIR_FUN_THM := Pr.FORALL_UNPAIR_FUN_THM
def EXISTS_UNPAIR_FUN_THM := Pr.EXISTS_UNPAIR_FUN_THM
def EXISTS_SWAP_FUN_THM := Pr.EXISTS_SWAP_FUN_THM
def FORALL_PAIRED_THM := Pr.FORALL_PAIRED_THM
def EXISTS_PAIRED_THM := Pr.EXISTS_PAIRED_THM
def FORALL_TRIPLED_THM := Pr.FORALL_TRIPLED_THM
def EXISTS_TRIPLED_THM := Pr.EXISTS_TRIPLED_THM
def CHOICE_UNPAIR_THM := Pr.CHOICE_UNPAIR_THM
def CHOICE_PAIRED_THM := Pr.CHOICE_PAIRED_THM

/- pair.ml: syntax operations. -/
/-- `is_pair = is_binary ","` (`HolMath.Pair`). -/
def is_pair : term → Bool := HolMath.Pair.is_pair
/-- `dest_pair = dest_binary ","` (`HolMath.Pair`). -/
def dest_pair : term → Except String (term × term) := HolMath.Pair.dest_pair
/-- `lex` (parser.ml 102) on the current lexical tables. -/
def lex (chars : List String) : IO (Except String (List HolCore.Parser.lexcode)) := do
  match HolCore.Parser.lex (← HolCore.Parser.mkCtx) chars with
  | .ok l => return .ok l
  | .error e => return .error (HolCore.Parser.perrMsg e)
/-- `GABS_CONV conv` (pair.ml 200): apply `conv` to the body of a generalized
    abstraction `\(x,y). t`, or of an ordinary one. -/
def GABS_CONV (conv : ioconv) : ioconv := HolMath.Pair.GABS_CONV conv
/-- `mk_pair (l,r)`: build the pair `l,r` (`HolMath.Pair`). -/
def mk_pair : term × term → IO (Except String term) := HolMath.Pair.mk_pair

/- pair.ml's `new_definition` over paired varstructs, with `the_definitions`. -/
initialize theDefinitions : IO.Ref (List thm) ←
  IO.mkRef [pairAux.SND_DEF, pairAux.FST_DEF, pairAux.COMMA_DEF, pairAux.mk_pair_def,
    pairAux.GEQ_DEF, pairAux.GABS_DEF, pairAux.LET_END_DEF, pairAux.LET_DEF,
    one_DEF, I_DEF, o_DEF, COND_DEF, FALSITY_DEF,
    B.EXISTS_UNIQUE_DEF, B.NOT_DEF, B.F_DEF, B.OR_DEF, B.EXISTS_DEF,
    B.FORALL_DEF, B.IMP_DEF, B.AND_DEF, B.T_DEF]

/-- `!the_definitions` (pair.ml 148). -/
def get_the_definitions : IO (List thm) := theDefinitions.get
/-- `the_definitions := l`. -/
def set_the_definitions (l : List thm) : IO Unit := theDefinitions.set l

/-- `new_definition` redefined to allow paired varstructs (pair.ml).  Depairs
    paired arguments on the LHS via `FST`/`SND`, defines the depaired equation
    with the primitive `new_definition`, then reconstitutes the paired form. -/
partial def new_definition (tm : term) : IO (Except String thm) := ExceptT.run do
  let rec depairAcc (gv arg : term) : IO (Except String (List (term × term))) := ExceptT.run do
    match HolMath.Pair.dest_pair arg with
    | .ok (l, r) =>
        let fstGv ← ExceptT.mk (Basics.list_mk_icomb "FST" [gv])
        let sndGv ← ExceptT.mk (Basics.list_mk_icomb "SND" [gv])
        let ls ← ExceptT.mk (depairAcc fstGv l)
        let rs ← ExceptT.mk (depairAcc sndGv r)
        pure (ls ++ rs)
    | .error _ => pure [(gv, arg)]
  let depair (arg : term) : IO (Except String (term × List (term × term))) := ExceptT.run do
    let gv ← (Basics.genvar (type_of arg) : IO term)
    let reps ← ExceptT.mk (depairAcc gv arg)
    pure (gv, reps)
  let (avs, def0) := Basics.strip_forall tm
  let idFn : term → Except String term := fun t => .ok t
  let defs ← theDefinitions.get
  let tryBenign : IO (Option thm) := do
    let rec first : List thm → IO (Option (thm × thm))
      | [] => pure none
      | th :: rest => do
        match ← (Drule.PART_MATCH B idFn th def0 : IO (Except String thm)) with
        | .ok th' => pure (some (th, th'))
        | .error _ => first rest
    match ← first defs with
    | none => pure none
    | some (th, th') =>
      match ← (Drule.PART_MATCH B idFn th' (Basics.strip_forall (concl th)).2 : IO (Except String thm)) with
      | .error _ => pure none
      | .ok _ =>
        HolCore.Lib.warn true "Benign redefinition"
        match (do B.GEN_ALL (← B.GENL avs th') : Except String thm) with
        | .ok r => pure (some r)
        | .error _ => pure none
  match ← tryBenign with
  | some r => pure r
  | none =>
    let (l, r) ← liftExcept (dest_eq def0)
    let (fn, args) := Basics.strip_comb l
    let mut pairs : List (term × List (term × term)) := []
    for a in args do
      let p ← (depair a : IO (Except String (term × List (term × term))))
      pairs := pairs ++ [p]
    let gargs := pairs.map Prod.fst
    let reps := Lib.unions (pairs.map Prod.snd)
    let l' ← liftExcept (Basics.list_mk_comb fn gargs)
    let substFn ← (Basics.subst reps : IO (Except String (term → IO (Except String term))))
    let r' ← (substFn r : IO (Except String term))
    let eqtm := safe_mk_eq l' r'
    let th1 ← ExceptT.mk (Drule.new_definition B eqtm)
    let slist ← liftExcept (Lib.zip args gargs)
    let th2 ← liftExcept (do Drule.INSTANTIATE ([], slist, []) (← B.SPEC_ALL th1))
    let substSl ← (Basics.subst slist : IO (Except String (term → IO (Except String term))))
    let mut xreps : List term := []
    for rep in reps do
      let x ← (substSl rep.1 : IO (Except String term))
      xreps := xreps ++ [x]
    let mut threps : List thm := []
    for x in xreps do
      let c ← (Simp.PURE_REWRITE_CONV' B [Pr.FST, Pr.SND] x : IO (Except String thm))
      threps := threps ++ [(← liftExcept (Equal.SYM c))]
    let subsc ← ExceptT.mk (Equal.SUBS_CONV threps r)
    let th3 ← liftExcept (do TRANS th2 (← Equal.SYM subsc))
    let th4 ← liftExcept (do B.GEN_ALL (← B.GENL avs th3))
    theDefinitions.modify (th4 :: ·)
    pure th4

/- pair.ml 184-192: CURRY, UNCURRY, PASSOC; pair.ml 450: LET_TAC's lemmas. -/
initialize curryDefs : thm × thm × thm ← (do
  let curryD ← ioOk' "CURRY_DEF" (do new_definition (← pt "CURRY(f:A#B->C) x y = f(x,y)"))
  let uncurryD ← ioOk' "UNCURRY_DEF" (do new_definition (← pt "!f x y. UNCURRY(f:A->B->C)(x,y) = f x y"))
  let passocD ← ioOk' "PASSOC_DEF" (do new_definition (← pt "!f x y z. PASSOC (f:(A#B)#C->D) (x,y,z) = f ((x,y),z)"))
  pure (curryD, uncurryD, passocD))

initialize letTacPths : thm × thm × thm ← do
  let pth ← ioOk' "LET_TAC pth" (MESON [Pr.PAIR, Pr.PAIR_EQ] (← pt "((x,y) = a) <=> (x = FST a) /\\ (y = SND a)"))
  let taut2 ← ioOk' "LET_TAC taut2" (TAUT (← pt "a /\\ T <=> a"))
  let taut1 ← ioOk' "LET_TAC taut1" (TAUT (← pt "(x = x) <=> T"))
  pure (pth, taut1, taut2)

def letDeps : HolMath.Pair.LetDeps :=
  { LET_DEF := pairAux.LET_DEF, LET_END_DEF := pairAux.LET_END_DEF
    letTacPth := letTacPths.1, taut1 := letTacPths.2.1, taut2 := letTacPths.2.2 }
def CURRY_DEF : thm := curryDefs.1
def UNCURRY_DEF : thm := curryDefs.2.1
def PASSOC_DEF : thm := curryDefs.2.2

/-- `let_CONV`: expand a `let`-term (pair.ml). -/
def let_CONV : ioconv := HolMath.Pair.let_CONV letDeps GEN_BETA_CONV

/-- `SUBLET_CONV conv`: apply `conv` to the RHS of a top-level `let`-term. -/
def SUBLET_CONV : ioconv → term → IO (Except String thm) :=
  HolMath.Pair.SUBLET_CONV

/-- `LET_TAC` (pair.ml). -/
def LET_TAC : tactic := HolMath.Pair.LET_TAC letDeps GEN_BETA_CONV

end Session
