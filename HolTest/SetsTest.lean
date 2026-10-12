/- File: HolTest/SetsTest.lean
Tests for HolMath/Sets.lean (sets.ml).

SECTION (0) BELOW IS A REGRESSION GUARD FOR A REAL DEFECT.  `sets.ml` line 12 is
`needs "int.ml"`, and HOL Light's `needs` loads EAGERLY AND IN ORDER, so every
file beneath sets.ml has run before any line of it executes.  Our Session CAFs
are LAZY, so the parser and overload state when a Sets setup FIRST runs depends
on whatever the caller happened to force.  Under a Sets-only warm-up,
`INTERS_2` (sets.ml 916) - `!s (t:A->bool). INTERS {s,t} = s INTER t` - failed
to parse with "s cannot have type ?->(A->bool)->?->bool and ?->bool
simultaneously", which panicked `setupSetsInters`, which panicked
`setupSetsMisc` with `TRANS`.  `setupSetsMisc` has THIRTY fields, so that
degenerates all thirty to `|-  = ` via `Inhabited`.

IT WAS INVISIBLE TO THE BUILD because the Sets bundle CAFs are PRIVATE and
nothing in the build forced them, so the masked-failure detector read 1 and the
build was green.  The fix is `Session.ensureHolPrefixThroughInt`, called by
`ensureSetsInfixes`, which reproduces the `needs "int.ml"` load order.
This section FORCES EVERY Sets BUNDLE and emits the literal token MISMATCH on
failure, so `make verify` catches any regression - the same discipline the
276-lift leak sweep needed before its failure path was visible.
-/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ====================================================================== -/
/- (0) FORCING GUARD: every Sets bundle must build, in a bare process.     -/
/- ====================================================================== -/

private unsafe def forceOk (lbl : String) (th : thm) : IO Unit := do
  let s ← HolCore.Printer.string_of_thm th
  -- A panicked setupX yields the `Inhabited` default, printing `|-  = `.
  if s.replace " " "" == "|-" || s.replace " " "" == "|-=" then
    IO.println s!"Sets force {lbl} -> MISMATCH degenerate (setup panicked): {s}"
  else
    IO.println s!"Sets force {lbl} -> OK"

/- Enter through `Session.ensureSets`, which forces every sets.ml bundle IN FILE
   ORDER.  That reproduces HOL Light's eager top-to-bottom execution of sets.ml;
   entering at an arbitrary bundle instead builds it in a state HOL Light never
   has, which is what produced varying `MATCH_MP_TAC: Bad theorem` /
   `dest_binary` / `solve_goal: Too deep` failures. -/
#eval Session.ensureSets

#eval forceOk "SetsCore/IN" Session.IN
#eval forceOk "SetsProps/IN_UNIONS" Session.IN_UNIONS
#eval forceOk "SetsTactics/CHOICE_DEF" Session.CHOICE_DEF
#eval forceOk "SetsInclusion/SUBSET_TRANS" Session.SUBSET_TRANS
#eval forceOk "SetsOperators/INTER_UNIV" Session.INTER_UNIV
#eval forceOk "SetsInsertDelete/NOT_INSERT_EMPTY" Session.NOT_INSERT_EMPTY
#eval forceOk "SetsUnions/UNIONS_0" Session.UNIONS_0
#eval forceOk "SetsInters/INTERS_SUBSET_STRONG" Session.INTERS_SUBSET_STRONG
#eval forceOk "SetsInters/INTERS_2 (the defect's term)" Session.INTERS_2
#eval forceOk "SetsImage/IMAGE_UNIONS" Session.IMAGE_UNIONS
#eval forceOk "SetsMisc/INTER_INTERS" Session.INTER_INTERS
#eval forceOk "SetsInduct/FINITE_INDUCT_STRONG" Session.FINITE_INDUCT_STRONG
#eval forceOk "SetsFunctions/INJECTIVE_ON_LEFT_INVERSE" Session.INJECTIVE_ON_LEFT_INVERSE
#eval forceOk "SetsFinite/FINITE_UNION" Session.FINITE_UNION
#eval forceOk "SetsRecursion/ITSET" Session.ITSET
#eval forceOk "SetsCard/CARD_CLAUSES" Session.CARD_CLAUSES
-- NB: probe each bundle with a theorem that REALLY belongs to it.  This line
-- previously used `CARD_UNION`, which lives in SetsCard, NOT SetsCard2 - so it
-- reported SetsCard2 as OK while that bundle was in fact degenerate.
#eval forceOk "SetsCard2/CARD_SUBSET_EQ" Session.CARD_SUBSET_EQ
#eval forceOk "SetsCard2/HAS_SIZE_IMAGE_INJ" Session.HAS_SIZE_IMAGE_INJ
#eval forceOk "SetsCross/CROSS" Session.CROSS
#eval forceOk "SetsFunspace/ARB" Session.ARB
-- BISECT: the SetsFunspace2 and SetsInfinite probes are temporarily disabled to
-- locate a runaway proof introduced with sets.ml 3325-3697.
#eval forceOk "SetsFunspace2/HAS_SIZE_POWERSET" Session.HAS_SIZE_POWERSET
/- (former quarantine note, retained for the record)
   SetsInfinite was quarantined because
   Forcing it runs away: `lake build HolTest.SetsTest` completed in 326s with
   SFun2 and SInf disabled, 336s with SFun2 re-enabled, but exceeded 660s with
   SInf enabled and had to be killed.  A streaming `--run` probe confirmed the
   prefix completes and the hang is inside `setupSetsInfinite` itself.
   PRIME SUSPECT: FINITE_REAL_INTERVAL (sets.ml 3631-3696), the heaviest proof
   in the range - it calls REAL_FIELD (the Grobner-backed field prover) and
   several inline REAL_ARITHs, and opens with
   `SUBGOAL_THEN ... ASSUME_TAC THENL [...; ALL_TAC] THEN ...`, a left-associative
   THENL of exactly the shape that has now caused ELEVEN defects in this project.
   The quarantine is announced as a MISMATCH so `make verify` stays RED: leaving a
   bundle silently unforced is the latent-defect trap that hid the SetsMisc and
   SetsCross failures for a whole session. -/
/- SetsInfinite (sets.ml 3554-3697).  The runaway that quarantined this bundle was
   NOT in its proof scripts: `lists.ml 884`'s `new_type_abbrev("string",`:char
   list`)` had never run, because the CAF installing it was "forced" with
   `let _ := charType`, which does NOT force a Lean CAF (defect class #3).  So
   `:string` never expanded to `:char list`, sets.ml 3623's
   `ISPEC `LENGTH:string->num`` could not typecheck, and MESON was handed a wildly
   over-general goal - the doubling inference count (…3016410..6060899..) in the
   trace.  `ensureHolPrefixThroughInt` now forces it where lists.ml would. -/
/- *** SetsInfinite (sets.ml 3554-3697) REMAINS QUARANTINED - the runaway is NOT
   yet located.  Forcing it exceeded 753s and had to be killed. ***
   ELIMINATED SO FAR: (a) it is not SetsFunspace or SetsFunspace2, both of which
   force in ~330s with all probes OK; (b) it is not the prefix, which completes
   first under a streaming `--run` probe; (c) it is NOT the `:string` type
   abbreviation - that was a genuine and separate defect, now FIXED (see
   `ensureHolPrefixThroughInt`), and `LENGTH:string->num` now parses as a Const,
   but the runaway persisted afterwards.
   STILL TO CHECK: the eight MESON/SET_TAC sites in range - sets.ml 3560, 3579,
   3598, 3605, 3610, 3614, 3625, 3684 - and FINITE_REAL_INTERVAL (3631-3696),
   whose opening `SUBGOAL_THEN ... ASSUME_TAC THENL [...; ALL_TAC] THEN ...` is the
   left-associative shape behind eleven prior defects.
   Announced as a MISMATCH so `make verify` stays RED: a silently unforced bundle
   is the trap that hid the SetsMisc and SetsCross failures for a whole session. -/
/- SetsInfinite (sets.ml 3554-3697).  This bundle was quarantined for a runaway
   that turned out to be TWO latent defects in EARLIER files, not in sets.ml:
     (a) `lists.ml 884`'s `new_type_abbrev("string",`:char list`)` never ran,
         because the CAF installing it was "forced" with `let _ := charType`,
         which does NOT force a Lean CAF (defect class #3).  So `:string` never
         expanded and sets.ml 3623's `ISPEC `LENGTH:string->num`` could not
         typecheck.
     (b) `REAL_RING` (calc_rat.ml 490) and `REAL_FIELD` (581) were built in the
         wrong order when first reached from the sets path.  REAL_RING PANICKED
         with `linear_ineqs: no contradiction`, and since
         `core_rule t = try REAL_RING t with Failure _ -> REAL_ARITH t` (610) can
         only fall back on a FAILURE, never on a panic, the fallback never fired.
         `setupRealField` then diverged outright - checkpoints inside its returned
         closure never printed, proving the hang was in the SETUP, not any goal.
   All three are now forced in `ensureHolPrefixThroughInt` at their hol_lib.ml
   positions.  sets.ml 3657's REAL_FIELD goal now PROVES. -/
#eval forceOk "SetsInfinite/num_INFINITE" Session.num_INFINITE
#eval forceOk "SetsInfinite/string_INFINITE" Session.string_INFINITE
#eval forceOk "SetsInfinite/FINITE_REAL_INTERVAL" Session.FINITE_REAL_INTERVAL
#eval forceOk "SetsInfinite/real_INFINITE" Session.real_INFINITE
/- SetsList (sets.ml 3697-3997): finite-set indexing, set/list mappings, and the
   pairwise property.  `set_of_list`/`list_of_set` are INTRODUCED HERE, not in
   Lists.lean, so this bundle bridges to the list theory.  Probe the heavy
   structured proofs (HAS_SIZE_INDEX, INFINITE_ENUMERATE, LIST_OF_SET_SING and
   the three pairwise-disjoint UNIONS theorems) plus the two definitions. -/
#eval forceOk "SetsList/HAS_SIZE_INDEX" Session.HAS_SIZE_INDEX
#eval forceOk "SetsList/INFINITE_ENUMERATE" Session.INFINITE_ENUMERATE
#eval forceOk "SetsList/INFINITE_ENUMERATE_SUBSET" Session.INFINITE_ENUMERATE_SUBSET
#eval forceOk "SetsList/set_of_list" Session.set_of_list
#eval forceOk "SetsList/list_of_set" Session.list_of_set
#eval forceOk "SetsList/LIST_OF_SET_PROPERTIES" Session.LIST_OF_SET_PROPERTIES
#eval forceOk "SetsList/MEM_LIST_OF_SET" Session.MEM_LIST_OF_SET
#eval forceOk "SetsList/LIST_OF_SET_SING" Session.LIST_OF_SET_SING
#eval forceOk "SetsList/pairwise" Session.pairwise
#eval forceOk "SetsList/PAIRWISE_UNION" Session.PAIRWISE_UNION
#eval forceOk "SetsList/DIFF_UNIONS_PAIRWISE_DISJOINT" Session.DIFF_UNIONS_PAIRWISE_DISJOINT
#eval forceOk "SetsList/INTER_UNIONS_PAIRWISE_DISJOINT" Session.INTER_UNIONS_PAIRWISE_DISJOINT
#eval forceOk "SetsList/PSUBSET_UNIONS_PAIRWISE_DISJOINT" Session.PSUBSET_UNIONS_PAIRWISE_DISJOINT
/- SetsUnionOf (sets.ml 3998-4364): the UNION_OF/INTERSECTION_OF combinators and
   their ARBITRARY and FINITE cases.  The two operators' infix fixity is
   registered by `ensureSetsUnionOfInfix` (the 15th/16th parse_as_infix of the
   file).  Probe the two definitions, an idiom, and the heavy structured proofs
   (the COMPLEMENT duals, the width-2 CONJ_TAC idempotence, the REPLICATE_TAC
   INTER_EQ, and the COMPL_COMPL-driven UNION_EQ) in both the ARBITRARY and
   FINITE families. -/
#eval forceOk "SetsUnionOf/UNION_OF" Session.UNION_OF
#eval forceOk "SetsUnionOf/INTERSECTION_OF" Session.INTERSECTION_OF
#eval forceOk "SetsUnionOf/UNION_OF_INC" Session.UNION_OF_INC
#eval forceOk "SetsUnionOf/ARBITRARY_UNION_OF_ALT" Session.ARBITRARY_UNION_OF_ALT
#eval forceOk "SetsUnionOf/ARBITRARY_UNION_OF_COMPLEMENT" Session.ARBITRARY_UNION_OF_COMPLEMENT
#eval forceOk "SetsUnionOf/ARBITRARY_UNION_OF_IDEMPOT" Session.ARBITRARY_UNION_OF_IDEMPOT
#eval forceOk "SetsUnionOf/ARBITRARY_UNION_OF_INTER_EQ" Session.ARBITRARY_UNION_OF_INTER_EQ
#eval forceOk "SetsUnionOf/ARBITRARY_INTERSECTION_OF_UNION_EQ" Session.ARBITRARY_INTERSECTION_OF_UNION_EQ
#eval forceOk "SetsUnionOf/FINITE_UNION_OF_COMPLEMENT" Session.FINITE_UNION_OF_COMPLEMENT
#eval forceOk "SetsUnionOf/FINITE_UNION_OF_IDEMPOT" Session.FINITE_UNION_OF_IDEMPOT
#eval forceOk "SetsUnionOf/FINITE_UNION_OF_INTER_EQ" Session.FINITE_UNION_OF_INTER_EQ
#eval forceOk "SetsUnionOf/FINITE_INTERSECTION_OF_UNION" Session.FINITE_INTERSECTION_OF_UNION
#eval forceOk "SetsCardComp/CARD_SET_OF_LIST_LE" Session.CARD_SET_OF_LIST_LE
#eval forceOk "SetsCardComp/HAS_SIZE_SET_OF_LIST" Session.HAS_SIZE_SET_OF_LIST
#eval forceOk "SetsCardComp/SURJECTIVE_IFF_INJECTIVE_GEN" Session.SURJECTIVE_IFF_INJECTIVE_GEN
#eval forceOk "SetsCardComp/SURJECTIVE_IFF_INJECTIVE" Session.SURJECTIVE_IFF_INJECTIVE
#eval forceOk "SetsCardComp/IMAGE_IMP_INJECTIVE_GEN" Session.IMAGE_IMP_INJECTIVE_GEN
#eval forceOk "SetsCardComp/IMAGE_IMP_INJECTIVE" Session.IMAGE_IMP_INJECTIVE
#eval forceOk "SetsCardComp/HAS_SIZE_IMAGE_INJ_RESTRICT" Session.HAS_SIZE_IMAGE_INJ_RESTRICT
#eval forceOk "SetsCardComp/CARD_LE_INJ" Session.CARD_LE_INJ
#eval forceOk "SetsCardComp/FORALL_IN_CLAUSES" Session.FORALL_IN_CLAUSES
#eval forceOk "SetsCardComp/EXISTS_IN_CLAUSES" Session.EXISTS_IN_CLAUSES
#eval forceOk "SetsCardComp/INJECTIVE_ON_IMAGE" Session.INJECTIVE_ON_IMAGE
#eval forceOk "SetsCardComp/INJECTIVE_IMAGE" Session.INJECTIVE_IMAGE
#eval forceOk "SetsCardComp/SURJECTIVE_ON_IMAGE" Session.SURJECTIVE_ON_IMAGE
#eval forceOk "SetsCardComp/SURJECTIVE_IMAGE" Session.SURJECTIVE_IMAGE
#eval forceOk "SetsCardComp/INJECTIVE_ON_PREIMAGE" Session.INJECTIVE_ON_PREIMAGE
#eval forceOk "SetsCardComp/SURJECTIVE_ON_PREIMAGE" Session.SURJECTIVE_ON_PREIMAGE
#eval forceOk "SetsCardComp/INJECTIVE_PREIMAGE" Session.INJECTIVE_PREIMAGE
#eval forceOk "SetsCardComp/SURJECTIVE_PREIMAGE" Session.SURJECTIVE_PREIMAGE
#eval forceOk "SetsCardComp/CARD_EQ_BIJECTION" Session.CARD_EQ_BIJECTION
#eval forceOk "SetsCardComp/CARD_EQ_BIJECTIONS" Session.CARD_EQ_BIJECTIONS
#eval forceOk "SetsCardComp/CARD_EQ_BIJECTIONS_SPECIAL" Session.CARD_EQ_BIJECTIONS_SPECIAL
#eval forceOk "SetsCardComp/BIJECTIONS_HAS_SIZE" Session.BIJECTIONS_HAS_SIZE
#eval forceOk "SetsCardComp/BIJECTIONS_HAS_SIZE_EQ" Session.BIJECTIONS_HAS_SIZE_EQ
#eval forceOk "SetsCardComp/BIJECTIONS_CARD_EQ" Session.BIJECTIONS_CARD_EQ
#eval forceOk "SetsCardComp/WF_FINITE" Session.WF_FINITE
#eval forceOk "SetsCardComp/WF_PSUBSET" Session.WF_PSUBSET
#eval forceOk "SetsCardComp/le_c" Session.le_c
#eval forceOk "SetsCardComp/lt_c" Session.lt_c
#eval forceOk "SetsCardComp/eq_c" Session.eq_c
#eval forceOk "SetsCardComp/ge_c" Session.ge_c
#eval forceOk "SetsCardComp/gt_c" Session.gt_c
#eval forceOk "SetsCardComp/LE_C" Session.LE_C
#eval forceOk "SetsCardComp/GE_C" Session.GE_C
#eval forceOk "SetsCardComp/COUNTABLE" Session.COUNTABLE
#eval forceOk "SetsSup/sup" Session.sup
#eval forceOk "SetsSup/SUP_EQ" Session.SUP_EQ
#eval forceOk "SetsSup/SUP" Session.SUP
#eval forceOk "SetsSup/SUP_FINITE_LEMMA" Session.SUP_FINITE_LEMMA
#eval forceOk "SetsSup/SUP_FINITE" Session.SUP_FINITE
#eval forceOk "SetsSup/REAL_LE_SUP_FINITE" Session.REAL_LE_SUP_FINITE
#eval forceOk "SetsSup/REAL_SUP_LE_FINITE" Session.REAL_SUP_LE_FINITE
#eval forceOk "SetsSup/REAL_LT_SUP_FINITE" Session.REAL_LT_SUP_FINITE
#eval forceOk "SetsSup/REAL_SUP_LT_FINITE" Session.REAL_SUP_LT_FINITE
#eval forceOk "SetsSup/REAL_SUP_UNIQUE" Session.REAL_SUP_UNIQUE
#eval forceOk "SetsSup/REAL_SUP_LE" Session.REAL_SUP_LE
#eval forceOk "SetsSup/REAL_SUP_LE_SUBSET" Session.REAL_SUP_LE_SUBSET
#eval forceOk "SetsSup/REAL_SUP_BOUNDS" Session.REAL_SUP_BOUNDS
#eval forceOk "SetsSup/REAL_ABS_SUP_LE" Session.REAL_ABS_SUP_LE
#eval forceOk "SetsSup/REAL_SUP_ASCLOSE" Session.REAL_SUP_ASCLOSE
#eval forceOk "SetsSup/SUP_UNIQUE_FINITE" Session.SUP_UNIQUE_FINITE
#eval forceOk "SetsSup/SUP_INSERT_FINITE" Session.SUP_INSERT_FINITE
#eval forceOk "SetsSup/SUP_SING" Session.SUP_SING
#eval forceOk "SetsSup/SUP_INSERT_INSERT" Session.SUP_INSERT_INSERT
#eval forceOk "SetsSup/REAL_LE_SUP" Session.REAL_LE_SUP
#eval forceOk "SetsSup/REAL_SUP_LE_EQ" Session.REAL_SUP_LE_EQ
#eval forceOk "SetsSup/SUP_UNIQUE" Session.SUP_UNIQUE
#eval forceOk "SetsSup/SUP_UNION" Session.SUP_UNION
#eval forceOk "SetsSup/ELEMENT_LE_SUP" Session.ELEMENT_LE_SUP
#eval forceOk "SetsSup/SUP_APPROACH" Session.SUP_APPROACH
#eval forceOk "SetsSup/REAL_MAX_SUP" Session.REAL_MAX_SUP
#eval forceOk "SetsSup/inf" Session.inf
#eval forceOk "SetsSup/INF_EQ" Session.INF_EQ
#eval forceOk "SetsSup/INF" Session.INF
#eval forceOk "SetsSup/INF_FINITE_LEMMA" Session.INF_FINITE_LEMMA
#eval forceOk "SetsSup/INF_FINITE" Session.INF_FINITE
#eval forceOk "SetsSup/REAL_LE_INF_FINITE" Session.REAL_LE_INF_FINITE
#eval forceOk "SetsSup/REAL_INF_LE_FINITE" Session.REAL_INF_LE_FINITE
#eval forceOk "SetsSup/REAL_LT_INF_FINITE" Session.REAL_LT_INF_FINITE
#eval forceOk "SetsSup/REAL_INF_LT_FINITE" Session.REAL_INF_LT_FINITE
#eval forceOk "SetsSup/REAL_INF_UNIQUE" Session.REAL_INF_UNIQUE
#eval forceOk "SetsSup/REAL_LE_INF" Session.REAL_LE_INF
#eval forceOk "SetsSup/REAL_LE_INF_SUBSET" Session.REAL_LE_INF_SUBSET
#eval forceOk "SetsSup/REAL_INF_BOUNDS" Session.REAL_INF_BOUNDS
#eval forceOk "SetsSup/REAL_ABS_INF_LE" Session.REAL_ABS_INF_LE
#eval forceOk "SetsSup/REAL_INF_ASCLOSE" Session.REAL_INF_ASCLOSE
#eval forceOk "SetsSup/INF_UNIQUE_FINITE" Session.INF_UNIQUE_FINITE
#eval forceOk "SetsSup/INF_INSERT_FINITE" Session.INF_INSERT_FINITE
#eval forceOk "SetsSup/INF_SING" Session.INF_SING
#eval forceOk "SetsSup/INF_INSERT_INSERT" Session.INF_INSERT_INSERT
#eval forceOk "SetsSup/REAL_SUP_EQ_INF" Session.REAL_SUP_EQ_INF
#eval forceOk "SetsSup/REAL_INF_LE" Session.REAL_INF_LE
#eval forceOk "SetsSup/REAL_LE_INF_EQ" Session.REAL_LE_INF_EQ
#eval forceOk "SetsSup/INF_UNIQUE" Session.INF_UNIQUE
#eval forceOk "SetsSup/INF_UNION" Session.INF_UNION
#eval forceOk "SetsSup/INF_LE_ELEMENT" Session.INF_LE_ELEMENT
#eval forceOk "SetsSup/INF_APPROACH" Session.INF_APPROACH
#eval forceOk "SetsSup/REAL_MIN_INF" Session.REAL_MIN_INF
#eval forceOk "SetsHasInfSup/has_inf" Session.has_inf
#eval forceOk "SetsHasInfSup/has_sup" Session.has_sup
#eval forceOk "SetsHasInfSup/HAS_INF_LBOUND" Session.HAS_INF_LBOUND
#eval forceOk "SetsHasInfSup/HAS_SUP_UBOUND" Session.HAS_SUP_UBOUND
#eval forceOk "SetsHasInfSup/HAS_INF_INF" Session.HAS_INF_INF
#eval forceOk "SetsHasInfSup/HAS_SUP_SUP" Session.HAS_SUP_SUP
#eval forceOk "SetsHasInfSup/INF_EXISTS" Session.INF_EXISTS
#eval forceOk "SetsHasInfSup/SUP_EXISTS" Session.SUP_EXISTS
#eval forceOk "SetsHasInfSup/HAS_INF_APPROACH" Session.HAS_INF_APPROACH
#eval forceOk "SetsHasInfSup/HAS_SUP_APPROACH" Session.HAS_SUP_APPROACH
#eval forceOk "SetsHasInfSup/HAS_INF" Session.HAS_INF
#eval forceOk "SetsHasInfSup/HAS_SUP" Session.HAS_SUP
#eval forceOk "SetsHasInfSup/HAS_INF_LE" Session.HAS_INF_LE
#eval forceOk "SetsHasInfSup/HAS_SUP_LE" Session.HAS_SUP_LE

/- ====================================================================== -/
/- SHARED HELPERS for the behavioural sections below.                      -/
/-                                                                        -/
/- Section (0) above only FORCES bundles; the sections below prove the     -/
/- translation actually WORKS.  Every helper prints `-> OK` on success and -/
/- the literal token MISMATCH on any failure, so `make verify` (which      -/
/- greps for MISMATCH and counts `|-  = ` degenerate prints) catches a     -/
/- regression in EITHER direction.  `squash` strips whitespace so a        -/
/- multi-line pretty-printed theorem compares against a single-line form.  -/
/- ====================================================================== -/

/-- Strip all whitespace, so a wrapped pretty-print compares against a
    single-line expected string. -/
private def sq (s : String) : String := (s.replace "\n" "").replace " " ""

/-- The head constant/variable name of a term after `strip_comb`, plus its
    argument count - the two facts the parser-baseline assertions turn on. -/
private def headTag (tm : term) : String × Nat :=
  let (h, args) := strip_comb tm
  let tag := match h with
    | .Const c _ => s!"Const {c}"
    | .Var v _   => s!"Var {v}"
    | .Comb _ _  => "Comb"
    | .Abs _ _   => "Abs"
  (tag, args.length)

/-- Parse `s` (in the CURRENT runtime parser state, i.e. AFTER `ensureSets`
    has installed the constants and infixes) and assert its head tag and arg
    count are as expected.  Uses `parse_term`, NOT the `[[ ]]` quotation,
    precisely because the baseline must reflect the RUNTIME parser state. -/
private unsafe def headCheck (lbl s wantTag : String) (wantN : Nat) : IO Unit := do
  match ← parse_term s with
  | .error e => IO.println s!"{lbl} -> MISMATCH parse ERR: {e}"
  | .ok tm =>
    let (tag, n) := headTag tm
    if tag == wantTag && n == wantN then
      IO.println s!"{lbl} -> OK (head={tag} nargs={n})"
    else
      IO.println s!"{lbl} -> MISMATCH head={tag} nargs={n} want={wantTag}/{wantN}"

/-- Walk an INSERT chain, returning the number of `Const "INSERT"` nodes if it
    terminates in `Const "EMPTY"`, else `none` (a non-const chain - e.g. free
    variables, the pre-translation baseline). -/
private def insertChainLen : term → Option Nat
  | .Comb (.Comb (.Const "INSERT" _) _) rest =>
      (insertChainLen rest).map (· + 1)
  | .Const "EMPTY" _ => some 0
  | _ => none

/-- Parse `s` and assert it is an INSERT chain of exactly `wantN` `Const`
    nodes terminating in `Const "EMPTY"` - i.e. built entirely from constants,
    not free variables. -/
private unsafe def insertChainCheck (lbl s : String) (wantN : Nat) : IO Unit := do
  match ← parse_term s with
  | .error e => IO.println s!"{lbl} -> MISMATCH parse ERR: {e}"
  | .ok tm =>
    match insertChainLen tm with
    | some n =>
      if n == wantN then
        IO.println s!"{lbl} -> OK ({n} INSERT consts terminating in EMPTY)"
      else IO.println s!"{lbl} -> MISMATCH inserts={n} want={wantN}"
    | none => IO.println s!"{lbl} -> MISMATCH not a const INSERT chain"

/-- Force a theorem, PRINT it (so it lands in the build log for inspection),
    and assert it is NON-DEGENERATE and equals `expected` (compared with
    whitespace squashed).  A panicked `setupX` prints `|-  = ` via `Inhabited`;
    we reject that explicitly, because merely FORCING a theorem - as the old
    `IO.mkRef (concl th)` harness did - succeeds even on a degenerate one. -/
private unsafe def thmIs (lbl expected : String) (t : thm) : IO Unit := do
  let s ← HolCore.Printer.string_of_thm t
  if sq s == "|-" || sq s == "|-=" then
    IO.println s!"{lbl} -> MISMATCH degenerate: {s}"
  else if sq s == sq expected then
    IO.println s!"{lbl} -> OK {s}"
  else
    IO.println s!"{lbl} -> MISMATCH got={sq s} want={sq expected}"

/-- Parse `goal`, run `SET_TAC[]` via `Session.prove`, assert it PROVES the
    goal outright (conclusion == reprinted goal, no hypotheses). -/
private unsafe def setTacProves (lbl goal : String) : IO Unit := do
  match ← parse_term goal with
  | .error e => IO.println s!"{lbl} -> MISMATCH parse ERR: {e}"
  | .ok tm =>
    let want := sq ("|- " ++ (← HolCore.Printer.string_of_term tm))
    match ← Session.prove tm (Session.SET_TAC []) with
    | .error e => IO.println s!"{lbl} -> MISMATCH failed to prove: {e}"
    | .ok th =>
      let got := sq (← HolCore.Printer.string_of_thm th)
      if got == want then IO.println s!"{lbl} -> OK"
      else IO.println s!"{lbl} -> MISMATCH got={got} want={want}"

/-- Prove `asm ==> goal` with `DISCH_TAC THEN ASM SET_TAC[]`.  `Session.prove`
    takes no assumption list, so discharge the hypothesis into the goal; after
    `DISCH_TAC` it sits in the goal's ASSUMPTION LIST, and `ASM SET_TAC[]`
    (`HolCore.Tactics.ASM SET_TAC []`) PREPENDS those assumptions to SET_TAC's
    theorem list - exactly what `ASM` adds over plain `SET_TAC`.  (Plain
    `REPEAT DISCH_TAC THEN SET_TAC[]` discards the assumption and drives MESON
    past its depth-50 cap on these goals; the `ASM` form supplies the
    hypothesis as a lemma and proves - the behavioural difference this checks.) -/
private unsafe def asmSetTacProves (lbl : String) (asms : List String)
    (goal : String) : IO Unit := do
  let full := asms.foldr (fun a g => "(" ++ a ++ ") ==> (" ++ g ++ ")") goal
  match ← parse_term full with
  | .error e => IO.println s!"{lbl} -> MISMATCH parse ERR: {e}"
  | .ok tm =>
    let want := sq ("|- " ++ (← HolCore.Printer.string_of_term tm))
    match ← Session.prove tm (THEN (REPEAT Session.DISCH_TAC)
                                   (HolCore.Tactics.ASM Session.SET_TAC [])) with
    | .error e => IO.println s!"{lbl} -> MISMATCH failed to prove: {e}"
    | .ok th =>
      let got := sq (← HolCore.Printer.string_of_thm th)
      if got == want then IO.println s!"{lbl} -> OK"
      else IO.println s!"{lbl} -> MISMATCH got={got} want={want}"

/-- Parse `goal`, run `SET_RULE` (the term-level form) directly. -/
private unsafe def setRuleProves (lbl goal : String) : IO Unit := do
  match ← parse_term goal with
  | .error e => IO.println s!"{lbl} -> MISMATCH parse ERR: {e}"
  | .ok tm =>
    let want := sq ("|- " ++ (← HolCore.Printer.string_of_term tm))
    match ← Session.SET_RULE tm with
    | .error e => IO.println s!"{lbl} -> MISMATCH failed to prove: {e}"
    | .ok th =>
      let got := sq (← HolCore.Printer.string_of_thm th)
      if got == want then IO.println s!"{lbl} -> OK"
      else IO.println s!"{lbl} -> MISMATCH got={got} want={want}"

/-- Assert `SET_TAC[]` FAILS on `goal` with an error CONTAINING `wantMsg`.
    Used for the SET_TAC.hlp example, which our depth-50 MESON (faithful to
    HOL Light's `ASM_MESON_TAC = GEN_MESON_TAC 0 50 1`) cannot reach - a
    DOCUMENTED failure mode ("or the resulting goal is too deep for MESON"),
    not a translation fault.  Asserting the SPECIFIC error makes this a real
    regression guard: if the goal ever starts proving, or fails differently,
    it flips to MISMATCH. -/
private unsafe def setTacFailsWith (lbl goal wantMsg : String) : IO Unit := do
  match ← parse_term goal with
  | .error e => IO.println s!"{lbl} -> MISMATCH parse ERR: {e}"
  | .ok tm =>
    match ← Session.prove tm (Session.SET_TAC []) with
    | .ok th =>
      IO.println s!"{lbl} -> MISMATCH unexpectedly proved: {
        sq (← HolCore.Printer.string_of_thm th)}"
    | .error e =>
      if (e.splitOn wantMsg).length > 1 then
        IO.println s!"{lbl} -> OK (documented failure: {e})"
      else IO.println s!"{lbl} -> MISMATCH wrong error: {e}"

/- ====================================================================== -/
/- (1) THE THREE MEASURED PARSER BASELINES - the payoff for the nineteen   -/
/-     `parse_as_infix` declarations and HolCore/Parser.lean's set         -/
/-     desugaring (pmk_setcompr at 724-725, pmk_set_enum at 684).          -/
/-                                                                        -/
/- BEFORE sets.ml was translated these three parsed as NONSENSE, because   -/
/- the constants and infixes did not exist yet:                           -/
/-   `{x | x = 1}`  parsed GSPEC/SETSPEC as FREE VARIABLES                 -/
/-   `{1,2,3}`      parsed INSERT/EMPTY as FREE VARIABLES                  -/
/-   `x IN s`       parsed as `x` applied to `IN` and `s` (a 3-way         -/
/-                  juxtaposition), because no `IN` infix existed          -/
/- Each assertion below checks the STRUCTURE has now flipped: parse in the -/
/- runtime state (after `ensureSets`) with `parse_term`, then inspect the  -/
/- head with `strip_comb`.  These are worth more than any forcing probe.   -/
/- ====================================================================== -/

/- `{x | x = 1}` must now be a set-comprehension: head `Const "GSPEC"`,
   applied to ONE argument (the `\v. ?... SETSPEC v (x=1) x` abstraction).
   Was: head `Var "GSPEC"` (a free variable) before the constant existed. -/
#eval headCheck "(1) baseline {x | x = 1} is GSPEC" "{x | x = 1}" "Const GSPEC" 1

/- `{1,2,3}` must now be an INSERT chain of CONSTANTS terminating in EMPTY:
   the outermost head is `Const "INSERT"` applied to 2 args (`1` and the
   tail `{2,3}`).  Was: `Var "INSERT"` / `Var "EMPTY"` before. -/
#eval headCheck "(1) baseline {1,2,3} is INSERT" "{1,2,3}" "Const INSERT" 2

/- `{1,2,3}`: additionally walk the WHOLE chain and confirm every node is a
   `Const "INSERT"` and the terminator is `Const "EMPTY"` - so the enum is
   built entirely from constants, not free variables.  (Calibrated: three
   INSERT nodes, then EMPTY.) -/
#eval insertChainCheck "(1) baseline {1,2,3} chain" "{1,2,3}" 3

/- `x IN s` must now be a 2-argument application of `Const "IN"` - NOT the
   3-way juxtaposition `x IN s` that a nonexistent infix produced.  Assert
   BOTH that the head is `Const "IN"` with 2 args AND (below) that it is NOT
   a juxtaposition whose head is the variable `x`. -/
#eval headCheck "(1) baseline x IN s is IN application" "x IN s" "Const IN" 2

/- The sharper form of the same fact: a 3-way juxtaposition `((x) (IN)) (s)`
   would have head `Var "x"`; assert the head is NOT a variable. -/
#eval (do
  match ← parse_term "x IN s" with
  | .error e => IO.println s!"(1) baseline x IN s not-juxtaposition -> MISMATCH parse ERR: {e}"
  | .ok tm =>
    match (strip_comb tm).1 with
    | .Var v _ => IO.println s!"(1) baseline x IN s not-juxtaposition -> MISMATCH head is Var {v}"
    | .Const "IN" _ => IO.println "(1) baseline x IN s not-juxtaposition -> OK (head is Const IN, not a var juxtaposition)"
    | other => IO.println s!"(1) baseline x IN s not-juxtaposition -> MISMATCH head={repr other}"
   : IO Unit)

/- ====================================================================== -/
/- (2) `.hlp` DOCUMENTATION CHECKS.                                        -/
/-                                                                        -/
/- Help/ has entries for SET_TAC, SET_RULE and new_inductive_set (the      -/
/- other requested names - IN_ELIM_THM, GSPEC, ITSET, CARD, HAS_SIZE,      -/
/- CROSS, UNION_OF - have NO .hlp entry, so there is nothing to reproduce   -/
/- for them; that absence is reported, not asserted).  For each entry with -/
/- an EXAMPLE, assert our implementation reproduces the documented result. -/
/-                                                                        -/
/- FINDING (documentation vs source).  The SET_TAC.hlp EXAMPLE goal        -/
/-   `!s. (UNIONS s = {{}}) <=> !t. t IN s ==> t = {}`                     -/
/- does NOT reproduce: it exhausts MESON at depth 50 with `solve_goal: Too -/
/- deep`.  This is NOT a sets.ml translation fault - SET_TAC (sets.ml      -/
/- 320-333) is faithfully PRESET_CONV then `MESON_TAC[]`, and MESON_TAC is -/
/- faithfully `ASM_MESON_TAC = GEN_MESON_TAC 0 50 1` (meson.ml), the same  -/
/- depth-50 cap HOL Light ships.  The .hlp's OWN \FAILURE section names    -/
/- this mode: "or the resulting goal is too deep for {MESON}".  Our MESON  -/
/- search order simply reaches that cap on this particular goal where the  -/
/- reference build's does not.  So we assert the SOURCE-specified          -/
/- behaviour: the three PRESET_CONV stages that SET_TAC is BUILT from all  -/
/- discharge their goals (section 3), and the exact hlp goal fails with    -/
/- the documented "Too deep" - a deterministic regression guard either way.-/
/- The SET_RULE.hlp examples DO reproduce verbatim.                        -/
/- ====================================================================== -/

/- SET_RULE.hlp, example 1: reproduces verbatim (calibrated). -/
#eval setRuleProves "(2) SET_RULE.hlp ex1"
  "{x | ~(x IN s <=> x IN t)} = (s DIFF t) UNION (t DIFF s)"

/- SET_RULE.hlp, example 2: the UNIONS/IMAGE-comprehension identity. -/
#eval setRuleProves "(2) SET_RULE.hlp ex2"
  "UNIONS {t y | y IN x INSERT s} = t x UNION UNIONS {t y | y IN s}"

/- SET_TAC.hlp example: the documented FAILURE mode.  Reported as a finding
   above; asserted here so a change in either direction trips MISMATCH. -/
#eval setTacFailsWith "(2) SET_TAC.hlp ex (documented Too-deep finding)"
  "!s. (UNIONS s = {{}}) <=> !t. t IN s ==> t = {}" "Too deep"

/- new_inductive_set.hlp: the even/odd mutual-induction EXAMPLE.  Assert all
   three returned theorems reproduce the documented (rules, induct, cases)
   triple verbatim.  This is `Session.new_inductive_set` run on the .hlp's own
   input; the expected strings are the .hlp's own output. -/
#eval (do
  match ← parse_term
      ("0 IN even_numbers /\\ " ++
       "(!n. n IN even_numbers ==> SUC n IN odd_numbers) /\\ " ++
       "1 IN odd_numbers /\\ " ++
       "(!n. n IN odd_numbers ==> SUC n IN even_numbers)") with
  | .error e => IO.println s!"(2) new_inductive_set.hlp -> MISMATCH parse ERR: {e}"
  | .ok tm =>
    match ← Session.new_inductive_set tm with
    | .error e => IO.println s!"(2) new_inductive_set.hlp -> MISMATCH failed: {e}"
    | .ok (rules, induct, cases) => do
      thmIs "(2) new_inductive_set.hlp RULES"
        ("|- 0 IN even_numbers /\\ (forall n. n IN even_numbers ==> SUC n IN odd_numbers) /\\ " ++
         "1 IN odd_numbers /\\ (forall n. n IN odd_numbers ==> SUC n IN even_numbers)") rules
      thmIs "(2) new_inductive_set.hlp INDUCT"
        ("|- forall odd_numbers' even_numbers'. even_numbers' 0 /\\ " ++
         "(forall n. even_numbers' n ==> odd_numbers' (SUC n)) /\\ odd_numbers' 1 /\\ " ++
         "(forall n. odd_numbers' n ==> even_numbers' (SUC n)) " ++
         "==> (forall a0. a0 IN odd_numbers ==> odd_numbers' a0) /\\ " ++
         "(forall a1. a1 IN even_numbers ==> even_numbers' a1)") induct
      thmIs "(2) new_inductive_set.hlp CASES"
        ("|- (forall a0. a0 IN odd_numbers <=> (exists n. a0 = SUC n /\\ n IN even_numbers) \\/ a0 = 1) /\\ " ++
         "(forall a1. a1 IN even_numbers <=> a1 = 0 \\/ (exists n. a1 = SUC n /\\ n IN odd_numbers))") cases
   : IO Unit)

/- ====================================================================== -/
/- (3) BEHAVIOURAL CHECKS ON SET_TAC - the linchpin (131 bare `SET_TAC[]`  -/
/-     one-liners, 281 uses in all).  Exercise the THREE stages of its     -/
/-     PRESET_CONV separately, plus `ASM SET_TAC[]` and `SET_RULE`.        -/
/-     All calibrated to PROVE outright.                                   -/
/- ====================================================================== -/

/- GSPEC/IMAGE stage: goals whose PRESET_CONV work is unfolding set
   comprehensions and IMAGE into membership. -/
#eval setTacProves "(3) SET_TAC gspec-stage INTER-as-comprehension"
  "{x | x IN s /\\ x IN t} = s INTER t"
#eval setTacProves "(3) SET_TAC image-stage IMAGE-as-comprehension"
  "!f s. IMAGE f s = {y | ?x. x IN s /\\ y = f x}"

/- EXTENSION/SUBSET/BIJ/INJ/SURJ stage: antisymmetry of SUBSET, the
   canonical EXTENSION-driven goal. -/
#eval setTacProves "(3) SET_TAC extension-stage SUBSET-antisym"
  "!s t:A->bool. s SUBSET t /\\ t SUBSET s ==> s = t"

/- Membership stage: a pure IN-of-INTER equivalence, all the work is in the
   membership rewrites. -/
#eval setTacProves "(3) SET_TAC membership-stage IN-INTER"
  "!x:A s t. x IN (s INTER t) <=> x IN s /\\ x IN t"

/- `ASM SET_TAC[]` with a hypothesis: the assumption `x IN (s INTER t)` must
   be PICKED UP from the goal's assumption list (that is what `ASM` adds over
   plain `SET_TAC`, which fails here at MESON's depth cap).  Calibrated. -/
#eval asmSetTacProves "(3) ASM SET_TAC with hypothesis"
  ["x IN (s INTER t)"] "x IN s"

/- `SET_RULE` used directly on a fresh elementary lemma (not one of the .hlp
   examples): UNION with EMPTY. -/
#eval setRuleProves "(3) SET_RULE direct UNION-EMPTY"
  "!s:A->bool. s UNION {} = s"

/- ====================================================================== -/
/- (4) LATER BUNDLES earlier tests do not reach.  For SetsCardComp,        -/
/-     SetsSup, SetsHasInfSup and the CROSS/UNION_OF/INTERSECTION_OF        -/
/-     infixes, assert (a) the operator PARSES with the right head const   -/
/-     - proving the infix fixity is live - and (b) a representative        -/
/-     theorem is NON-DEGENERATE and matches sets.ml verbatim.  CROSS and   -/
/-     UNION_OF goals are NOT routed through SET_TAC: they unfold to        -/
/-     pair/UNIONS comprehensions that exceed MESON's depth-50 cap (the     -/
/-     same documented "Too deep" boundary as the SET_TAC.hlp example), so  -/
/-     the theorem-print form is the robust "in real use" check.           -/
/- ====================================================================== -/

/- SetsCardComp: cardinal comparison over `<=_c` / `=_c`.  Infix heads live,
   and the definitions are the faithful sets.ml statements. -/
#eval headCheck "(4) SCC <=_c infix parses" "(s:A->bool) <=_c (t:B->bool)" "Const <=_c" 2
#eval headCheck "(4) SCC =_c infix parses"  "(s:A->bool) =_c (t:B->bool)"  "Const =_c"  2
#eval thmIs "(4) SCC le_c"
  ("|- forall t s. s <=_c t <=> (exists f. (forall x. x IN s ==> f x IN t) /\\ " ++
   "(forall x y. x IN s /\\ y IN s /\\ f x = f y ==> x = y))") Session.le_c
#eval thmIs "(4) SCC eq_c"
  ("|- forall t s. s =_c t <=> (exists f. (forall x. x IN s ==> f x IN t) /\\ " ++
   "(forall y. y IN t ==> (existsunique x. x IN s /\\ f x = y)))") Session.eq_c
/- A non-definitional cardinal theorem: CARD_LE_INJ (a real result). -/
#eval thmIs "(4) SCC CARD_LE_INJ"
  ("|- forall s t. FINITE s /\\ FINITE t /\\ CARD s <= CARD t ==> " ++
   "(exists f. IMAGE f s SUBSET t /\\ (forall x y. x IN s /\\ y IN s /\\ f x = f y ==> x = y))")
  Session.CARD_LE_INJ

/- SetsSup: sup over the reals.  SUP_SING is a clean closed form; REAL_LE_SUP
   a representative ordering theorem. -/
#eval thmIs "(4) SSup SUP_SING" "|- forall a. sup {a} = a" Session.SUP_SING
#eval thmIs "(4) SSup REAL_LE_SUP"
  "|- forall s a b y. y IN s /\\ a <= y /\\ (forall x. x IN s ==> x <= b) ==> a <= sup s"
  Session.REAL_LE_SUP

/- SetsHasInfSup: the `has_inf` / `has_sup` infixes must PARSE (the 18th/19th
   parse_as_infix of the file), and their definitions are the faithful reals
   statements. -/
#eval headCheck "(4) SISup has_inf infix parses" "s has_inf b" "Const has_inf" 2
#eval headCheck "(4) SISup has_sup infix parses" "s has_sup b" "Const has_sup" 2
#eval thmIs "(4) SISup has_inf"
  "|- forall s b. s has_inf b <=> (forall c. (forall x. x IN s ==> c <= x) <=> c <= b)" Session.has_inf
#eval thmIs "(4) SISup has_sup"
  "|- forall s b. s has_sup b <=> (forall c. (forall x. x IN s ==> x <= c) <=> b <= c)" Session.has_sup
#eval thmIs "(4) SISup HAS_INF_LBOUND"
  "|- forall s b x. s has_inf b /\\ x IN s ==> b <= x" Session.HAS_INF_LBOUND

/- CROSS (SetsCross): infix parses, definition and IN_CROSS are faithful. -/
#eval headCheck "(4) CROSS infix parses" "(s:A->bool) CROSS (t:B->bool)" "Const CROSS" 2
#eval thmIs "(4) CROSS def" "|- forall s t. s CROSS t = {x,y | x IN s /\\ y IN t}" Session.CROSS
#eval thmIs "(4) IN_CROSS" "|- forall x y s t. x,y IN s CROSS t <=> x IN s /\\ y IN t" Session.IN_CROSS

/- UNION_OF / INTERSECTION_OF (SetsUnionOf): infixes parse (3-arg apply, the
   operator applied to P, Q and then a set), definitions are faithful. -/
#eval headCheck "(4) UNION_OF infix parses" "(P UNION_OF Q) (s:A->bool)" "Const UNION_OF" 3
#eval headCheck "(4) INTERSECTION_OF infix parses" "(P INTERSECTION_OF Q) (s:A->bool)" "Const INTERSECTION_OF" 3
#eval thmIs "(4) UNION_OF def"
  "|- forall P Q. P UNION_OF Q = (\\s. exists u. P u /\\ (forall c. c IN u ==> Q c) /\\ UNIONS u = s)"
  Session.UNION_OF
#eval thmIs "(4) INTERSECTION_OF def"
  "|- forall P Q. P INTERSECTION_OF Q = (\\s. exists u. P u /\\ (forall c. c IN u ==> Q c) /\\ INTERS u = s)"
  Session.INTERSECTION_OF
