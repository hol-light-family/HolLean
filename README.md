# HOL-Lean (a port of HOL Light to Lean 4) v 0.02 #

HOL Light can be found here: https://hol-light.github.io/

This directory contains a port of the HOL Light theorem prover to Lean 4.  It translates everything HOL Light's `hol.ml` loads: the kernel, the core proof infrastructure, the mathematical theories, and the online help.  It also translates HOL Light's `Library/` (every file except `tactician_light.ml`) and the files of `Tutorial/`, `Examples/`, `Logic/` and `Arithmetic/` whose dependencies are translated.  From `Multivariate/` it translates `misc.ml`, `vectors.ml`, `msum.ml`, `determinants.ml`, `clifford.ml`, `metric.ml`, `topology.ml`, `homology.ml`, `specialtopologies.ml`, `convex.ml`, `complexes.ml`, `cross.ml`, `tarski.ml`, `wlog.ml`, `wlog_examples.ml`, `cvectors.ml`, `paths.ml`, `paracompact.ml`, `polytope.ml`, `degree.ml`, `derivatives.ml`, `integration.ml`, `measure.ml`, `canal.ml`, `transcendentals.ml`, `realanalysis.ml`, `geom.ml`, `lpspaces.ml`, `moretop.ml`, `cauchy.ml`, `gamma.ml` and `flyspeck.ml`; the rest of `Multivariate/` is not yet translated.  The focus is on accuracy of the translation from OCaml, and no work has been done on optimizing the performance of the code.

HOL Light is written in Objective Caml (OCaml), which is a dialect of the ML language known for high-performance.  The purpose of this port is to leverage the Lean 4 language, which is a strict pure functional language that can be viewed as a spiritual successor to ML.  Note that this port uses Lean 4 only as the meta-language for the HOL Lean prover – it does not use dependent types or the theorem proving capabilities of Lean.

The reason for this port is that there are distinct advantages of LCF-style theorem provers over dependent types.  This port blends the best of both worlds, i.e. theorem proving is done using the simple but powerful HOL Light core, while the meta-language for proofs and tactics can use the full features of the Lean 4 language.

The kernel (fusion.ml) was translated by hand to ensure high accuracy, and the remainder of the HOL Light system was translated interactively using Kiro CLI with Claude Opus 5.5.  Lean 4 has many similarities to OCaml and it was possible to faithfully translate most aspects of HOL Light. However, there are two important differences:

1. Lean 4 is a pure functional language meaning that the read-eval-print loop (REPL), mutable data, and exceptions are done via the IO Monad.  Exception handling was particularly cumbersome to translate due to the .ok/.error matching that would prevent HOL definitions from composing cleanly.  Failures keep HOL Light's own messages.
1. The parser is integrated with Lean '#eval' statements.  This required some changes to the HOL Light syntax, most notably HOL expressions must now be enclosed in '[[' and ']]', rather than backquotes.  Turning a quotation into a term runs the parser, an `IO` action, so it needs a small amount of unsafe code; it is kept to a few functions (see Layout below).

## Getting started ##

The port is designed to be used interactively within VS Code with the Lean plugin.  To get started, open the file Prove.lean and start typing, e.g:

`#eval prove ([[ p \/ p ==> p ]]) (DISCH_THEN (DISJ_CASES_THEN2 ACCEPT_TAC ACCEPT_TAC))`

The output will be shown in the Lean InfoView window, in this case:

`|- p \/ p ==> p`

Prove.lean imports `Session`, which loads the whole library in the same order as HOL Light's `hol_lib.ml`.  This takes about 20 seconds each time the file is opened, because the theorems are proved when the library loads, as in HOL Light.  Prove.lean can also be run from the command line with `make prove` or `lake lean Prove.lean`.  Use `lake lean`, not `lake env lean`: only `lake lean` (and the VS Code extension) loads the compiled native code, and without it the load takes about 5 minutes.  `make prove` also shows the messages printed while loading (they are not shown when loading in VS Code).  By default it uses level 2: HOL Light's verbose messages during the load, about 250,000 lines.  `make prove SHOW_LOAD=1` shows only HOL Light's default messages (about 5,000 lines).  With `lake lean`, set `HOLLEAN_SHOW_LOAD=1` or `2`.  These switches are off by default, as in HOL Light; set them yourself with, for example, `#eval copverb.set true`.

A few things to know:

* Parenthesise a quotation when it is not the last argument: `prove ([[...]]) tac` works, `prove [[...]] tac` does not parse.
* As in HOL Light, after loading, a variable with no type information defaults to a natural number.  Write `[[!x y:real. ...]]` for real numbers; `&n`, `abs` and `max` already make a term real.
* To keep a result under a name, as HOL Light's `let th = NUM_REDUCE_CONV `2 + 2 * 3`;;`, define it: `def th : thm := NUM_REDUCE_CONV [[2 + 2 * 3]]`.  Later commands can use `th`; a failure is reported with HOL Light's message.
* HOL Light's online help is available as `#eval help("NAME")`, e.g. `#eval help("REAL_ARITH")`; an unknown name lists the closest entries, though note that the help uses HOL Light syntax and not the new Lean syntax.
* `#eval Help.search [Help.name "ADD"]` searches the theorem database, like HOL Light's `search [name "ADD"]`.  It needs `import Database` (Prove.lean imports only `Help`, so add it there).
* Interactive proofs use HOL Light's subgoal package, and each command prints the goalstack:

```
#eval g ([[x + 1 = 1 + x /\ 1 + 1 = 2]])
#eval e CONJ_TAC
#eval e ARITH_TAC
```

`b`, `r n`, `p`, `er`, `set_goal`, `top_thm` and `flush_goalstack` are available too.

See the HolTest directory for further examples of HOL Lean code.

## Layout ##

| Path | Contents |
|---|---|
| `HolCore/` | the kernel and core proof infrastructure (fusion.ml to impconv.ml) |
| `HolMath/` | the mathematical theories (pair.ml to define.ml) |
| `SessionCore/`, `SessionMath/` | the session state: one module per HolCore file with load-time state (bool.ml to impconv.ml) and one per HolMath file (pair.ml to define.ml), each building its file's theorems when it is imported, and the names HOL Light users type |
| `Session.lean` | imports SessionCore and SessionMath, so importing it loads the whole library, in `hol_lib.ml` order |
| `HolToplevel.lean` | helpers for the translated toplevel sessions (OCaml's `let x = e;;` evaluated once, values kept between `#eval`s) |
| `HolLibrary/` | files from HOL Light's `Library/` (so far `prime.ml`, `floor.ml`, `components.ml`, `records.ml`, `bdd.ml`, `words.ml`, `analysis.ml`, `rstc.ml`, `transc.ml`, `wo.ml`, `card.ml`, `bitmatch.ml`, `products.ml`, `agm.ml`, `iter.ml`, `bitsize.ml`, `binary.ml`, `isum.ml`, `frag.ml`, `binomial.ml`, `pocklington.ml`, `ringtheory.ml`, `integer.ml`, `multiplicative.ml`, `primitive.ml`, `pratt.ml`, `poly.ml`, `matroids.ml`, `calc_real.ml`, `permutations.ml`, `jacobi.ml`, `word_automata.ml`, `q.ml`, `fieldtheory.ml`, `grouptheory.ml`, `modmul_group.ml`, `symmetric_group.ml`, `ring_det.ml`, `ring_groups.ml`, `galois.ml`, `finite_fields.ml` and `cyclotomic.ml`: every Library file except `tactician_light.ml`, a tool that runs tactics given as OCaml source and so has no Lean counterpart), pure like HolMath |
| `SessionLibrary/` | connects `HolLibrary` to Session and exports its theorems by name; importing a module loads its Library file |
| `HolMultiLib/` | files from HOL Light's `Multivariate/`: `misc.ml`, `vectors.ml`, `msum.ml`, `determinants.ml`, `clifford.ml`, `metric.ml`, `topology.ml`, `homology.ml`, `specialtopologies.ml`, `convex.ml`, `complexes.ml`, `cross.ml`, `tarski.ml`, `wlog.ml`, `wlog_examples.ml`, `cvectors.ml`, `paths.ml`, `paracompact.ml`, `polytope.ml`, `degree.ml`, `derivatives.ml`, `integration.ml`, `measure.ml`, `canal.ml`, `transcendentals.ml`, `realanalysis.ml`, `geom.ml`, `lpspaces.ml`, `moretop.ml`, `cauchy.ml`, `gamma.ml` and `flyspeck.ml` (pure, like HolLibrary) |
| `SessionMultiLib/` | connects `HolMultiLib` to Session and exports its theorems, conversions and tactics by name; importing a module loads its Multivariate file and the files it needs |
| `Help.lean`, `Database.lean`, `Help/` | help.ml, database.ml and HOL Light's help files |
| `HolTest/` | the test suite (about 3,850 checks), including the examples from HOL Light's help files and its UnitTests; built only by `make test` and `make check` |
| `Hol.lean` | the `hollean` executable (`hol.ml`); it does not import the tests |
| `HolTrace/`, `HolTrace.lean` | the `holtrace` executable: a proof reconstructor for [HOLTrace](https://holtrace.cr.yp.to) files (see `HolTrace/README.md`) |
| `SessionMultiLib/MultivariateDatabase.lean` | `Multivariate/multivariate_database.ml`: the same for `make.ml`'s files (17,529 theorems) |
| `SessionMultiLib/ComplexDatabase.lean` | `Multivariate/complex_database.ml`: importing it loads the files `make_complex.ml` loads and makes `search` see all 20,954 of their theorems |
| `HolTutorial/` | translations of HOL Light's Tutorial/ files, one toplevel session each in Prove.lean style (built by `make tutorial` and `make check`); Vectors.ml (it needs Examples/sos.ml and Rqe/) and the two files that load it are not translated yet |
| `HolExamples/` | translations of 45 files of HOL Light's Examples/ (those whose dependencies are translated, except sos.ml, which needs the external solver csdp), in the same style (built by `make examples` and `make check`; BitBlast takes about 10 minutes) |
| `Hol100/` | translations of 64 of the 68 files of HOL Light's 100/ (proofs from the "top 100 theorems" list), in the same style; not translated: buffon.ml (needs Probability/), ceva.ml and thales.ml (REAL_SOS, which needs csdp) and cubic.ml (needs Complex/complex_transc.ml) (built by `make hundred` and `make check`; Transcendence takes about an hour) |
| `HolLogicArith/` | translations of HOL Light's Logic/ (18 files) and Arithmetic/ (8 files; its fol.ml is `ArithFol`), in the same style; each module imports the files its make.ml loads before it (built by `make logic` and `make check`) |
| `Prove.lean` | your scratchpad |
| `VERYQUICK_REFERENCE.txt`, `QUICK_REFERENCE.txt` | HOL Light's two quick-reference sheets, converted to HolLean's syntax and names, with notes where HolLean differs |

HolCore, HolMath, HolLibrary and HolMultiLib contain no `unsafe` code and no `sorry`; the build checks this.  Session's layers are built by `initialize` when it is imported, and everything built on it (SessionLibrary, SessionMultiLib, the translations, your own files) is ordinary safe code.  The only `unsafe` code is a few functions that turn an `IO` action into a value, each behind a safe `implemented_by` declaration: in `SessionCore/Base.lean` (quotations and printing), `SessionMath/Sets.lean` (one rule) and `HolToplevel.lean`; and some helpers in the test suite.

To use a `Library/` file, import its `SessionLibrary` module; importing it is the equivalent of HOL Light `needs`, and loads the files it needs too:

```lean
import SessionLibrary.Prime             -- needs "Library/prime.ml"
open Session SessionLibrary.Prime
#eval PRIME_DIVPROD
#eval GCD_CONV [[gcd(12,18)]]
```

The modules are named after the files: `prime.ml` is `SessionLibrary.Prime`, `floor.ml` `Floor`, `components.ml` `Components`, `records.ml` `Records`, `bdd.ml` `BDD`, `words.ml` `Words`, `analysis.ml` `Analysis`, `rstc.ml` `RSTC`, `transc.ml` `Transc`, `wo.ml` `Wo`, `card.ml` `Card`, `bitmatch.ml` `BitMatch`, `products.ml` `Products`, `agm.ml` `Agm`, `iter.ml` `Iter`, `bitsize.ml` `Bitsize`, `binary.ml` `Binary`, `isum.ml` `Isum`, `frag.ml` `Frag`, `binomial.ml` `Binomial`, `pocklington.ml` `Pocklington`, `ringtheory.ml` `RingTheory`, `integer.ml` `Integer`, `multiplicative.ml` `Multiplicative`, `primitive.ml` `Primitive`, `pratt.ml` `Pratt`, `poly.ml` `Poly`, `matroids.ml` `Matroids`, `calc_real.ml` `CalcReal`, `permutations.ml` `Permutations`, `jacobi.ml` `Jacobi`, `word_automata.ml` `WordAutomata`, `q.ml` `Q` (module Pa: `SessionLibrary.Q.Pa`), `fieldtheory.ml` `FieldTheory`, `grouptheory.ml` `GroupTheory`, `modmul_group.ml` `ModmulGroup`, `symmetric_group.ml` `SymmetricGroup`, `ring_det.ml` `RingDet`, `ring_groups.ml` `RingGroups`, `galois.ml` `Galois`, `finite_fields.ml` `FiniteFields` and `cyclotomic.ml` `Cyclotomic`.

As in HOL Light, not every combination of library files can be loaded into one session: loading `analysis.ml`, then `rstc.ml`, then `transc.ml` fails (with `EQT_ELIM`) in both.  So there is no module that imports them all; import the ones you need.

The translated `Multivariate/` files work the same way, through `SessionMultiLib`: `misc.ml` is `SessionMultiLib.Misc`, `vectors.ml` `Vectors`, `msum.ml` `MSum`, `determinants.ml` `Determinants`, `clifford.ml` `Clifford`, `metric.ml` `Metric`, `topology.ml` `Topology`, `homology.ml` `Homology`, `specialtopologies.ml` `SpecialTopologies`, `convex.ml` `Convex`, `complexes.ml` `Complexes`, `cross.ml` `Cross`, `tarski.ml` `Tarski`, `wlog.ml` `Wlog`, `wlog_examples.ml` `WlogExamples`, `cvectors.ml` `CVectors`, `paths.ml` `Paths`, `paracompact.ml` `Paracompact`, `polytope.ml` `Polytope`, `degree.ml` `Degree`, `derivatives.ml` `Derivatives`, `integration.ml` `Integration`, `measure.ml` `Measure`, `canal.ml` `Canal`, `transcendentals.ml` `Transcendentals`, `realanalysis.ml` `RealAnalysis`, `geom.ml` `Geom`, `lpspaces.ml` `LpSpaces`, `moretop.ml` `MoreTop`, `cauchy.ml` `Cauchy`, `gamma.ml` `Gamma` and `flyspeck.ml` `Flyspeck`.  Importing `SessionMultiLib.Determinants` loads vectors.ml and misc.ml first, and the Library files they need:

```lean
import SessionMultiLib.Determinants     -- needs "Multivariate/determinants.ml"
open Session HolLight.Syntax SessionMultiLib.Vectors SessionMultiLib.Determinants
#eval DET_MUL
#eval prove ([[ !a b:real^N. dist(a,b) = dist(b,a) ]])
    (GEOM_ORIGIN_TAC ([[ a:real^N ]]) THEN REWRITE_TAC [DIST_SYM])
```

`pratt.ml` (like HOL Light) calls PARI/GP's `gp` to factor numbers while it loads, so it needs `gp` on the `PATH`; without it, loading fails with HOL Light's message "factor: Call to GP/PARI failed".

Each library name is exported under its HOL Light name.  Where a library rebinds a name that Session (or a library it needs) already has, qualify it: `transc.ml` rebinds `DIVISION_0`, `REAL_DIV_SQRT`, `SQRT_EVEN_POW2` and `SUM_DIFFS` from the core and `SYM_CANON_CONV` and `EXT_CONV` from `analysis.ml`, so write `SessionLibrary.Transc.SUM_DIFFS` for transc's version.  `isum.ml` rebinds `INT_OF_REAL_THM` (a stronger version of int.ml's rule); use `SessionLibrary.Isum.INT_OF_REAL_THM` for isum.ml's.  `pocklington.ml` rebinds lib.ml's `num_0`, `num_1` and `num_2` (same values; `HolCore.Lib.num_0` is the core one).

HolMath and `HolLibrary/Prime.lean` are translated by hand and read much like the OCaml: `HolMath/Base.lean` provides HOL Light's tactics, rules and conversions under their own names, with infix `THEN`, `THENL`, `ORELSE`, `THENC`, `ORELSEC` and `o`.

## Building and testing ##

You need Lean 4 (installed with `elan`; the version is fixed in `lean-toolchain`).  The main make targets:

* `make build` builds everything except the tests: the `hollean` executable and HOL Light's Library/ and Multivariate/ files.  A build from scratch takes a while, mostly compiling to C.
* `make test` builds and runs the tests (the HolTest library; nothing else imports them) and prints assertion counts per module.  There is no output until the build finishes.
* `make verify` checks the build log for errors, warnings, failed tests, panics, and `unsafe` or `sorry` in the pure libraries, and runs `checks/InitGate.lean`, which rejects any `initialize` of function type (Lean never runs such an initialiser in compiled code).
* `make check` does a clean build of everything, including the tests and the translations, followed by `make verify`.  From scratch it takes about five hours on the author's machine (about two and a half without the Hol100 translations).  It first builds the wiring libraries (SessionLibrary, SessionMultiLib) with `HOLLEAN_REPLAY=0`, so that compiling them does not re-prove the library files they import; the proofs run when the tests and translations are compiled.
* `make tutorial` builds the tutorial translations (HolTutorial), printing each session's output; `make examples`, `make logic` and `make hundred` do the same for HolExamples, HolLogicArith and Hol100.
* `make help` lists the other targets.

GitHub Actions runs `make core` on pushes to main and on pull requests (`.github/workflows/ci.yml`).

By default HolCore, HolMath and the executable are compiled to native code at `-O3`, and HolLibrary and the session libraries (SessionCore, SessionMath, Session, HolToplevel) at `-O0`: their generated C is mostly one-off set-up code, and HolLibrary's is very large (RingTheory's is 117 MB), so at `-O0` it compiles in minutes rather than an hour.  SessionLibrary is not compiled to native code.  `make build-O3`, `make test-O3` and `make check-O3` compile everything at `-O3`, and `OPT=N` compiles everything at `-ON` for any target (for example `make test OPT=1`).  Each `OPT=N` build has its own directory, `.lake/build-ON`.

## Known differences from HOL Light ##

* `dest_small_numeral` does not fail on numbers too large for an OCaml `int`.
* Some long terms are broken across lines differently.
* When types are printed, a pair is printed with a space after the comma, `((a:A), (b:A))`, where HOL Light prints `((a:A),(b:A))`.
* By default, results that come from HOL Light's hash-based lookup tables (for example `atoms`) can come out in a different order.  Setting the environment variable `HOLLEAN_OCAML_HASH` makes them use OCaml's hash and match HOL Light's order.
* `ORELSE_TCL` and `REPEAT_TCL` also catch a failure of the following tactic.
* OCaml's physical equality `==` is translated as structural equality, because pointer comparison needs `unsafe` code.  Results are the same, but a test of whether two values are the same object gives `true` for equal copies: in `qmap`'s help example, `map I million == million` is `true`, not `false`.
* `SessionLibrary.Analysis` exports every name `Library/analysis.ml` defines under its HOL Light name.  About 100 of them, such as `REAL_LE_TRANS`, `SUM_LE`, `sum` and `EXPAND_TAC`, are also names in `Session`, where they refer to the core versions.  With both namespaces open, write `SessionLibrary.Analysis.SUM_LE` or `Session.SUM_LE`.  In HOL Light the later binding simply shadows the earlier one.
* Names that are not valid in Lean are changed: `omit` is written `«omit»`, and `WF_REC_CASES'` is `WF_REC_CASES_prime`.
* HOL Light redefines a few functions, each later definition replacing the earlier: `GEN_REAL_ARITH` and `REAL_ARITH` (twice in realarith.ml, then calc_rat.ml), `REAL_ARITH_TAC` (real.ml, then calc_rat.ml), and `INT_ARITH`, `INT_ARITH_TAC`, `ASM_INT_ARITH_TAC`, `INTEGER_RULE` and `INTEGER_TAC` (twice in int.ml).  Here the plain name is always the final version, the one HOL Light's users get.  The earlier versions stay available under numbered names (`REAL_ARITH1`, `REAL_ARITH2`, `REAL_ARITH_TAC1`, `INT_ARITH1`, ...), and the final versions also have numbered names (`REAL_ARITH3`, `REAL_ARITH_TAC2`, `INT_ARITH2`, ...).

Please let me know how you get on, and if you find any issues.

Chris
# HolLean
