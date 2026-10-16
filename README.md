# HOL-Lean (a port of HOL Light to Lean 4) v 0.02 #

HOL Light can be found here: https://hol-light.github.io/

This directory contains a port of the HOL Light theorem prover to Lean 4.  It translates everything HOL Light's `hol.ml` loads: the kernel, the core proof infrastructure, the mathematical theories, and the online help.  HOL Light's `Library/` and `Multivariate/` directories are not yet translated.  The focus is on accuracy of the translation from OCaml, and no work has been done on optimizing the performance of the code.

HOL Light is written in Objective Caml (OCaml), which is a dialect of the ML language known for high-performance.  The purpose of this port is to leverage the Lean 4 language, which is a strict pure functional language that can be viewed as a spiritual successor to ML.  Note that this port uses Lean 4 only as the meta-language for the HOL Lean prover – it does not use dependent types or the theorem proving capabilities of Lean.

The reason for this port is that there are distinct advantages of LCF-style theorem provers over dependent types.  This port blends the best of both worlds, i.e. theorem proving is done using the simple but powerful HOL Light core, while the meta-language for proofs and tactics can use the full features of the Lean 4 language.

The kernel (fusion.ml) was translated by hand to ensure high accuracy, and the remainder of the HOL Light system was translated interactively using Kiro CLI with Claude Opus 5.5.  Lean 4 has many similarities to OCaml and it was possible to faithfully translate most aspects of HOL Light. However, there are two important differences:

1. Lean 4 is a pure functional language meaning that the read-eval-print loop (REPL), mutable data, and exceptions are done via the IO Monad.  Exception handling was particularly cumbersome to translate due to the .ok/.error matching that would prevent HOL definitions from composing cleanly.  Failures keep HOL Light's own messages.
1. The parser requires some unsafe code to enable direct integration with Lean '#eval' statements.  This required some changes to the HOL Light syntax, most notably HOL expressions must now be enclosed in '[[' and ']]', rather than backquotes.  The unsafe code is kept out of the translated libraries (see Layout below).

## Getting started ##

The port is designed to be used interactively within VS Code with the Lean plugin.  To get started, open the file Prove.lean and start typing, e.g:

`#eval prove ([[ p \/ p ==> p ]]) (DISCH_THEN (DISJ_CASES_THEN2 ACCEPT_TAC ACCEPT_TAC))`

The output will be shown in the Lean InfoView window, in this case:

`|- p \/ p ==> p`

Prove.lean imports `HolInit`, which loads the whole library in the same order as HOL Light's `hol_lib.ml`.  This takes about 30 seconds each time the file is opened, because the theorems are proved when the library loads, as in HOL Light.  Prove.lean can also be run from the command line with `make prove` or `lake lean Prove.lean`.  Use `lake lean`, not `lake env lean`: only `lake lean` (and the VS Code extension) loads the compiled native code, and without it the load takes about 6 minutes.  `make prove` also shows the messages printed while loading (they are not shown when loading in VS Code).  By default it uses level 2: HOL Light's verbose messages during the load, about 250,000 lines.  `make prove SHOW_LOAD=1` shows only HOL Light's default messages (about 5,000 lines).  With `lake lean`, set `HOLLEAN_SHOW_LOAD=1` or `2`.  These switches are off by default, as in HOL Light; set them yourself with, for example, `#eval copverb.set true`.

A few things to know:

* Parenthesise a quotation when it is not the last argument: `prove ([[...]]) tac` works, `prove [[...]] tac` does not parse.
* As in HOL Light, after loading, a variable with no type information defaults to a natural number.  Write `[[!x y:real. ...]]` for real numbers; `&n`, `abs` and `max` already make a term real.
* To keep a result under a name, as HOL Light's `let th = NUM_REDUCE_CONV `2 + 2 * 3`;;`, define it: `unsafe def th : thm := NUM_REDUCE_CONV [[2 + 2 * 3]]`.  Later commands can use `th`; a failure is reported with HOL Light's message.
* HOL Light's online help is available as `#eval help("NAME")`, e.g. `#eval help("REAL_ARITH")`; an unknown name lists the closest entries, though note that the help uses HOL Light syntax and not the new Lean syntax.
* `#eval Help.search [Help.name "ADD"]` searches the theorem database, like HOL Light's `search [name "ADD"]` (Prove.lean imports `Help`).  The first search loads the theorem database and takes about 30 seconds.
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
| `Session.lean` | the session state, and the names HOL Light users type |
| `HolLibrary/` | files from HOL Light's `Library/` (so far `prime.ml`, `floor.ml`, `components.ml`, `records.ml`, `bdd.ml`, `words.ml`, `analysis.ml`, `rstc.ml`, `transc.ml`, `wo.ml`, `card.ml`, `bitmatch.ml`, `products.ml`, `agm.ml`, `iter.ml`, `bitsize.ml`, `binary.ml`, `isum.ml`, `frag.ml`, `binomial.ml`, `pocklington.ml` and `ringtheory.ml`), pure like HolMath |
| `SessionLibrary/` | connects `HolLibrary` to Session and exports its theorems by name |
| `HolInit.lean` | loads the library in `hol_lib.ml` order |
| `Help.lean`, `Database.lean`, `Help/` | help.ml, database.ml and HOL Light's help files |
| `HolTest/`, `HolTest.lean` | the test suite (about 2,700 checks), including the examples from HOL Light's help files and its UnitTests; HolTest.lean imports every test module and is built only by `make test` and `make check` |
| `Hol.lean` | the `hollean` executable (`hol.ml`); it does not import the tests |
| `HolTrace/`, `HolTrace.lean` | the `holtrace` executable: a proof reconstructor for [HOLTrace](https://holtrace.cr.yp.to) files (see `HolTrace/README.md`) |
| `Prove.lean` | your scratchpad |

HolCore, HolMath and HolLibrary contain no `unsafe` code and no `sorry`; the build checks this.  The `unsafe` code is in Session.lean and the modules built on it (SessionLibrary, HolInit, Database and Hol.lean).

To use a `Library/` file, import its `SessionLibrary` module and call its `ensure` function, the equivalent of HOL Light `needs`:

```lean
import SessionLibrary
open Session SessionLibrary.Prime
#eval ensurePrime                       -- needs "Library/prime.ml"
-- and SessionLibrary.Floor.ensureFloor  -- needs "Library/floor.ml"
-- and SessionLibrary.Components.ensureComponents  -- needs "Library/components.ml"
-- and SessionLibrary.Records.ensureRecords        -- needs "Library/records.ml"
-- and SessionLibrary.BDD.ensureBDD                -- needs "Library/bdd.ml"
-- and SessionLibrary.Words.ensureWords            -- needs "Library/words.ml"
-- and SessionLibrary.Analysis.ensureAnalysis      -- needs "Library/analysis.ml"
-- and SessionLibrary.RSTC.ensureRSTC              -- needs "Library/rstc.ml"
-- and SessionLibrary.Transc.ensureTransc          -- needs "Library/transc.ml"
-- and SessionLibrary.Wo.ensureWo                  -- needs "Library/wo.ml"
-- and SessionLibrary.Card.ensureCard              -- needs "Library/card.ml"
-- and SessionLibrary.BitMatch.ensureBitMatch    -- needs "Library/bitmatch.ml"
-- and SessionLibrary.Products.ensureProducts    -- needs "Library/products.ml"
-- and SessionLibrary.Agm.ensureAgm                -- needs "Library/agm.ml"
-- and SessionLibrary.Iter.ensureIter              -- needs "Library/iter.ml"
-- and SessionLibrary.Bitsize.ensureBitsize        -- needs "Library/bitsize.ml"
-- and SessionLibrary.Binary.ensureBinary          -- needs "Library/binary.ml"
-- and SessionLibrary.Isum.ensureIsum              -- needs "Library/isum.ml"
-- and SessionLibrary.Frag.ensureFrag              -- needs "Library/frag.ml"
-- and SessionLibrary.Binomial.ensureBinomial      -- needs "Library/binomial.ml"
-- and SessionLibrary.Pocklington.ensurePocklington -- needs "Library/pocklington.ml"
-- and SessionLibrary.RingTheory.ensureRingTheory   -- needs "Library/ringtheory.ml"
#eval PRIME_DIVPROD
#eval GCD_CONV [[gcd(12,18)]]
```

Each library name is exported under its HOL Light name.  Where a library rebinds a name that Session (or a library it needs) already has, qualify it: `transc.ml` rebinds `DIVISION_0`, `REAL_DIV_SQRT`, `SQRT_EVEN_POW2` and `SUM_DIFFS` from the core and `SYM_CANON_CONV` and `EXT_CONV` from `analysis.ml`, so write `SessionLibrary.Transc.SUM_DIFFS` for transc's version.  `isum.ml` rebinds `INT_OF_REAL_THM` (a stronger version of int.ml's rule); use `SessionLibrary.Isum.INT_OF_REAL_THM` for isum.ml's.  `pocklington.ml` rebinds lib.ml's `num_0`, `num_1` and `num_2` (same values; `HolCore.Lib.num_0` is the core one).

HolMath and `HolLibrary/Prime.lean` are translated by hand and read much like the OCaml: `HolMath/Base.lean` provides HOL Light's tactics, rules and conversions under their own names, with infix `THEN`, `THENL`, `ORELSE`, `THENC`, `ORELSEC` and `o`.

## Building and testing ##

You need Lean 4 (installed with `elan`; the version is fixed in `lean-toolchain`).  The main make targets:

* `make build` builds everything except the tests: the `hollean` executable and HOL Light's Library/ files.  A build from scratch takes a while, mostly compiling to C.
* `make test` builds and runs the tests (the HolTest library; HolTest.lean is the only place they are imported) and prints assertion counts per module.  After a build, running all the tests takes about 35 minutes of CPU, less in wall time.  There is no output until the build finishes.
* `make verify` checks the build log for errors, warnings, failed tests, panics, and `unsafe` or `sorry` in the pure libraries.
* `make check` does a clean build followed by `make verify`.
* `make help` lists the other targets.

GitHub Actions runs `make core` on pushes to main and on pull requests (`.github/workflows/ci.yml`).

## Known differences from HOL Light ##

* `dest_small_numeral` does not fail on numbers too large for an OCaml `int`.
* Some long terms are broken across lines differently.
* By default, results that come from HOL Light's hash-based lookup tables (for example `atoms`) can come out in a different order.  Setting the environment variable `HOLLEAN_OCAML_HASH` makes them use OCaml's hash and match HOL Light's order.
* Parts of the library are built when first used, rather than all at load as in HOL Light (`HolInit` loads everything up front).
* `ORELSE_TCL` and `REPEAT_TCL` also catch a failure of the following tactic.
* OCaml's physical equality `==` is translated as structural equality, because pointer comparison needs `unsafe` code.  Results are the same, but a test of whether two values are the same object gives `true` for equal copies: in `qmap`'s help example, `map I million == million` is `true`, not `false`.
* `SessionLibrary.Analysis` exports every name `Library/analysis.ml` defines under its HOL Light name.  About 100 of them, such as `REAL_LE_TRANS`, `SUM_LE`, `sum` and `EXPAND_TAC`, are also names in `Session`, where they refer to the core versions.  With both namespaces open, write `SessionLibrary.Analysis.SUM_LE` or `Session.SUM_LE`.  In HOL Light the later binding simply shadows the earlier one.
* Names that are not valid in Lean are changed: `omit` is written `«omit»`, and `WF_REC_CASES'` is `WF_REC_CASES_prime`.

Please let me know how you get on, and if you find any issues.

Chris
# HolLean
