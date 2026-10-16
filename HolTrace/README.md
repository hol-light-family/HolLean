# HolTrace: a proof reconstructor for HOLTrace files #

[HOLTrace](https://holtrace.cr.yp.to) is a file format that records a HOL Light session as a sequence of types, terms, inferences and theorems.  The `holtrace` executable verifies such a file by replaying it: it rebuilds every type and term, applies the primitive rule each inference line names, and checks that the theorem produced is exactly the one the file states - hypotheses, their order, and conclusion.

Since `HolCore.Kernel.thm` has a private constructor, nothing outside the kernel can fabricate a theorem.  The only theorems the restorer can hold are ones the kernel handed it, so the only way a trace can be accepted is for this kernel to accept every step in it.  A bug in the restorer can reject a good trace, or report the wrong theorem, but it cannot make the kernel accept an unsound inference.

## Running it ##

Traces are not in this repository.  To try it, fetch one:

```sh
wget https://holtrace.cr.yp.to/prime.50.gz && gunzip prime.50.gz
lake build holtrace
lake exe holtrace prime.50
```

which reports

```
verified 2399423 bytes, 359543 lines, 597 types, 176388 terms, 91115 infs, 91115 thms, 6 typedefs
named thms: 327
```

matching the counts HOLTrace's own tools report for that file.  Exit status is 0 if every trace verified, 1 if one did not, 2 on a usage error.  Nothing in the Makefile's targets depends on HolTrace; `lake build holtrace` and `lake exe holtrace` are the whole interface.

| Option | |
|---|---|
| `--print NAME` | print the theorem named NAME once the trace verifies |
| `--names` | print every named theorem the trace defines, with its name |
| `--names-only` | print those names on their own |
| `--no-thm-check` | run every inference, but do not compare the results with the theorem statements the trace records |
| `--lax-names` | accept theorem names outside HOL Light's identifiers |
| `--quiet` | print nothing on success |
| `-h`, `--help` | show the usage message |

`FILE` may be `-` to read standard input.

## What replay assumes ##

Replay starts from a bare kernel, so a trace of HOL Light's standard library is checked from nothing: the trace itself creates every constant, type and axiom it uses.  Two primitive objects have no trace tag, because HOL Light introduces them with `new_type`/`new_constant` rather than by inference - the type of individuals `ind` (nums.ml) and the choice operator `@` (class.ml) - so `declarePrimitives` supplies both.

Because of that, this library depends on `HolCore` alone.  Importing `Session` would run `setupBool` when the module loads, declaring `T`, `/\` and the rest, and the trace's own definitions of those names would then collide.  One consequence is that theorems print with HOL Light's initial fixities, so `=` comes out in prefix form rather than infix.

The kernel's type and constant tables are process-global and nothing retracts a constant once declared, so two traces that define the same constant cannot both be verified in one run.

## Tests ##

```sh
make test-module M=HolTest/HolTraceTest.lean
```

43 checks: the encoding table and worked `T_DEF` example published with the format, a trace exercising every inference tag, and the malformed or unsound traces that must each be rejected for a stated reason.  The checks are compile-time `#eval`s that PRINT their result, so `lake lean` exits 0 either way - read the output, or count it:

```sh
make test-module M=HolTest/HolTraceTest.lean 2>&1 | tee t.log
grep -c -- '-> OK' t.log     # expect 43
grep -c MISMATCH t.log       # expect 0
```

This module is also run by `.github/workflows/ci.yml`, and is part of the suite `make test` runs.

## Layout ##

| Path | Contents |
|---|---|
| `HolTrace/Parse.lean` | the argument encoding: base-32 `0-9A-V`, the `!@#$%^&*()` shorthands for *n*-1 through *n*-10, the `-`-relative form, and the inserted-space rule.  Pure and total on every input |
| `HolTrace/Restore.lean` | the replay engine: the four counters, the twenty inference tags, and the kernel calls |
| `HolTrace.lean` | library root and the command line |

The format is specified at <https://holtrace.cr.yp.to/format.html>.

## Why this is worth running ##

A trace was produced by HOL Light on OCaml, and nothing in its trace-saver is shared with the restorer here, so verifying one cross-checks two independent kernels on real proofs.  A disagreement about `term_union`'s hypothesis ordering, `alphaorder`, variable capture in `inst`, or the sorted type variables a type definition is parameterised by shows up as a rejected trace rather than as nothing at all.
