# Makefile for HolLean - a Lean 4 translation of HOL Light.
#
# A thin, documented wrapper around the `lake` invocations used day to day.
# See lakefile.toml for the targets themselves: FIVE libraries, each with a
# single root module mirroring the project's layering, plus one executable.
#
#     HolCore   the kernel and core proof infrastructure (self-contained)
#     HolMath   the mathematical theories        (depends on HolCore)
#     Session   the `unsafe` session state       (depends on HolCore + HolMath)
#     HolTest   the runtime test suite           (depends on Session)
#     HolInit   eager bootstrap for scratchpad use, outside defaultTargets
#     hollean   the executable, rooted at Hol.lean (the default target)
#
# QUICK REFERENCE - every target, grouped by what you want to do:
#
#   building, cheapest tier first
#     make core          the kernel only
#     make math          + the mathematical theories (no tests run)
#     make session       + the session state layer
#     make proofs        + the Library files; proof-checks everything, no
#                        native code, no tests
#     make               everything but the tests, including native code and
#                        the binary
#     make module M=...  one module only
#     make rebuild       clean, then build from scratch, capturing the log
#
#   interactive use
#     make prove         run your own experiments in Prove.lean
#
#   verification
#     make check         build from scratch and enforce the acceptance gates
#     make verify        apply the gates to an existing build log
#     make test          build and run the tests (HolTest.lean, the ONLY
#                        place they are imported), with assertion counts
#     make test-module M=...  run one test module standalone
#
#   housekeeping
#     make clean         remove build artefacts and the log
#     make distclean     also remove .lake entirely
#     make help          list targets and variables
#
# NOTE ON OUTPUT VOLUME: HOL Light sets its `verbose` flag to true by default
# (lib.ml), so MESON prints a search trace (`0..0..1..3..11..solved at 633`,
# meson.ml 447-467) and ITAUT prints `Searching with limit N`; the parser also
# warns about every term with invented type variables, and grobner.ml prints
# its progress.  The test suite turns `verbose`, `type_invention_warning` and
# `grobner_messages` off (HolTest/CommonTest.lean), so
# build.log holds the test results; Prove.lean keeps HOL Light's defaults.
#
LAKE ?= lake

# What `make`/`make build` builds: the executable (Hol.lean, which does NOT
# import the tests) and HOL Light's Library/ files.  The test suite is the
# HolTest library, built only by `make test` and `make check`.
BUILD_TARGETS ?= hollean @/HolLibrary @/SessionLibrary
TEST_TARGETS ?= @/HolTest

# --- Parallelism -----------------------------------------------------------
#
# Leave THREADS EMPTY unless you have a reason not to.  It sets
# LEAN_NUM_THREADS, which in Lake 5.0.0 also sizes the task pool Lake schedules
# JOBS on - so pinning it to 1 serialises the whole build, not just the work
# inside each process.  MEASURED on the same three modules: 1m44s wall with
# Lean's default versus 4m57s at THREADS=1, for near-identical CPU time.  An
# early version of this Makefile defaulted to 1 and a from-scratch build took
# 68 minutes wall for ~21 minutes of CPU; the idle time was that serialisation.
# (Memory pressure looked like a plausible cause at the time - the machine had
# swap in use - but the thread measurement above ruled it out.)
#
# Lake 5.0.0 exposes no job-count flag, so if you ever do hit memory pressure
# THREADS is the only lever available, and it trades wall time badly.
#
# Pin it where determinism or bounded memory matters for ONE heavy module:
#   make test-module M=HolTest/WfTest.lean THREADS=1
THREADS ?=
ifeq ($(strip $(THREADS)),)
LEAN_ENV :=
else
LEAN_ENV := LEAN_NUM_THREADS=$(THREADS)
endif

# Extra flags passed to every `lake build`.  Normally empty; a hook for
# one-off experiments such as --no-cache or -v.
LAKEFLAGS ?=

# Captured build log, written by `rebuild`, `check` and `test`, and read by
# `verify`.  Also removed by `clean`.
BUILD_LOG ?= build.log

# Module or file argument, used by BOTH `make module` (a module name, e.g.
# HolMath.RealArith) and `make test-module` (a path, e.g. HolTest/WfTest.lean).
M ?=

# Message level for `make prove` (HOLLEAN_SHOW_LOAD, see the prove target).
SHOW_LOAD ?= 2

# A MASKED FAILURE is a real failure wearing the costume of ordinary output.
# Session reads each theorem bundle from a cached ref through an `unsafe def`; if
# the layer never initialised, that hits `panic!` - and `panic!` does NOT abort,
# it prints to stderr and returns `Inhabited.default`, then execution CONTINUES
# (verified experimentally).  `Inhabited thm` is `REFL default` and
# `default : term` prints as the EMPTY STRING, so every field of the degenerated
# bundle prints as an equation with both sides invisible.  A test meant to
# exercise real theorems instead emits that, which reads as OUTPUT rather than an
# error, and the build still exits 0.  There are ~466 `panic!` sites feeding this
# path.
#
# WAS 1, NOW 0.  One intentional line used to print `default : thm` on purpose,
# costing a permanent exemption and meaning a REAL degeneration had to reach TWO
# before the gate fired.  That probe now asserts the same property STRUCTURALLY
# (HolTest/RegressionTest.lean), so zero is the correct expectation and any hit is
# a genuine defect.
EXPECTED_MASKED ?= 0

# Pattern matching a DEGENERATED theorem (see EXPECTED_MASKED above): `|-`
# followed by nothing but an `=` and whitespace, i.e. an equation whose sides
# both printed empty.  Covers BOTH renderings: `|-  =` once the session bootstrap
# has installed `=` as an infix, and `|- =  ` before it has (where the printer
# falls back to application form).  The narrower `\|-  =` pattern missed the
# second.  Verified: matches both degenerate forms, and none of `|- x = y`,
# `|- T = T`, `|- p ==> p`.
MASKED_RE ?= \|-[[:space:]]*=[[:space:]]*$$

# A `panic!` does not stop the build (it returns a default value and carries
# on), so a layer that failed to build is visible only as a `PANIC` line.
# Any such line is a defect.  HolTest/HolInitTest imports HolInit, so under
# `make check` (which builds the tests) this also covers the full load sequence.

# Pattern matching a FAILED ASSERTION.  Test modules print `-> OK` when a check
# passes and `-> FAILED`/`-> FAIL` when it does not, but only `MISMATCH` used to
# be gated - so a failing assertion could ship with all gates GREEN.  It did:
# four such lines sat in HolTest/PretermTest.lean undetected (three wrong
# expectations of mine, one mis-premised pipeline).  Anchored on the `-> ` arrow
# so prose mentioning the word is not matched.
FAILED_RE ?= -> FAIL

# Pattern matching a REAL Lean diagnostic, i.e. the `file:line:col: error`
# form.  Grepping for the bare word "error" is WRONG here: several tests
# legitimately PRINT the word as expected output (HolTest/NumsTest.lean shows
# `dest_small_numeral (SUC 0) = error: dest_numeral`), which a loose pattern
# reports as a build failure.  Verified: loose 'error' finds 6 matches in a
# clean build log (tests printing the word as EXPECTED output), this pattern 0.
ERROR_RE ?= \.lean:[0-9]+:[0-9]+: error

# Pattern matching a REAL `unsafe` DECLARATION (not the word in a docstring).
# The HolMath layer is a pure library: all `unsafe` state lives in Session and
# above.  Several HolMath docstrings PROSE about staying "PURE with ZERO
# `unsafe`", so grepping the bare word is WRONG (it finds those comments); this
# anchors on `unsafe` as a leading declaration modifier before def/instance/etc,
# optionally preceded by `private` or an attribute.  Verified: 0 in the pure
# libraries, 3452 in Session.
UNSAFE_DECL_RE ?= ^[[:space:]]*(private[[:space:]]+|@\[[^]]*\][[:space:]]*)*unsafe[[:space:]]+(def|instance|abbrev|structure|opaque|axiom)\b

# Directories the purity invariants scan.  BOTH HolCore and HolMath are pure
# libraries: every `unsafe` declaration in the project belongs in Session.lean or
# above (HolInit/Hol/HolTest legitimately carry `unsafe` because CALLING an
# unsafe Session accessor requires an unsafe context).  HolCore was previously
# unscanned - it was at zero by construction but nothing enforced it, so a
# regression there would have been invisible.  Measured: HolCore 0, HolMath 0.
PURE_SRC ?= HolCore HolMath HolLibrary
# The umbrella module every HolTest module must be imported by.
ROOT_MODULE ?= HolTest.lean

.PHONY: all build core math session proofs prove rebuild clean distclean check verify test test-module module help

# ---------------------------------------------------------------------------
# Building
# ---------------------------------------------------------------------------

all: build

## build: everything but the tests - proofs, native code and the executable
build:
	$(LEAN_ENV) $(LAKE) build $(LAKEFLAGS) $(BUILD_TARGETS)

## core: the kernel and core infrastructure only (cheapest tier)
core:
	$(LEAN_ENV) $(LAKE) build $(LAKEFLAGS) @/HolCore

## math: the mathematical theories, without running the tests
math:
	$(LEAN_ENV) $(LAKE) build $(LAKEFLAGS) @/HolMath

## session: the session state layer (HolCore + HolMath + Session)
session:
	$(LEAN_ENV) $(LAKE) build $(LAKEFLAGS) @/Session

## proofs: check all proofs (oleans only) - skips native compilation
# The DEFAULT target is the `hollean` executable, so Lake compiles Lean -> C ->
# object code for every module.  That native codegen was MEASURED at 35% of a
# from-scratch build and produces a binary that proof checking does not need.
# Building the module facets `+Hol +HolLibrary +SessionLibrary` instead
# elaborates everything (no tests: they are only in HolTest.lean), but emits
# no C.  Use this while developing; use `build` when
# you actually want the executable.
#
# The tiers below are cumulative - each builds on the one above it.  Job counts
# are current; wall times depend heavily on your machine and on whether MESON's
# verbose trace is enabled, so they are deliberately not recorded here.
#
#   make core       28 jobs   kernel and core infrastructure only
#   make math       46 jobs   + the mathematical theories
#   make session    49 jobs   + Session
#   make proofs               + the Library files (no tests)
#   make build                + native codegen and the executable
proofs:
	$(LEAN_ENV) $(LAKE) build $(LAKEFLAGS) +Hol +HolLibrary +SessionLibrary

## rebuild: clean, then build from scratch, capturing the log
rebuild: clean
	$(LEAN_ENV) $(LAKE) build $(LAKEFLAGS) $(BUILD_TARGETS) 2>&1 | tee $(BUILD_LOG)

## module: build one module only, e.g. make module M=HolMath.RealArith
module:
	@if [ -z "$(M)" ]; then \
	  echo "usage: make module M=<Module.Name>   e.g. M=HolMath.RealArith"; \
	  exit 2; \
	fi
	$(LEAN_ENV) $(LAKE) build $(LAKEFLAGS) $(M)

# ---------------------------------------------------------------------------
# Cleaning
# ---------------------------------------------------------------------------

## clean: remove compiled artefacts (.lake/build) and the build log
clean:
	rm -rf .lake/build
	rm -f $(BUILD_LOG)

## distclean: also remove .lake entirely (safe - the project has no external deps)
distclean: clean
	rm -rf .lake

# ---------------------------------------------------------------------------
# Verification
# ---------------------------------------------------------------------------

## check: build from scratch and enforce the acceptance gates
# The standing acceptance criteria are stricter than "the build exited 0": also
# zero warnings, no masked bundle failures, and no test MISMATCH.  Builds with
# `|| true` so that a failing build still reaches `verify` and reports WHICH
# gate broke rather than dying silently.
check: clean
	@echo "==> building from scratch (THREADS=$(THREADS))"
	@$(LEAN_ENV) $(LAKE) build $(LAKEFLAGS) $(BUILD_TARGETS) $(TEST_TARGETS) > $(BUILD_LOG) 2>&1 || true
	@$(MAKE) --no-print-directory verify

## verify: apply the acceptance gates to an existing build log
# Split out from `check` so the gates can be exercised without a rebuild, e.g.
#   make verify EXPECTED_MASKED=99      (should FAIL)
verify:
	@test -f $(BUILD_LOG) || { echo "no $(BUILD_LOG); run 'make check' or 'make rebuild'"; exit 2; }
	@errors=$$(grep -cE '$(ERROR_RE)|^error' $(BUILD_LOG) || true); \
	warnings=$$(grep -cE '^warning:|^⚠' $(BUILD_LOG) || true); \
	masked=$$(grep -cE '$(MASKED_RE)' $(BUILD_LOG) || true); \
	mismatch=$$(grep -c MISMATCH $(BUILD_LOG) || true); \
	failed=$$(grep -cF -- '$(FAILED_RE)' $(BUILD_LOG) || true); \
	panics=$$(grep -c 'PANIC' $(BUILD_LOG) || true); \
	ok=$$(grep -c -- '-> OK' $(BUILD_LOG) || true); \
	pure_unsafe=$$(grep -rhE '$(UNSAFE_DECL_RE)' $(PURE_SRC) 2>/dev/null | grep -c . || true); \
	pure_sorry=$$(grep -rhwE 'sorry' $(PURE_SRC) 2>/dev/null | grep -c . || true); \
	unimported=0; \
	for f in HolTest/*.lean; do \
	  mod=$$(basename "$$f" .lean); \
	  grep -qE "^import HolTest\.$$mod([[:space:]]|$$)" $(ROOT_MODULE) || { \
	    echo "    UNIMPORTED HolTest module: $$mod"; unimported=$$((unimported+1)); }; \
	done; \
	printf '    %-18s %-6s %s\n' "errors"          "$$errors"   "(want 0)"; \
	printf '    %-18s %-6s %s\n' "warnings"        "$$warnings" "(want 0)"; \
	printf '    %-18s %-6s %s\n' "masked failures" "$$masked"   "(want $(EXPECTED_MASKED))"; \
	printf '    %-18s %-6s %s\n' "MISMATCH"        "$$mismatch" "(want 0)"; \
	printf '    %-18s %-6s %s\n' "failed assertions" "$$failed" "(want 0)"; \
	printf '    %-18s %-6s %s\n' "panics" "$$panics" "(want 0)"; \
	printf '    %-18s %-6s %s\n' "pure-lib unsafe" "$$pure_unsafe" "(want 0)"; \
	printf '    %-18s %-6s %s\n' "pure-lib sorry"  "$$pure_sorry" "(want 0)"; \
	printf '    %-18s %-6s %s\n' "unimported tests" "$$unimported" "(want 0)"; \
	printf '    %-18s %-6s %s\n' "assertions OK"   "$$ok"       "(informational)"; \
	fail=0; \
	[ "$$errors"   = "0" ] || fail=1; \
	[ "$$warnings" = "0" ] || fail=1; \
	[ "$$masked"   = "$(EXPECTED_MASKED)" ] || fail=1; \
	[ "$$mismatch" = "0" ] || fail=1; \
	[ "$$failed"   = "0" ] || fail=1; \
	[ "$$panics"   = "0" ] || fail=1; \
	[ "$$pure_unsafe" = "0" ] || fail=1; \
	[ "$$pure_sorry"  = "0" ] || fail=1; \
	[ "$$unimported" = "0" ] || fail=1; \
	if [ "$$fail" = "0" ]; then \
	  echo "==> OK: all gates passed (full log in $(BUILD_LOG))"; \
	else \
	  echo "==> FAILED: see $(BUILD_LOG)"; \
	  exit 1; \
	fi

## prove: run your own scratchpad experiments in Prove.lean
# HOLLEAN_SHOW_LOAD shows the library load's messages; HolInit drops them
# otherwise, because in VS Code they would deadlock the language server.
#   1  HOL Light's default messages (MESON progress, type-invention warnings);
#   2  also the METIS and CoP tracing (`metisverb`, `Metis_unify.verb`,
#      `copverb`), for the load only.
# `make prove` uses SHOW_LOAD (default 2): make prove SHOW_LOAD=1 for less
# Prove.lean imports HolInit, which pulls in HolCore + HolMath + Session but
# NOT HolTest, so you do not re-run the project's test suite.  Prove.lean itself
# belongs to no Lake target and nothing imports it, so whatever you write there
# cannot break `build`, `proofs` or `check`.
#
# HolInit is built first because Prove.lean imports it.  Its `initialize` block
# runs the whole HOL Light load sequence - Lean's nearest analogue to hol.ml's
# `loads` - so nothing needs forcing, at the cost of a bootstrap on every run.
# Expect MESON's verbose search trace during that bootstrap; that is HOL Light's
# startup behaviour, not a fault.
prove:
	$(LEAN_ENV) $(LAKE) build $(LAKEFLAGS) @/HolInit
	$(LEAN_ENV) HOLLEAN_SHOW_LOAD=$(SHOW_LOAD) $(LAKE) lean Prove.lean

## test: report per-module assertion counts and real errors from a build
# The test modules are compile-time `#eval`s, so building the HolTest library
# RUNS them.  This target therefore builds it (incrementally) and reads the log,
# rather than re-elaborating every test module in separate processes - which
# produces identical counts but takes minutes instead of seconds.
#
# Attribution is done with awk rather than a per-file grep for two reasons:
# long results WRAP onto continuation lines that carry no `file:line:col`
# prefix (so a naive grep undercounts), and a plain filename match collides on
# substrings (ArithTest.lean is a substring of RealArithTest.lean).  Tracking
# the most recently seen module and counting against it fixes both, and
# reproduces the counts obtained by running each module standalone.
#
# Assertion-style modules print `-> OK` per check; the older inspection-style
# modules just print theorems, so a count of 0 for those is expected and is
# NOT a failure.
test:
	@$(LEAN_ENV) $(LAKE) build $(LAKEFLAGS) $(TEST_TARGETS) > $(BUILD_LOG) 2>&1 || true
	@awk 'match($$0, /HolTest\/[A-Za-z0-9_]+\.lean/) { cur = substr($$0, RSTART, RLENGTH) } \
	      /-> OK/ && cur != "" { ok[cur]++ } \
	      END { for (f in ok) printf "%-40s assertions=%s\n", f, ok[f] }' $(BUILD_LOG) | sort
	@printf '%-40s assertions=%s\n' "-- total" "$$(grep -c -- '-> OK' $(BUILD_LOG) || true)"
	@errs=$$(grep -cE '$(ERROR_RE)|^error' $(BUILD_LOG) || true); \
	printf '%-40s errors=%s\n' "-- total" "$$errs"; \
	[ "$$errs" = "0" ] || { echo "see $(BUILD_LOG)"; exit 1; }

## test-module: run ONE test module standalone, e.g. make test-module M=HolTest/WfTest.lean
test-module:
	@if [ -z "$(M)" ]; then \
	  echo "usage: make test-module M=HolTest/<Name>.lean"; \
	  exit 2; \
	fi
	$(LEAN_ENV) $(LAKE) lean $(M)

# ---------------------------------------------------------------------------
# Help
# ---------------------------------------------------------------------------

## help: list available targets
help:
	@echo "HolLean targets:"
	@grep -E '^## ' $(MAKEFILE_LIST) | sed 's/^## /  /'
	@echo ""
	@echo "Variables:"
	@printf '  %-22s %s\n' "THREADS=$(THREADS)" "Lean threads; leave EMPTY - setting 1 serialises the build"
	@printf '  %-22s %s\n' "BUILD_LOG=$(BUILD_LOG)" "log written by rebuild/check/test, read by verify"
	@printf '  %-22s %s\n' "EXPECTED_MASKED=$(EXPECTED_MASKED)" "tolerated masked-failure lines; 0 - any hit is a defect"
	@printf '  %-22s %s\n' "LAKEFLAGS=$(LAKEFLAGS)" "extra flags for every lake build"
	@printf '  %-22s %s\n' "M=$(M)" "module for 'make module' / file for 'make test-module'"
