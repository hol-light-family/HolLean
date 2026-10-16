/- File: HolTest.lean
Library root: the runtime test suite (compile-time `#eval`s).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

This module is the ROOT of the `HolTest` Lean library (see `lakefile.toml`).
Lake's `roots` determine which modules BELONG to a library, while the default
`globs` build only the root module itself and, recursively, its local imports.
So this import list IS the library's build set - a module absent from it is not
built by `lake build @/HolTest`.  In `hol_lib.ml` order.  This is the ONLY place the tests are imported: the
`hollean` executable (Hol.lean) does not build them; `make test` and
`make check` do. -/

-- Importing a test module RUNS its checks, since the tests are `#eval`s.

import HolTest.CommonTest
import HolTest.AxiomsTest
import HolTest.NumsArithWfCheck
import HolTest.PairRecComputeCheck
import HolTest.ListsIndTypesCheck
import HolTest.IntCalcIntCheck
import HolTest.NormRealCheck
import HolTest.SetsCheck
import HolTest.HelpTest
import HolTest.SubgoalTest
import HolTest.HolInitTest
import HolTest.CoreTest
import HolTest.CoverageTest
-- Core-layer module tests.  `Preterm`, `Itab`, `FirstOrder` and `System`
-- are covered here.
import HolTest.FusionTest      -- the logical kernel: rules + side conditions
import HolTest.DruleTest       -- derived rules; higher-order matching
import HolTest.PretermTest     -- preterm elaboration / type inference
import HolTest.ItabTest        -- ITAUT, with Pelletier-style propositions
import HolTest.NetsTest        -- term nets: enter / lookup / merge_nets
import HolTest.FirstOrderTest  -- HOL <-> first-order translation
import HolTest.SystemTest      -- the pure formatter shim
import HolTest.LibTest         -- combinators, folds, Func, the `o` family
import HolTest.BasicsTest      -- syntax helpers, type_match, paths
import HolTest.BoolTest        -- derived propositional rules
import HolTest.EqualTest       -- conversions and conversionals
import HolTest.SimpTest        -- the rewriting engine, term_order, nets
import HolTest.TacticsTest     -- the tactic engine; THEN/THENL semantics
import HolTest.ParserTest      -- precedence, associativity, the lexer
import HolTest.PrinterTest     -- parenthesisation, round trip, escaping
import HolTest.TheoremsTest
import HolTest.IndDefsTest
import HolTest.ClassicTest
import HolTest.TriviaTest
import HolTest.CanonTest
import HolTest.MesonTest
import HolTest.MetisTest
import HolTest.TheCopsTest
import HolTest.TraceTest
import HolTest.QuotTest
import HolTest.ImpConvTest
import HolTest.PairTest
import HolTest.ComputeTest
import HolTest.RegressionTest
import HolTest.NumsTest
import HolTest.RecursionTest
import HolTest.ArithTest
import HolTest.WfTest
import HolTest.CalcNumTest
import HolTest.NormalizerTest
import HolTest.GrobnerTest
import HolTest.IndTypesTest
import HolTest.ListsTest
import HolTest.RealAxTest
import HolTest.CalcIntTest
import HolTest.RealArithTest
import HolTest.RealTest
import HolTest.CalcRatTest
import HolTest.IntTest
import HolTest.SetsTest
import HolTest.IterateTest
import HolTest.CartTest
import HolTest.DefineTest
-- Library/ files (loaded by `needs` after hol.ml)
import HolTest.PrimeTest
import HolTest.FloorTest
import HolTest.ComponentsTest
import HolTest.RecordsTest
import HolTest.BDDTest
import HolTest.WordsTest
import HolTest.AnalysisTest
import HolTest.RSTCTest
import HolTest.TranscTest
import HolTest.WoTest
import HolTest.CardTest
import HolTest.BitMatchTest
import HolTest.ProductsTest
import HolTest.AgmTest
import HolTest.IterTest
import HolTest.BitsizeTest
import HolTest.BinaryTest
import HolTest.IsumTest
import HolTest.FragTest
import HolTest.BinomialTest
import HolTest.PocklingtonTest
import HolTest.RingTheoryTest
import HolTest.UnitBasicTest
import HolTest.UnitParserTest
import HolTest.UnitPrinterTest
import HolTest.UnitRecordsTest
import HolTest.HolTraceTest
import HolTest.IntegerTest
import HolTest.MultiplicativeTest
import HolTest.PrimitiveTest
import HolTest.PrattTest
import HolTest.PolyTest
import HolTest.MatroidsTest
import HolTest.PermutationsTest
import HolTest.JacobiTest
import HolTest.CalcRealTest
import HolTest.WordAutomataTest
import HolTest.QTest
import HolTest.FieldTheoryTest
import HolTest.RabinTestTest
import HolTest.GroupTheoryTest
import HolTest.ModmulGroupTest
import HolTest.SymmetricGroupTest
