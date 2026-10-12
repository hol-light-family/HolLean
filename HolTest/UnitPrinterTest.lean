/- File: HolTest/UnitPrinterTest.lean
Runtime test suite: HOL Light's own UnitTests/printer_tests.ml, translated.
Every `check label input expected` case (104) in file order, the
prioritize_int/real/num and print_types_of_subterms changes between them at
the same points, and the 3 `check_roundtrip` cases: 107 in all, as in HOL
Light, where all 107 pass ("OK: 107/107 printer tests passed", /tmp/hol4).
The case table is the file's own string literals, copied unchanged (OCaml and
Lean read `\\` and `\"` alike).
Part of the Lean4 translation of HOL Light by Chris Walton 2026. -/

import HolTest.CommonTest

open HolCore.Kernel HolTest.CommonTest

namespace HolTest.UnitPrinterTest
open Session

private def seg0 : List (String × String × String) := [
  ("numeral.zero", "0:num", "0"),
  ("numeral.large", "12345:num", "12345"),
  ("list.nil", "[]:num list", "[]"),
  ("list.three", "[1;2;3]:num list", "[1; 2; 3]"),
  ("list.nested", "[[1;2];[3;4]]:(num list)list", "[[1; 2]; [3; 4]]"),
  ("list.tyvar", "[(x:A);(y:A);(z:A)]:A list", "[x; y; z]"),
  ("gabs.tuple", "(\\(x,y). x + y) ((1:num),(2:num))", "(\\(x,y). x + y) (1,2)"),
  ("gabs.tyvar", "\\((x:A),(y:B)). (x,y)", "\\(x,y). x,y"),
  ("univ.num", "(:num)", "(:num)"),
  ("univ.bool", "(:bool)", "(:bool)"),
  ("univ.tyvar", "(:A)", "(:A)"),
  ("set.three", "{1,2,3}:num->bool", "{1, 2, 3}"),
  ("set.compr", "{(x:num) | x > 0}", "{x | x > 0}"),
  ("set.compr.pair", "{(x:num,y:num) | x + y = 1}", "{x,y | x + y = 1}"),
  ("let.simple", "let x = 1 in x + (2:num)", "let x = 1 in x + 2"),
  ("let.chained", "let x = 1 in let y = 2 in x + (y:num)", "let x = 1 in let y = 2 in x + y"),
  ("let.parallel", "let x = 1 and y = 2 in x + (y:num)", "let x = 1 and y = 2 in x + y"),
  ("decimal", "#1.5", "#1.5"),
  ("match", "match (x:num) with 0 -> T | _ -> F", "match x with 0 -> true | _ -> false"),
  ("function", "function (0:num) -> T | _ -> F", "function 0 -> true | _ -> false"),
  ("cond.simple", "if (x:num) = 0 then 1 else 2", "if x = 0 then 1 else 2"),
  ("cond.cascade", "if (a:num) = 0 then 1 else if a = 1 then 2 else if a = 2 then 3 else 4", "if a = 0 then 1 else if a = 1 then 2 else if a = 2 then 3 else 4"),
  ("prefix.neg", "~T", "~true"),
  ("prefix.double", "~ (~T)", "~ ~true"),
  ("prefix.real_neg", "-- &3", "-- &3"),
  ("prefix.real_neg.parens", "-- (&3 + &4)", "--(&3 + &4)"),
  ("infix.and", "T /\\ F", "true /\\ false"),
  ("infix.implies", "p ==> q ==> r", "p ==> q ==> r"),
  ("infix.add", "(x:num) + 1", "x + 1"),
  ("infix.add.assoc", "(a:num) + b + c + d", "a + b + c + d"),
  ("infix.sub.assoc", "(a:num) - b - c", "a - b - c"),
  ("infix.mixed.prec", "(a:num) + b * c", "a + b * c"),
  ("infix.add.right_assoc", "(x:num) + (y + z)", "x + y + z"),
  ("infix.add.left_grouping", "((x:num) + y) + z", "(x + y) + z"),
  ("infix.mul.right_assoc", "(x:num) * (y * z)", "x * y * z"),
  ("infix.mul.left_grouping", "((x:num) * y) * z", "(x * y) * z"),
  ("infix.sub.left_assoc", "((x:num) - y) - z", "x - y - z"),
  ("infix.sub.right_grouping", "(x:num) - (y - z)", "x - (y - z)"),
  ("infix.exp.left_assoc", "((x:num) EXP y) EXP z", "x EXP y EXP z"),
  ("infix.exp.right_grouping", "(x:num) EXP (y EXP z)", "x EXP (y EXP z)"),
  ("infix.div.left_assoc", "((x:num) DIV y) DIV z", "x DIV y DIV z"),
  ("infix.div.right_grouping", "(x:num) DIV (y DIV z)", "x DIV (y DIV z)"),
  ("infix.mod.left_assoc", "((x:num) MOD y) MOD z", "x MOD y MOD z"),
  ("infix.mod.right_grouping", "(x:num) MOD (y MOD z)", "x MOD (y MOD z)"),
  ("infix.imp.right_assoc", "p ==> (q ==> r)", "p ==> q ==> r"),
  ("infix.imp.left_grouping", "(p ==> q) ==> r", "(p ==> q) ==> r"),
  ("infix.and.right_assoc", "p /\\ (q /\\ r)", "p /\\ q /\\ r"),
  ("infix.and.left_grouping", "(p /\\ q) /\\ r", "(p /\\ q) /\\ r"),
  ("infix.mix.add_then_mul", "((a:num) + b) * c", "(a + b) * c"),
  ("infix.mix.mul_then_add", "(a:num) * b + c", "a * b + c"),
  ("infix.mix.mul_then_add.parens", "(a:num) * (b + c)", "a * (b + c)"),
  ("infix.mix.add_sub.left", "((x:num) + y) - z", "(x + y) - z"),
  ("infix.mix.add_sub.right", "(x:num) + (y - z)", "x + y - z"),
  ("infix.mix.sub_add.left", "((x:num) - y) + z", "x - y + z"),
  ("infix.mix.sub_add.right", "(x:num) - (y + z)", "x - (y + z)")
]

private def seg1 : List (String × String × String) := [
  ("prioritize.int.add", "(x:int) + y + z", "x + y + z"),
  ("prioritize.int.add_sub", "((x:int) + y) - z", "(x + y) - z"),
  ("prioritize.int.mul_add", "(x:int) * y + z", "x * y + z"),
  ("infix.int.div.left_assoc", "((x:int) div y) div z", "x div y div z"),
  ("infix.int.div.right_grouping", "(x:int) div (y div z)", "x div (y div z)"),
  ("infix.int.rem.left_assoc", "((x:int) rem y) rem z", "x rem y rem z"),
  ("infix.int.pow.left_assoc", "((x:int) pow y) pow z", "x pow y pow z"),
  ("infix.int.pow.right_grouping", "(x:int) pow (y EXP z)", "x pow (y EXP z)")
]

private def seg2 : List (String × String × String) := [
  ("prioritize.real.add", "(x:real) + y + z", "x + y + z"),
  ("prioritize.real.add_sub", "((x:real) + y) - z", "(x + y) - z"),
  ("prioritize.real.mul_add", "(x:real) * y + z", "x * y + z"),
  ("prioritize.real.div", "(x:real) / (y * z)", "x / (y * z)"),
  ("infix.real.div.left_assoc", "((x:real) / y) / z", "x / y / z"),
  ("infix.real.div.right_grouping", "(x:real) / (y / z)", "x / (y / z)"),
  ("infix.real.pow.left_assoc", "((x:real) pow y) pow z", "x pow y pow z"),
  ("infix.real.pow.right_grouping", "(x:real) pow (y EXP z)", "x pow (y EXP z)"),
  ("infix.real.zpow.left_assoc", "((x:real) zpow y) zpow z", "x zpow y zpow z")
]

private def seg3 : List (String × String × String) := [
  ("infix.real.add", "&1 + &2", "&1 + &2"),
  ("infix.real.div", "&5 / &2", "&5 / &2"),
  ("infix.real.dec", "#1.5 + #2.25", "#1.5 + #2.25"),
  ("infix.eq", "(x:num) = (y:num)", "x = y"),
  ("infix.iff", "(T <=> F)", "true <=> false"),
  ("infix.append", "APPEND [1;2] [3;4]:num list", "APPEND [1; 2] [3; 4]"),
  ("binder.exists", "?x. x = (3:num)", "exists x. x = 3"),
  ("binder.forall", "!x. x + 0 = x", "forall x. x + 0 = x"),
  ("binder.lambda", "\\x. x + 1", "\\x. x + 1"),
  ("binder.lambda.multi", "\\x y z. x + y + (z:num)", "\\x y z. x + y + z"),
  ("binder.uexists", "?!x. x = (5:num)", "existsunique x. x = 5"),
  ("binder.epsilon", "@x. x > (0:num)", "@x. x > 0"),
  ("binder.forall.multi", "!x y z. x + y + z = (z:num) + y + x", "forall x y z. x + y + z = z + y + x"),
  ("app.curried", "(f:num->num->num->num) (a:num) (b:num) (c:num)", "f a b c"),
  ("app.deep", "(f:num->num) ((g:num->num) ((h:num->num) ((i:num->num) ((j:num->num) (x:num)))))", "f (g (h (i (j x))))"),
  ("app.parens", "(f:num->num->num) ((a:num) + b) ((c:num) * d)", "f (a + b) (c * d)"),
  ("atom.tyvar.app", "(f:A->A->A->A) (x:A) (y:A) (z:A)", "f x y z"),
  ("atom.tyvar.lambda", "\\(x:A). x", "\\x. x")
]

private def seg4 : List (String × String × String) := [
  ("show_types.var", "(x:num)", "(x:num)"),
  ("show_types.const", "T", "(true:bool)"),
  ("show_types.bool_const_F", "F", "(false:bool)"),
  ("show_types.app", "(f:num->num) (x:num)", "(f:num->num) (x:num)"),
  ("show_types.infix", "(x:num) + (y:num)", "(x:num) + (y:num)"),
  ("show_types.lambda", "\\(x:num). x + (1:num)", "\\(x:num). (x:num) + 1"),
  ("show_types.binder", "!(x:num). x = x", "forall (x:num). (x:num) = (x:num)"),
  ("show_types.tyvar", "(f:A->A) (x:A)", "(f:A->A) (x:A)"),
  ("show_types.list_numerals", "[(1:num); 2; 3]", "[1; 2; 3]"),
  ("show_types.cond", "if (b:bool) then (1:num) else 2", "if (b:bool) then 1 else 2"),
  ("show_types.let", "let (x:num) = 1 in x + 2", "let (x:num) = 1 in (x:num) + 2"),
  ("show_types.real_of_num", "&2", "(& :num->real)2"),
  ("show_types.real_neg", "-- &2", "-- (& :num->real)2"),
  ("show_types.real_of_num.add", "&1 + &2", "(& :num->real)1 + (& :num->real)2")
]


/-- `check label input expected` (printer_tests.ml 20-28). -/
private def check (cases : List (String × String × String)) : IO Unit := do
  for (label, input, expected) in cases do
    let actual ← try
        match ← HolCore.Parser.parse_term input with
        | .ok t => HolCore.Printer.string_of_term t
        | .error e => pure s!"<<parse-fail: {e}>>"
      catch e => pure s!"<<parse-fail: {e}>>"
    IO.println (if actual == expected then s!"printer_tests {label} -> OK"
      else s!"printer_tests {label} -> MISMATCH input `{input}` expected `{expected}` actual `{actual}`")

private unsafe def prioritize (ty : String) : IO Unit := do
  match ← mk_type ty [] with
  | .ok t => prioritize_overload t
  | .error e => throw (IO.userError e)

/-- `check_roundtrip label tm` (printer_tests.ml 302-320). -/
private def checkRoundtrip (label : String) (tm : term) : IO Unit := do
  let ptos := HolCore.Printer.print_types_of_subterms
  let saved ← ptos.get
  ptos.set 2
  let printed ← try HolCore.Printer.string_of_term tm finally ptos.set saved
  match ← HolCore.Parser.parse_term printed with
  | .error e => IO.println s!"printer_tests {label} -> MISMATCH printed `{printed}` parse error: {e}"
  | .ok re =>
    IO.println (if aconv re tm then s!"printer_tests {label} -> OK"
      else s!"printer_tests {label} -> MISMATCH printed `{printed}` reparsed != original")

#eval (do
  -- printer_tests.ml runs in a fully loaded HOL Light: load everything (as
  -- HolInit does), dropping the load's MESON output.
  let sink ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let out := IO.FS.Stream.ofBuffer sink
  let _ ← IO.withStdout out (IO.withStderr out ensureDefine)
  HolCore.Printer.set_margin 1000000
  check seg0
  prioritize "int"
  check seg1
  prioritize_real
  check seg2
  prioritize "num"
  check seg3
  let ptos := HolCore.Printer.print_types_of_subterms
  let savedShowTypes ← ptos.get
  ptos.set 2
  check seg4
  ptos.set savedShowTypes
  let tm (r : Except String term) : IO term := IO.ofExcept r
  let real_of_num_tm ← tm (← HolCore.Kernel.mk_const "real_of_num" [])
  let real_neg_tm ← tm (← HolCore.Kernel.mk_const "real_neg" [])
  let real_add_tm ← tm (← HolCore.Kernel.mk_const "real_add" [])
  let amp_2 ← tm (HolCore.Kernel.mk_comb real_of_num_tm (← tm (mk_numeral 2)))
  let amp_1 ← tm (HolCore.Kernel.mk_comb real_of_num_tm (← tm (mk_numeral 1)))
  checkRoundtrip "roundtrip.real_of_num" amp_2
  checkRoundtrip "roundtrip.real_neg" (← tm (HolCore.Kernel.mk_comb real_neg_tm amp_2))
  checkRoundtrip "roundtrip.real_add" (← tm (do (← HolCore.Basics.mk_binop real_add_tm amp_1) amp_2))
  : IO Unit)

end HolTest.UnitPrinterTest
