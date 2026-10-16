/- File: HolTutorial/LinkingExternalTools.lean
Translation of HOL Light's Tutorial/Linking_external_tools.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

The external program `maxima` is not available here.  As in HOL Light, the
`maximas` call runs a shell pipeline `echo ... | maxima | grep ... | sed ...
>tmpfile` via the shell (translated with `IO.Process`, as HolLibrary/
Pocklington.lean's `factor` runs `gp`).  When `maxima` is missing the shell
prints `sh: maxima: command not found` and the pipeline's final `sed` still
exits 0, so `maximas` reads an EMPTY temp file and HOL Light's `input_line`
raises `End_of_file`; the toplevel prints `Exception: End_of_file.`.  So the
conversions that call `maximas` (FACTOR_CONV, ANTIDERIV_CONV, INTEGRAL_CONV)
fail the same way here.
-/
import HolTutorial.Common
open HolCore.Kernel HolCore.Lib HolCore.Basics HolLight HolLight.Syntax HolTutorial
open Session (prove prioritize_real is_ratconst is_numeral rat_of_term term_of_rat
  lex REAL_RING MESON_TAC NUM_REDUCE_CONV REAL_RAT_REDUCE_CONV
  REAL_MUL_2 REAL_POW_2 NUMERAL BIT0 BIT1 ADD1 REAL_OF_NUM_ADD REAL_ADD_RDISTRIB
  REAL_MUL_LID REAL_MUL_LZERO REAL_MUL_RZERO)
open SessionLibrary.Transc (DIFF_CONV SIN_ADD COS_ADD SIN_CIRCLE FTC1 SIN_0 COS_0)
open HolCore.Parser (parse_term parse_type)
open HolCore.Lib (string_of_num num_of_string)
open HolCore.Printer (get_infix_status isalnum)
open HolCore.Equal (lhand GSYM BETA_RULE)
open HolCore.Simp (convRuleIO thencIO landConvIO)
open HolCore.Tactics (tactic)

namespace HolTutorial.LinkingExternalTools

/-- Print an uncaught `End_of_file`, as HOL Light's toplevel does. -/
def endOfFile : IO Unit := IO.println "Exception: End_of_file."

/-- Print `<fun>`, as the OCaml toplevel prints a function value. -/
def fn : IO Unit := IO.println "<fun>"

/-- OCaml's `isnum` (preterm.ml): a one-character digit string. -/
def isnumc (s : String) : Bool := s.length == 1 && s.front.isDigit

#eval phrase 1
-- needs "Library/transc.ml";;  (loads the real-analysis library; not compared)
#eval SessionLibrary.Transc.ensureTransc

#eval phrase 2
/- let maximas e = ... | maxima | ... -/
unsafe def maximas (e : String) : IO String := do
  -- Filename.temp_file "maxima" ".out"
  let (handle, filename) ← IO.FS.createTempFile
  let _ := handle
  let s :=
    "echo 'linel:10000; display2d:false;" ++ e ++
    ";' | maxima | grep '^(%o3)' | sed -e 's/^(%o3) //' >" ++ filename.toString
  -- Sys.command s : run via the shell (stderr inherited, as HOL Light's).
  let child ← IO.Process.spawn
    { cmd := "sh", args := #["-c", s], stdout := .inherit, stderr := .inherit }
  let code ← child.wait
  if code != 0 then throw (IO.userError "maxima")   -- failwith "maxima"
  else
    -- open_in; input_line; close_in; Sys.remove.  An empty file -> End_of_file.
    let data ← IO.FS.readFile filename
    IO.FS.removeFile filename
    match (data.splitOn "\n").head? with
    | some line => if data.isEmpty then throw (IO.userError "End_of_file") else pure line
    | none => throw (IO.userError "End_of_file")
#eval fn

#eval phrase 3
#eval prioritize_real

#eval phrase 4
unsafe def maxima_ops : List (String × term) :=
  keep "maxima_ops" fun _ =>
    [("+", ([[(+)]] : term)), ("-", [[(-)]]), ("*", [[( * )]]),
     ("/", [[(/)]]), ("^", [[(pow)]])]
#eval IO.println ("[" ++ String.intercalate "; "
  (maxima_ops.map (fun p => "(\"" ++ p.1 ++ "\", `" ++ toString p.2 ++ "`)")) ++ "]")

#eval phrase 5
unsafe def maxima_funs : List (String × term) :=
  keep "maxima_funs" fun _ => [("sin", ([[sin]] : term)), ("cos", [[cos]])]
#eval IO.println ("[" ++ String.intercalate "; "
  (maxima_funs.map (fun p => "(\"" ++ p.1 ++ "\", `" ++ toString p.2 ++ "`)")) ++ "]")

#eval phrase 6
/- let mk_uneg = curry mk_comb `(--)` -/
unsafe def mk_uneg (t : term) : term := (mk_comb ([[(--)]] : term) t).toOption.get!
#eval fn

#eval phrase 7
/- let dest_uneg = let ntm = `(--)` in fun tm -> ... -/
unsafe def dest_uneg (tm : term) : Except String term :=
  match dest_comb tm with
  | .ok (op, t) => if op == ([[(--)]] : term) then .ok t else .error "dest_uneg"
  | .error e => .error e
#eval fn

#eval phrase 8
/- let mk_pow = let f = mk_binop `(pow)` in fun x y -> f x (rand y) -/
unsafe def mk_pow (x y : term) : term :=
  ((mk_binop ([[(pow)]] : term) x).toOption.get! ((rand y).toOption.get!)).toOption.get!
#eval fn

#eval phrase 9
/- let mk_realvar = let real_ty = `:real` in fun x -> mk_var(x,real_ty) -/
unsafe def realTy : hol_type := ((unsafeIO (parse_type "real")).toOption.get!).toOption.get!
unsafe def mk_realvar (x : String) : term := mk_var x realTy
#eval fn

/-- OCaml's `string_of_num` on a rational: `n` or `n/d`. -/
def strOfNum (r : Rat) : String :=
  if r.den == 1 then toString r.num else toString r.num ++ "/" ++ toString r.den

#eval phrase 10
/- let rec string_of_hol tm = ... -/
unsafe def string_of_hol (tm : term) : String :=
  if is_ratconst tm then "(" ++ strOfNum ((rat_of_term tm).toOption.get!) ++ ")"
  else if is_numeral tm then strOfNum ((dest_numeral tm).toOption.get!)
  else if is_var tm then (dest_var tm).toOption.get!.1
  else if (can dest_uneg tm) then "-(" ++ string_of_hol ((rand tm).toOption.get!) ++ ")"
  else
    match dest_comb tm with
    | .error _ => "?"
    | .ok (lop, r) =>
      match dest_comb lop with
      | .ok (op, l) =>
        "(" ++ string_of_hol l ++ " " ++ (rev_assoc op maxima_ops).toOption.get! ++ " " ++ string_of_hol r ++ ")"
      | .error _ => (rev_assoc lop maxima_funs).toOption.get! ++ "(" ++ string_of_hol r ++ ")"
#eval fn

#eval phrase 11
#eval IO.println s!"\"{string_of_hol [[(x + sin(-- &2 * x)) pow 2 - cos(x - &22 / &7)]]}\""

#eval phrase 12
/- let lexe s = map (function Resword s -> s | Ident s -> s) (lex(explode s)) -/
unsafe def lexe (s : String) : List String :=
  (((unsafeIO (lex (explode s))).toOption.get!).toOption.get!).map (fun t =>
    match t with
    | .Resword s => s
    | .Ident s => s)
#eval fn

#eval phrase 13
/- let parse_bracketed prs inp = match prs inp with ast,")"::rst -> ast,rst
   | _ -> failwith "Closing bracket expected" -/
unsafe def parse_bracketed {α : Type} (prs : List String → Except String (α × List String))
    (inp : List String) : Except String (α × List String) := do
  match ← prs inp with
  | (ast, ")" :: rst) => .ok (ast, rst)
  | _ => .error "Closing bracket expected"
#eval fn

#eval phrase 14
/- let rec parse_ginfix op opup sof prs inp = ... -/
unsafe def parse_ginfix {α β γ : Type} [BEq α]
    (op : α) (opup : (β → γ) → β → β → γ) (sof : β → γ)
    (prs : List α → Except String (β × List α)) (inp : List α) :
    Except String (γ × List α) := do
  match ← prs inp with
  | (e1, hop :: rst) =>
    if hop == op then parse_ginfix op opup (opup sof e1) prs rst
    else .ok (sof e1, hop :: rst)
  | (e1, rest) => .ok (sof e1, rest)
#eval fn

#eval phrase 15
/- let parse_general_infix op = ... -/
unsafe def parse_general_infix (op : String)
    (prs : List String → Except String (term × List String)) (inp : List String) :
    Except String (term × List String) :=
  let opcon : term → term → term :=
    if op == "^" then mk_pow
    else fun e1 e2 => ((mk_binop ((assoc op maxima_ops).toOption.get!) e1).toOption.get! e2).toOption.get!
  let constr : (term → term) → term → term → term :=
    if op != "^" && (((unsafeIO (get_infix_status op)).toOption.get!).toOption.get!.2 == "right")
    then fun f e1 e2 => f (opcon e1 e2)
    else fun f e1 e2 => opcon (f e1) e2
  parse_ginfix op constr (fun x => x) prs inp
#eval fn

#eval phrase 16
/- let rec parse_atomic_expression inp = ... and parse_exp ... and parse_neg ...
   and parse_expression ... -/
mutual
unsafe def parse_atomic_expression (inp : List String) :
    Except String (term × List String) := do
  match inp with
  | [] => .error "expression expected"
  | "(" :: rest => parse_bracketed parse_expression rest
  | s :: rest =>
    if (explode s).all isnumc then
      .ok ((term_of_rat ((num_of_string s).toOption.get!)).toOption.get!, rest)
    else
      match rest with
      | "(" :: rest2 =>
        if (explode s).all isalnum then do
          let (e, rst) ← parse_bracketed parse_expression rest2
          .ok ((mk_comb ((assoc s maxima_funs).toOption.get!) e).toOption.get!, rst)
        else if (explode s).all isalnum then .ok (mk_realvar s, rest)
        else .error "expression expected"
      | _ =>
        if (explode s).all isalnum then .ok (mk_realvar s, rest)
        else .error "expression expected"
unsafe def parse_exp (inp : List String) : Except String (term × List String) :=
  parse_general_infix "^" parse_atomic_expression inp
unsafe def parse_neg (inp : List String) : Except String (term × List String) := do
  match inp with
  | "-" :: rest => do let (e, rst) ← parse_neg rest; .ok (mk_uneg e, rst)
  | _ => parse_exp inp
unsafe def parse_expression (inp : List String) :
    Except String (term × List String) :=
  itlist parse_general_infix (maxima_ops.map Prod.fst) parse_neg inp
end
#eval do fn; fn; fn; fn

#eval phrase 17
/- let hol_of_string = fst o parse_expression o lexe -/
unsafe def hol_of_string (s : String) : term :=
  ((parse_expression (lexe s)).toOption.get!).1
#eval fn

#eval phrase 18
#eval IO.println ("`" ++ toString (hol_of_string "sin(x) - cos(-(- - 1 + x))") ++ "`")

/-- `mk_eq (l, r)`, as a one-shot wrapper over the core two-stage `mk_eq`. -/
unsafe def mkEq (l r : term) : term :=
  (((unsafeIO mk_eq).toOption.get!).toOption.get! (l, r)).toOption.get!

/-- Run a `maximas`-calling conversion.  Because `maxima` is absent the shell
    prints `sh: maxima: command not found`, `maximas` reads an empty file and
    raises `End_of_file`, and (as HOL Light's toplevel does) we print
    `Exception: End_of_file.`. -/
unsafe def runMaxima {α : Type} (x : IO α) : IO Unit := do
  try let _ ← x; pure () catch _ => endOfFile

#eval phrase 19
/- let FACTOR_CONV tm = ... REAL_RING(mk_eq(tm,tm')) -/
unsafe def FACTOR_CONV (tm : term) : IO thm := do
  let s := "factor(" ++ string_of_hol tm ++ ")"
  let tm' := hol_of_string (← maximas s)
  match ← REAL_RING (mkEq tm tm') with
  | .ok th => pure th
  | .error e => throw (IO.userError e)
#eval fn

#eval phrase 20
#eval runMaxima (FACTOR_CONV [[&1234567890]])

#eval phrase 21
#eval runMaxima (FACTOR_CONV [[x pow 6 - &1]])

#eval phrase 22
#eval runMaxima (FACTOR_CONV [[r * (r * x * (&1 - x)) * (&1 - r * x * (&1 - x)) - x]])

#eval phrase 23
/- let ANTIDERIV_CONV tm = ... (integrate ...) -/
unsafe def ANTIDERIV_CONV (tm : term) : IO thm := do
  let (x, bod) ← IO.ofExcept (dest_abs tm)
  let s := "integrate(" ++ string_of_hol bod ++ "," ++ (dest_var x).toOption.get!.1 ++ ")"
  let tm' := (mk_abs x (hol_of_string (← maximas s))).toOption.get!
  let th1 ← IO.ofExcept (← convRuleIO (thencIO NUM_REDUCE_CONV REAL_RAT_REDUCE_CONV)
                           (← IO.ofExcept (Session.SPEC x (← IO.ofExcept (← DIFF_CONV tm')))))
  let th2 ← IO.ofExcept (← REAL_RING (mkEq ((lhand (concl th1)).toOption.get!) bod))
  IO.ofExcept (Session.GEN x (← IO.ofExcept (← Session.GEN_REWRITE_RULE landConvIO [th2] th1)))
#eval fn

#eval phrase 24
#eval runMaxima (ANTIDERIV_CONV [[\x. (x + &5) pow 2 + &77 * x]])

#eval phrase 25
#eval runMaxima (ANTIDERIV_CONV [[\x. sin(x) + x pow 11]])

#eval phrase 26
/- (**** This one fails as expected so we need more simplification later
   ANTIDERIV_CONV `\x. sin(x) pow 3`;;  ****) -/
unsafe def SIN_N_CLAUSES : thm := keep "SIN_N_CLAUSES" fun _ => prove
 ([[(sin(&(NUMERAL(BIT0 n)) * x) =
     &2 * sin(&(NUMERAL n) * x) * cos(&(NUMERAL n) * x)) /\
    (sin(&(NUMERAL(BIT1 n)) * x) =
         sin(&(NUMERAL(BIT0 n)) * x) * cos(x) +
         sin(x) * cos(&(NUMERAL(BIT0 n)) * x)) /\
    (cos(&(NUMERAL(BIT0 n)) * x) =
         cos(&(NUMERAL n) * x) pow 2 - sin(&(NUMERAL n) * x) pow 2) /\
    (cos(&(NUMERAL(BIT1 n)) * x) =
         cos(&(NUMERAL(BIT0 n)) * x) * cos(x) -
         sin(x) * sin(&(NUMERAL(BIT0 n)) * x))]])
  (REWRITE_TAC [REAL_MUL_2, REAL_POW_2] THEN
   REWRITE_TAC [NUMERAL, BIT0, BIT1] THEN
   REWRITE_TAC [ADD1, (GSYM REAL_OF_NUM_ADD : Except String thm)] THEN
   REWRITE_TAC [REAL_ADD_RDISTRIB, SIN_ADD, COS_ADD, REAL_MUL_LID] THEN
   CONV_TAC REAL_RING)
#eval SIN_N_CLAUSES

#eval phrase 27
/- let TRIG_IDENT_TAC x = ... -/
unsafe def TRIG_IDENT_TAC (x : term) : tactic :=
  REWRITE_TAC [SIN_N_CLAUSES, SIN_ADD, COS_ADD] THEN
  REWRITE_TAC [REAL_MUL_LZERO, SIN_0, COS_0, REAL_MUL_RZERO] THEN
  MP_TAC (Session.SPEC x SIN_CIRCLE) THEN CONV_TAC REAL_RING
#eval fn

#eval phrase 28
/- let ANTIDERIV_CONV tm = ... expand(integrate ...) ... TRIG_IDENT_TAC x -/
unsafe def ANTIDERIV_CONV_2 (tm : term) : IO thm := do
  let (x, bod) ← IO.ofExcept (dest_abs tm)
  let s := "expand(integrate(" ++ string_of_hol bod ++ "," ++ (dest_var x).toOption.get!.1 ++ "))"
  let tm' := (mk_abs x (hol_of_string (← maximas s))).toOption.get!
  let th1 ← IO.ofExcept (← convRuleIO (thencIO NUM_REDUCE_CONV REAL_RAT_REDUCE_CONV)
                           (← IO.ofExcept (Session.SPEC x (← IO.ofExcept (← DIFF_CONV tm')))))
  let th2 ← IO.ofExcept (← prove (mkEq ((lhand (concl th1)).toOption.get!) bod) (TRIG_IDENT_TAC x))
  IO.ofExcept (Session.GEN x (← IO.ofExcept (← Session.GEN_REWRITE_RULE landConvIO [th2] th1)))
#eval fn

#eval phrase 29
#eval runMaxima (HolCore.Lib.time ANTIDERIV_CONV_2 [[\x. sin(x) pow 3]])

#eval phrase 30
#eval runMaxima (HolCore.Lib.time ANTIDERIV_CONV_2 [[\x. sin(x) * sin(x) pow 5 * cos(x) pow 4 + cos(x)]])

#eval phrase 31
/- let FCT1_WEAK = prove(...) -/
unsafe def FCT1_WEAK : thm := keep "FCT1_WEAK" fun _ => prove
 ([[(!x. (f diffl f'(x)) x) ==> !x. &0 <= x ==> defint(&0,x) f' (f x - f(&0))]])
  (MESON_TAC [FTC1])
#eval FCT1_WEAK

#eval phrase 32
/- let INTEGRAL_CONV tm = ... MATCH_MP FCT1_WEAK (ANTIDERIV_CONV tm) ... -/
unsafe def INTEGRAL_CONV (tm : term) : IO thm := do
  let th1 ← IO.ofExcept (← Session.MATCH_MP FCT1_WEAK (← ANTIDERIV_CONV_2 tm))
  let r1 ← IO.ofExcept (BETA_RULE th1)
  let r2 ← IO.ofExcept (← convRuleIO REAL_RAT_REDUCE_CONV r1)
  let r3 ← IO.ofExcept (← Session.REWRITE_RULE [SIN_0, COS_0, REAL_MUL_LZERO, REAL_MUL_RZERO] r2)
  IO.ofExcept (← convRuleIO REAL_RAT_REDUCE_CONV r3)
#eval fn

#eval phrase 33
#eval runMaxima (INTEGRAL_CONV [[\x. sin(x) pow 13]])

/- Remaining tools/tutorialdiff differences (all unavoidable, not translation
   errors): P14/P15/P16 — OCaml's toplevel prints a line-wrapped polymorphic
   type signature that compare.py's `val x : ty =` normaliser cannot strip (its
   regex needs the type on the same line as `val name :`); Lean prints `<fun>`.
   P29/P30 — the `time` combinator's failure line `Failed after (user) CPU time
   of N: End_of_file` carries a nondeterministic CPU time that compare.py masks
   only in the success form `CPU time (user): N`, so the number (and s-vs-ns
   unit) always differs; every other character of those lines matches. -/

end HolTutorial.LinkingExternalTools
