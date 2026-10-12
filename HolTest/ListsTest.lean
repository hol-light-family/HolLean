/- File: HolTest/ListsTest.lean
Runtime test suite: lists.ml - theory of lists, characters and strings.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

FAITHFULNESS BASIS.  The conversion and syntax expectations below are taken
VERBATIM from HOL Light's own reference documentation, which ships worked
examples with real OCaml output:
  * hol-light/Help/LENGTH_CONV.hlp    * hol-light/Help/EL_CONV.hlp
  * hol-light/Help/REVERSE_CONV.hlp   * hol-light/Help/LIST_CONV.hlp
  * hol-light/Help/CHAR_EQ_CONV.hlp   * hol-light/Help/STRING_EQ_CONV.hlp
  * hol-light/Help/mk_flist.hlp
A mismatch on those is therefore a genuine divergence from HOL Light, not a
disagreement with this translator's guesses.  The definition and theorem
statements are checked against lists.ml itself. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- FORCING THE LISTS LAYER FIRST IS MANDATORY.                            -/
/-                                                                        -/
/- The list constants (LENGTH, CONS, NIL, APPEND, ...) are declared by     -/
/- `setupListDefs`, which runs lazily.  A term parsed BEFORE that happens  -/
/- gets `LENGTH` as a free VARIABLE, not a constant - measured directly:   -/
/-   BEFORE forcing: head is_const=false is_var=true                       -/
/-   AFTER  forcing: head is_const=true  is_var=false                      -/
/- Every conversion below matches on `.Const "LENGTH"` etc., so an         -/
/- unforced parse makes them all fail with their generic error.  This is   -/
/- the same defect class as the `(DIV)` quotation in calc_num.ml.  Forcing -/
/- `listDefs.LENGTH` here declares the constants before anything parses.   -/
/- ---------------------------------------------------------------------- -/

#eval Session.listDefs.LENGTH

/-- Strip newlines and spaces so a wrapped pretty-printed theorem can be
    compared against a single-line expected string. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

/-- Compare a theorem against an expected printed form. -/
private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/-- Parse `expr`, apply the `ioconv`, compare the resulting theorem. -/
private unsafe def convCheck (lbl expr expected : String) (c : ioconv) : IO Unit := do
  match ← HolCore.Parser.parse_term expr with
  | .error e => IO.println s!"{lbl} parse ERR: {e}"
  | .ok tm =>
    match ← c tm with
    | .error e => IO.println s!"{lbl} ERR: {e}"
    | .ok th =>
      let got := squash (← HolCore.Printer.string_of_thm th)
      if got == squash expected then IO.println s!"{lbl} -> OK"
      else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- The recursive definitions (lists.ml 28-143).                           -/
/-                                                                        -/
/- Note THREE of these use `num_RECURSION` rather than `list_RECURSION`:  -/
/- REPLICATE, EL and list_of_seq.  The four `_DEF`/derived pairs (ALL2,   -/
/- MAP2, ITLIST2, ZIP) are checked in their DERIVED form, which is the     -/
/- two/four-clause version the rest of HOL Light consumes.                -/
/-                                                                        -/
/- QUANTIFIERS: some definitions carry leading `!`s and some do not, and   -/
/- that follows the OCaml SOURCE TEXT rather than any rule.  APPEND and    -/
/- MAP are written `(!l. ...) /\ (!h t l. ...)` and so come out           -/
/- quantified; REVERSE, NULL, ALL, EX, MEM and FILTER are written with     -/
/- their variables FREE and so come out unquantified.  These expectations  -/
/- were checked line by line against lists.ml - an earlier draft of this   -/
/- file wrongly added `!`s to those six and they failed, which is exactly  -/
/- the check working.                                                      -/
/- ---------------------------------------------------------------------- -/

#eval thmCheck "def HD" listDefs.HD "|- HD (CONS h t) = h"
#eval thmCheck "def TL" listDefs.TL "|- TL (CONS h t) = t"
#eval thmCheck "def APPEND" listDefs.APPEND
  "|- (forall l. APPEND [] l = l) /\\ (forall h t l. APPEND (CONS h t) l = CONS h (APPEND t l))"
#eval thmCheck "def REVERSE" listDefs.REVERSE
  "|- REVERSE [] = [] /\\ REVERSE (CONS x l) = APPEND (REVERSE l) [x]"
#eval thmCheck "def LENGTH" listDefs.LENGTH
  "|- LENGTH [] = 0 /\\ (forall h t. LENGTH (CONS h t) = SUC (LENGTH t))"
#eval thmCheck "def MAP" listDefs.MAP
  "|- (forall f. MAP f [] = []) /\\ (forall f h t. MAP f (CONS h t) = CONS (f h) (MAP f t))"
#eval thmCheck "def NULL" listDefs.NULL
  "|- (NULL [] <=> true) /\\ (NULL (CONS h t) <=> false)"
#eval thmCheck "def ALL" listDefs.ALL
  "|- (ALL P [] <=> true) /\\ (ALL P (CONS h t) <=> P h /\\ ALL P t)"
#eval thmCheck "def EX" listDefs.EX
  "|- (EX P [] <=> false) /\\ (EX P (CONS h t) <=> P h \\/ EX P t)"
#eval thmCheck "def MEM" listDefs.MEM
  "|- (MEM x [] <=> false) /\\ (MEM x (CONS h t) <=> x = h \\/ MEM x t)"
#eval thmCheck "def FILTER" listDefs.FILTER
  "|- FILTER P [] = [] /\\ FILTER P (CONS h t) = (if P h then CONS h (FILTER P t) else FILTER P t)"
-- num_RECURSION cases
#eval thmCheck "def REPLICATE (num_RECURSION)" listDefs.REPLICATE
  "|- REPLICATE 0 x = [] /\\ REPLICATE (SUC n) x = CONS x (REPLICATE n x)"
#eval thmCheck "def EL (num_RECURSION)" listDefs.EL
  "|- EL 0 l = HD l /\\ EL (SUC n) l = EL n (TL l)"
#eval thmCheck "def list_of_seq (num_RECURSION)" listDefs.list_of_seq
  "|- list_of_seq s 0 = [] /\\ list_of_seq s (SUC n) = APPEND (list_of_seq s n) [s n]"
-- derived forms of the four _DEF pairs
#eval thmCheck "def ALL2 (derived)" listDefs.ALL2
  "|- (ALL2 P [] [] <=> true) /\\ (ALL2 P (CONS h1 t1) [] <=> false) /\\ (ALL2 P [] (CONS h2 t2) <=> false) /\\ (ALL2 P (CONS h1 t1) (CONS h2 t2) <=> P h1 h2 /\\ ALL2 P t1 t2)"
#eval thmCheck "def MAP2 (derived)" listDefs.MAP2
  "|- MAP2 f [] [] = [] /\\ MAP2 f (CONS h1 t1) (CONS h2 t2) = CONS (f h1 h2) (MAP2 f t1 t2)"
#eval thmCheck "def ITLIST2 (derived)" listDefs.ITLIST2
  "|- ITLIST2 f [] [] b = b /\\ ITLIST2 f (CONS h1 t1) (CONS h2 t2) b = f h1 h2 (ITLIST2 f t1 t2 b)"
#eval thmCheck "def ZIP (derived)" listDefs.ZIP
  "|- ZIP [] [] = [] /\\ ZIP (CONS h1 t1) (CONS h2 t2) = CONS (h1,h2) (ZIP t1 t2)"
#eval thmCheck "def PAIRWISE" listDefs.PAIRWISE
  "|- (PAIRWISE r [] <=> true) /\\ (PAIRWISE r (CONS h t) <=> ALL (r h) t /\\ PAIRWISE r t)"

/- ---------------------------------------------------------------------- -/
/- Representative theorems (lists.ml 148-697), spanning both halves.      -/
/- ---------------------------------------------------------------------- -/

#eval thmCheck "NOT_CONS_NIL" listThms1.NOT_CONS_NIL "|- forall h t. ~(CONS h t = [])"
#eval thmCheck "APPEND_NIL" listThms1.APPEND_NIL "|- forall l. APPEND l [] = l"
#eval thmCheck "APPEND_ASSOC" listThms1.APPEND_ASSOC
  "|- forall l m n. APPEND l (APPEND m n) = APPEND (APPEND l m) n"
#eval thmCheck "REVERSE_REVERSE" listThms1.REVERSE_REVERSE "|- forall l. REVERSE (REVERSE l) = l"
#eval thmCheck "CONS_11" listThms1.CONS_11
  "|- forall h1 h2 t1 t2. CONS h1 t1 = CONS h2 t2 <=> h1 = h2 /\\ t1 = t2"
#eval thmCheck "list_CASES" listThms1.list_CASES "|- forall l. l = [] \\/ (exists h t. l = CONS h t)"
#eval thmCheck "LENGTH_APPEND" listThms1.LENGTH_APPEND
  "|- forall l m. LENGTH (APPEND l m) = LENGTH l + LENGTH m"
#eval thmCheck "MAP_o" listThms1.MAP_o "|- forall f g l. MAP (g o f) l = MAP g (MAP f l)"
#eval thmCheck "MEM_APPEND" listThms1.MEM_APPEND
  "|- forall x l1 l2. MEM x (APPEND l1 l2) <=> MEM x l1 \\/ MEM x l2"
#eval thmCheck "LENGTH_MAP" listThms1.LENGTH_MAP "|- forall l f. LENGTH (MAP f l) = LENGTH l"
#eval thmCheck "LENGTH_EQ_NIL" listThms1.LENGTH_EQ_NIL "|- forall l. LENGTH l = 0 <=> l = []"
-- part 2
#eval thmCheck "ALL_APPEND" listThms2.ALL_APPEND
  "|- forall P l1 l2. ALL P (APPEND l1 l2) <=> ALL P l1 /\\ ALL P l2"
#eval thmCheck "APPEND_EQ_NIL" listThms2.APPEND_EQ_NIL
  "|- forall l m. APPEND l m = [] <=> l = [] /\\ m = []"
#eval thmCheck "MAP_ID" listThms2.MAP_ID "|- forall l. MAP (\\x. x) l = l"
#eval thmCheck "MAP_REVERSE" listThms2.MAP_REVERSE
  "|- forall f l. REVERSE (MAP f l) = MAP f (REVERSE l)"
#eval thmCheck "CONS_HD_TL" listThms2.CONS_HD_TL
  "|- forall l. ~(l = []) ==> l = CONS (HD l) (TL l)"

/- ---------------------------------------------------------------------- -/
/- The two extra monotonicity theorems (lists.ml 722-731) and their       -/
/- REGISTRATION (line 733).                                               -/
/-                                                                        -/
/- The registration is the point: `monotonicity_theorems :=               -/
/- [MONO_ALL; MONO_ALL2] @ !monotonicity_theorems` PREPENDS both, and     -/
/- MONO_TAC re-reads that list on every use.  A frozen snapshot would     -/
/- silently lose them - the defect class that once lost MONO_COND.         -/
/- ---------------------------------------------------------------------- -/

#eval thmCheck "MONO_ALL" MONO_ALL "|- (forall x. P x ==> Q x) ==> ALL P l ==> ALL Q l"
#eval thmCheck "MONO_ALL2" MONO_ALL2
  "|- (forall x y. P x y ==> Q x y) ==> ALL2 P l l' ==> ALL2 Q l l'"

#eval (do
  let _ ← IO.mkRef (concl Session.MONO_ALL)
  let l := (← Session.theMonotonicityTheorems.get).getD []
  let concls ← l.mapM (fun t => do return squash (← HolCore.Printer.string_of_thm t))
  let hasAll := concls.any (fun s => s == squash "|- (forall x. P x ==> Q x) ==> ALL P l ==> ALL Q l")
  let hasAll2 := concls.any (fun s =>
    s == squash "|- (forall x y. P x y ==> Q x y) ==> ALL2 P l l' ==> ALL2 Q l l'")
  if hasAll && hasAll2 then
    IO.println s!"monotonicity registration -> OK ({l.length} theorems)"
  else
    IO.println s!"monotonicity registration -> MISMATCH ALL={hasAll} ALL2={hasAll2}" : IO Unit)

/- ---------------------------------------------------------------------- -/
/- The four evaluation conversions (lists.ml 751-876).                    -/
/- Expected values from Help/LENGTH_CONV.hlp, Help/EL_CONV.hlp and        -/
/- Help/REVERSE_CONV.hlp - the documented examples, verbatim.             -/
/-                                                                        -/
/- Each is also exercised on a LONGER list.  These are the "efficient     -/
/- tail-recursive" versions, and a nesting error can be invisible on      -/
/- short input - exactly how the calc_num Toom-3 bug hid.                 -/
/- ---------------------------------------------------------------------- -/

-- Help/LENGTH_CONV.hlp
#eval convCheck "LENGTH_CONV doc" "LENGTH [1;2;3;4;5]"
  "|- LENGTH [1; 2; 3; 4; 5] = 5" LENGTH_CONV
#eval convCheck "LENGTH_CONV len1" "LENGTH [1]" "|- LENGTH [1] = 1" LENGTH_CONV
#eval convCheck "LENGTH_CONV len10" "LENGTH [1;2;3;4;5;6;7;8;9;10]"
  "|- LENGTH [1; 2; 3; 4; 5; 6; 7; 8; 9; 10] = 10" LENGTH_CONV

-- Help/EL_CONV.hlp
#eval convCheck "EL_CONV doc last" "EL 4 [1;2;3;4;5]" "|- EL 4 [1; 2; 3; 4; 5] = 5" EL_CONV
#eval convCheck "EL_CONV head" "EL 0 [7;8;9]" "|- EL 0 [7; 8; 9] = 7" EL_CONV
#eval convCheck "EL_CONV mid long" "EL 5 [10;20;30;40;50;60;70;80]"
  "|- EL 5 [10; 20; 30; 40; 50; 60; 70; 80] = 60" EL_CONV

-- Help/REVERSE_CONV.hlp
#eval convCheck "REVERSE_CONV doc" "REVERSE [1;2;3]"
  "|- REVERSE [1; 2; 3] = [3; 2; 1]" REVERSE_CONV
#eval convCheck "REVERSE_CONV len1" "REVERSE [1]" "|- REVERSE [1] = [1]" REVERSE_CONV
#eval convCheck "REVERSE_CONV len8" "REVERSE [1;2;3;4;5;6;7;8]"
  "|- REVERSE [1; 2; 3; 4; 5; 6; 7; 8] = [8; 7; 6; 5; 4; 3; 2; 1]" REVERSE_CONV

-- LIST_OF_SEQ_CONV
#eval convCheck "LIST_OF_SEQ_CONV 3" "list_of_seq (\\n. n + 1) 3"
  "|- list_of_seq (\\n. n + 1) 3 = [0 + 1; 1 + 1; 2 + 1]" LIST_OF_SEQ_CONV

/- ---------------------------------------------------------------------- -/
/- LIST_CONV (lists.ml 740-746): apply a conversion down a list.          -/
/- Expected value from Help/LIST_CONV.hlp, verbatim.                      -/
/- ---------------------------------------------------------------------- -/

#eval (do
  match ← HolCore.Parser.parse_term "[1;2;3;4;5]" with
  | .error e => IO.println s!"LIST_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.LIST_CONV_IO Session.num_CONV tm with
    | .error e => IO.println s!"LIST_CONV ERR: {e}"
    | .ok th =>
      let got := squash (← HolCore.Printer.string_of_thm th)
      let exp := squash "|- [1; 2; 3; 4; 5] = [SUC 0; SUC 1; SUC 2; SUC 3; SUC 4]"
      if got == exp then IO.println "LIST_CONV doc -> OK"
      else IO.println s!"LIST_CONV doc -> MISMATCH got={got}" : IO Unit)

/- ---------------------------------------------------------------------- -/
/- Syntax constructors (lists.ml 702-717).                                -/
/- `mk_flist` expectation from Help/mk_flist.hlp, verbatim.               -/
/- ---------------------------------------------------------------------- -/

#eval (do
  -- Help/mk_flist.hlp: mk_flist(map mk_small_numeral (1--10))
  let nums ← (List.range 10).mapM (fun i => do
    match Session.mk_small_numeral (Int.ofNat (i + 1)) with
    | .ok t => return t
    | .error _ => return (default : term))
  match ← Session.mk_flist nums with
  | .error e => IO.println s!"mk_flist ERR: {e}"
  | .ok t =>
    let got := squash (← HolCore.Printer.string_of_term t)
    let exp := squash "[1; 2; 3; 4; 5; 6; 7; 8; 9; 10]"
    if got == exp then IO.println "mk_flist doc -> OK"
    else IO.println s!"mk_flist doc -> MISMATCH got={got}" : IO Unit)

-- `mk_flist []` must FAIL (the OCaml's `hd []` raises, normalised to "mk_flist").
#eval (do
  match ← Session.mk_flist [] with
  | .ok _ => IO.println "mk_flist [] -> MISMATCH: expected failure"
  | .error e =>
    if e == "mk_flist" then IO.println "mk_flist [] -> OK"
    else IO.println s!"mk_flist [] -> MISMATCH got={e}" : IO Unit)

/- ---------------------------------------------------------------------- -/
/- The char type and string machinery (lists.ml 877-998).                 -/
/-                                                                        -/
/- `char_INDUCT`/`char_RECURSION` come from `define_type` on an EIGHT-    -/
/- argument constructor, so these also exercise the ind_types.ml          -/
/- translation end to end from a different file.                          -/
/-                                                                        -/
/- The round-trips are the evidence that `code_of_term`'s bit order is    -/
/- right: it folds over `map bool_of_term (rev tms)`, and reversing that  -/
/- would silently map every character to the wrong code.                  -/
/- ---------------------------------------------------------------------- -/

#eval thmCheck "char_INDUCT" char_INDUCT
  "|- forall P. (forall a0 a1 a2 a3 a4 a5 a6 a7. P (ASCII a0 a1 a2 a3 a4 a5 a6 a7)) ==> (forall x. P x)"
#eval thmCheck "char_RECURSION" char_RECURSION
  "|- forall f. exists fn. forall a0 a1 a2 a3 a4 a5 a6 a7. fn (ASCII a0 a1 a2 a3 a4 a5 a6 a7) = f a0 a1 a2 a3 a4 a5 a6 a7"

/-- Round-trip a character through `mk_char`/`dest_char` and check the code. -/
private unsafe def charRoundTrip (c : Char) : IO Unit := do
  match Session.mk_char c with
  | .error e => IO.println s!"char {c} mk ERR: {e}"
  | .ok t =>
    match Session.dest_char t with
    | .error e => IO.println s!"char {c} dest ERR: {e}"
    | .ok c' =>
      if c == c' then IO.println s!"char roundtrip {c} (code {c.toNat}) -> OK"
      else IO.println s!"char roundtrip {c} -> MISMATCH got={c'}"

#eval charRoundTrip 'A'   -- 65
#eval charRoundTrip 'a'   -- 97
#eval charRoundTrip '0'   -- 48
#eval charRoundTrip '!'   -- 33
#eval charRoundTrip '~'   -- 126
#eval charRoundTrip ' '   -- 32

-- Help/CHAR_EQ_CONV.hlp shows mk_char 'A' printing as `ASCII F T F F F F F T`.
#eval (do
  match Session.mk_char 'A' with
  | .error e => IO.println s!"mk_char A ERR: {e}"
  | .ok t =>
    let got := squash (← HolCore.Printer.string_of_term t)
    let exp := squash "ASCII false true false false false false false true"
    if got == exp then IO.println "mk_char A bit pattern -> OK"
    else IO.println s!"mk_char A bit pattern -> MISMATCH got={got}" : IO Unit)

/-- Round-trip a string through `mk_string`/`dest_string`. -/
private unsafe def stringRoundTrip (s : String) : IO Unit := do
  match ← Session.mk_string s with
  | .error e => IO.println s!"string {s} mk ERR: {e}"
  | .ok t =>
    match Session.dest_string t with
    | .error e => IO.println s!"string {s} dest ERR: {e}"
    | .ok s' =>
      if s == s' then IO.println s!"string roundtrip \"{s}\" -> OK"
      else IO.println s!"string roundtrip \"{s}\" -> MISMATCH got=\"{s'}\""

#eval stringRoundTrip "hello"
#eval stringRoundTrip ""
#eval stringRoundTrip "The quick brown fox!"

/- ---------------------------------------------------------------------- -/
/- CHAR_EQ_CONV / STRING_EQ_CONV, both directions.                        -/
/- Expected values from Help/CHAR_EQ_CONV.hlp and Help/STRING_EQ_CONV.hlp. -/
/- ---------------------------------------------------------------------- -/

#eval (do
  -- Help/CHAR_EQ_CONV.hlp: mk_eq(mk_char 'A', mk_char 'A') -> ... <=> T
  match Session.mk_char 'A', Session.mk_char 'B' with
  | .ok a, .ok b =>
    let chk (lbl : String) (l r : term) (expTail : String) : IO Unit := do
      let eqt := HolCore.Kernel.safe_mk_eq l r
        match Session.CHAR_EQ_CONV eqt with
        | .error e => IO.println s!"{lbl} ERR: {e}"
        | .ok th =>
          let got := squash (← HolCore.Printer.string_of_thm th)
          if got.endsWith (squash expTail) then IO.println s!"{lbl} -> OK"
          else IO.println s!"{lbl} -> MISMATCH got={got}"
    chk "CHAR_EQ_CONV A=A" a a "<=> true"
    chk "CHAR_EQ_CONV A=B" a b "<=> false"
  | _, _ => IO.println "CHAR_EQ_CONV setup failed" : IO Unit)

#eval (do
  let chk (lbl s1 s2 expTail : String) : IO Unit := do
    match ← Session.mk_string s1, ← Session.mk_string s2 with
    | .ok l, .ok r =>
      let eqt := HolCore.Kernel.safe_mk_eq l r
        match Session.STRING_EQ_CONV eqt with
        | .error e => IO.println s!"{lbl} ERR: {e}"
        | .ok th =>
          let got := squash (← HolCore.Printer.string_of_thm th)
          if got.endsWith (squash expTail) then IO.println s!"{lbl} -> OK"
          else IO.println s!"{lbl} -> MISMATCH got={got}"
    | _, _ => IO.println s!"{lbl} setup failed"
  -- Help/STRING_EQ_CONV.hlp
  chk "STRING_EQ_CONV same" "same" "same" "<=> true"
  chk "STRING_EQ_CONV knowledge/power" "knowledge" "power" "<=> false" : IO Unit)
