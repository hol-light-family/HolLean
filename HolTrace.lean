/- File: HolTrace.lean
Library root and command line for the HOLTrace proof reconstructor.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

HOLTrace (https://holtrace.cr.yp.to) is a file format recording a sequence of
HOL Light proofs and theorems: a few hundred megabytes of trace can hold every
inference HOL Light's standard library makes.  This is the ROOT of the
`HolTrace` Lean library and of the `holtrace` executable, which verifies such a
file by rebuilding it through this translation's kernel - every type, every
term, and every theorem by the primitive rule the trace says proves it.

    lake exe holtrace prime.50

Verifying a trace is a strictly stronger check than running the proof scripts
that produced it, in one specific sense: it establishes that THIS kernel accepts
the inferences some OTHER system recorded.  So it cross-checks two kernels
against each other on real proofs - and since HOL Light's own trace-saver and
this restorer share no code, a disagreement about `term_union`, `alphaorder`,
`inst`'s variable capture, or the sorted type variables of a type definition
shows up as a rejected trace rather than as nothing at all.

See `HolTrace/Parse.lean` for the format's encoding and `HolTrace/Restore.lean`
for the replay itself; this module is only the command line. -/

import HolTrace.Parse
import HolTrace.Restore

open HolCore.Kernel

namespace HolTrace.Cli

/-- What the command line asked for. -/
structure Options where
  /-- Which checks to run while replaying. -/
  cfg : Config := {}
  /-- The traces to verify, in order; `-` means standard input. -/
  files : Array String := #[]
  /-- Theorems to print after a trace verifies (`--print`). -/
  print : Array String := #[]
  /-- List the names the trace defines, with their theorems (`--names`). -/
  listNames : Bool := false
  /-- List those names on their own, without the theorems (`--names-only`).
      Takes precedence over `listNames` if both are given. -/
  listNamesOnly : Bool := false
  /-- Say nothing on success (`--quiet`). -/
  quiet : Bool := false
  /-- Show the usage message and stop (`--help`). -/
  help : Bool := false
  deriving Inhabited

/-- The usage message. -/
def usage : String :=
  "holtrace - verify HOLTrace files against the HOL Light kernel\n\
   \n\
   usage: holtrace [options] FILE...\n\
   \n\
   Replays each trace through this translation's HOL Light kernel: every type,\n\
   term and inference in the file is rebuilt, and each theorem the file states\n\
   must be exactly the one the inference before it derives.  FILE may be '-'\n\
   to read standard input.\n\
   \n\
   Replay starts from a bare kernel, so every constant, type and axiom a trace\n\
   uses must be created by that trace.  Several FILEs share one kernel, and\n\
   nothing can retract a constant once it is declared, so two traces that\n\
   define the same constant cannot both be verified in one run: give them to\n\
   two runs instead.\n\
   \n\
   options:\n\
     --print NAME    print the theorem named NAME once the trace verifies\n\
     --names         print every named theorem the trace defines, with its name\n\
     --names-only    print those names on their own\n\
     --no-thm-check  run every inference, but do not compare the results with\n\
                     the theorem statements the trace records\n\
     --lax-names     accept theorem names outside HOL Light's identifiers\n\
     --quiet         print nothing on success\n\
     -h, --help      show this message\n\
   \n\
   Exit status is 0 if every trace verified, 1 if one did not, 2 on a usage\n\
   error.  The format is specified at https://holtrace.cr.yp.to/format.html.\n"

/-- Parse the command line. -/
def parseArgs (args : List String) : Except String Options := do
  let mut opts : Options := {}
  let mut rest := args
  repeat
    match rest with
    | [] => break
    | a :: as =>
      rest := as
      match a with
      | "-h" | "--help"  => opts := { opts with help := true }
      | "--names"        => opts := { opts with listNames := true }
      | "--names-only"   => opts := { opts with listNamesOnly := true }
      | "--quiet"        => opts := { opts with quiet := true }
      | "--no-thm-check" =>
        opts := { opts with cfg := { opts.cfg with checkThms := false } }
      | "--lax-names"    =>
        opts := { opts with cfg := { opts.cfg with strictNames := false } }
      | "--print"        =>
        match as with
        | n :: as' => opts := { opts with print := opts.print.push n }; rest := as'
        | []       => throw "--print needs a theorem name"
      | _ =>
        -- `-` is a file (standard input); anything else starting with `-` is a
        -- mistyped option, which is worth reporting rather than treating as a
        -- filename that will not exist.
        if a.length > 1 && a.startsWith "-" then
          throw s!"unknown option '{a}'"
        opts := { opts with files := opts.files.push a }
  return opts

/-- Verify one trace, reporting what was checked.  Returns whether it passed. -/
def runFile (opts : Options) (path : String) : IO Bool := do
  match ← (verifyFile opts.cfg path).run with
  | .error e =>
      IO.eprintln s!"holtrace: {path}: {e}"
      return false
  | .ok st =>
      unless opts.quiet do
        IO.println st.summary
        IO.println s!"named thms: {st.names.size}"
      if opts.listNamesOnly then
        for (n, _) in st.names do IO.println n
      else if opts.listNames then
        for (n, th) in st.names do
          IO.println s!"{n}: {← HolCore.Printer.string_of_thm th}"
      for n in opts.print do
        match st.find? n with
        | some th => IO.println s!"{n}: {← HolCore.Printer.string_of_thm th}"
        | none    =>
            IO.eprintln s!"holtrace: {path}: no theorem named '{n}' in this trace"
            return false
      return true

/-- Entry point. -/
def run (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e =>
      IO.eprintln s!"holtrace: {e}"
      IO.eprint usage
      return 2
  | .ok opts =>
      if opts.help then
        IO.print usage
        return 0
      if opts.files.isEmpty then
        IO.eprintln "holtrace: no trace file given"
        IO.eprint usage
        return 2
      let mut ok := true
      for f in opts.files do
        unless ← runFile opts f do ok := false
      return if ok then 0 else 1

end HolTrace.Cli

/-- `holtrace`: verify HOLTrace files against this translation's kernel. -/
def main (args : List String) : IO UInt32 := HolTrace.Cli.run args
