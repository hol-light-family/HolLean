/- File: HolTrace/Parse.lean
Decoding of HOLTrace version 1 lines.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

HOLTrace (https://holtrace.cr.yp.to) records a HOL Light session as a sequence
of lines, each a 1-character tag followed by arguments.  This module implements
the LEXICAL half of the format - the argument encoding - and nothing about its
meaning; `HolTrace.Restore` interprets the tags.

The encoding is specified by https://holtrace.cr.yp.to/format.html.  Every
integer argument is written RELATIVE to an integer `n` fixed by the context
(usually "the counter of objects defined so far", so that back-references are
small numbers however long the file gets):

  * `!@#$%^&*()` mean `n-1` through `n-10`;
  * otherwise an uppercase base-32 numeral (digits `0`-`9` then `A`-`V`) means
    itself, and the same numeral after `-` means `n` minus that value.

A writer picks whichever of the last two forms is shorter, so a reader must
accept both.  Arguments are concatenated with no separator; a single space is
inserted only where it is needed to stop the next argument from being read as
more base-32 digits of this one.

This module is deliberately pure (no `IO`): the functions here are total on
every input, returning `Except String` rather than failing, which lets the
restorer turn any malformed line into a diagnostic naming the line number. -/

namespace HolTrace

/- ---------------------------------------------------------------------- -/
/- Bytes.                                                                 -/
/- ---------------------------------------------------------------------- -/

/-- The byte at `i`, or `0` past the end.  Total, so no index can panic: all
    callers stay inside the current line by construction, and a reader of a
    hostile file must not be able to crash. -/
@[inline] def byteAt (buf : ByteArray) (i : Nat) : UInt8 :=
  if h : i < buf.size then buf[i] else 0

/-- A HOLTrace line is "printable ASCII": bytes 32 through 126.  The LF
    terminating it is not part of the line. -/
@[inline] def isPrintable (b : UInt8) : Bool := 32 ≤ b && b ≤ 126

/-- Is this byte a base-32 digit, i.e. one of `0123456789ABCDEFGHIJKLMNOPQRSTUV`? -/
@[inline] def isBase32 (b : UInt8) : Bool :=
  (48 ≤ b && b ≤ 57) || (65 ≤ b && b ≤ 86)

/-- The value of a base-32 digit (`0`-`9` are 0-9, `A`-`V` are 10-31). -/
@[inline] def base32Digit (b : UInt8) : Nat :=
  if b ≤ 57 then b.toNat - 48 else b.toNat - 55

/-- The `!@#$%^&*()` shorthands, in order, denote `n-1` through `n-10`. -/
def symbolOffset (b : UInt8) : Option Nat :=
  match b with
  | 33 => some 1   -- !
  | 64 => some 2   -- @
  | 35 => some 3   -- #
  | 36 => some 4   -- $
  | 37 => some 5   -- %
  | 94 => some 6   -- ^
  | 38 => some 7   -- &
  | 42 => some 8   -- *
  | 40 => some 9   -- (
  | 41 => some 10  -- )
  | _  => none

/- ---------------------------------------------------------------------- -/
/- Cursors.                                                               -/
/- ---------------------------------------------------------------------- -/

/-- A position inside one line of a trace: the whole file's bytes, the offset
    to read next, and the offset just past this line's last byte.

    Lines are slices of the file rather than copies.  A trace of HOL Light's
    standard library runs to tens of millions of lines, so allocating a
    `String` per line - let alone per argument - is the one thing a reader must
    not do. -/
structure Cursor where
  /-- The whole file. -/
  buf : ByteArray
  /-- The next byte to read. -/
  pos : Nat
  /-- One past the last byte of the current line. -/
  stop : Nat

namespace Cursor

/-- Has the current line been consumed? -/
@[inline] def atEnd (c : Cursor) : Bool := c.stop ≤ c.pos

/-- Advance by `n` bytes. -/
@[inline] def skip (c : Cursor) (n : Nat) : Cursor := { c with pos := c.pos + n }

/- ---------------------------------------------------------------------- -/
/- Integer arguments.                                                     -/
/- ---------------------------------------------------------------------- -/

/-- Scan a base-32 numeral.  Returns its value and the position after it.

    A space ENDS the numeral and is consumed: that is how the format separates
    two arguments that would otherwise run together (`e17 14` is 17 then 14,
    not the single numeral `1714`).  A space in the first position therefore
    yields `0`, exactly as in the reference implementations - the restorer's
    progress check below is what rejects a missing argument. -/
def scanNonneg (buf : ByteArray) (pos stop : Nat) : Nat × Nat := Id.run do
  let mut acc : Nat := 0
  let mut i := pos
  while i < stop do
    let b := byteAt buf i
    if b == 32 then
      i := i + 1
      break
    else if isBase32 b then
      acc := 32 * acc + base32Digit b
      i := i + 1
    else
      break
  return (acc, i)

/-- Scan an argument in either absolute or `-`-relative form, relative to `id`.
    Nothing is consumed when the line has run out, which `subid` reports. -/
def scanRelative (c : Cursor) (id : Int) : Int × Cursor :=
  if c.atEnd then (0, c)
  else if byteAt c.buf c.pos == 45 then       -- '-': the value is id - numeral
    let (n, i) := scanNonneg c.buf (c.pos + 1) c.stop
    (id - (n : Int), { c with pos := i })
  else
    let (n, i) := scanNonneg c.buf c.pos c.stop
    ((n : Int), { c with pos := i })

/-- Scan one integer argument encoded relative to `id`, in any of the three
    forms: a `!@#$%^&*()` shorthand, an absolute numeral, or `-`-relative. -/
def scanArg (c : Cursor) (id : Int) : Int × Cursor :=
  if c.atEnd then (0, c)
  else match symbolOffset (byteAt c.buf c.pos) with
  | some k => (id - (k : Int), c.skip 1)
  | none   => scanRelative c id

/-- An integer argument that must name an object already defined: a back
    reference, so in `0 ≤ v < id`.

    `id` is the relevant counter (how many types, terms, theorems, ... the file
    has defined so far), which is also the value the encoding is relative to.
    A negative `id` means "no upper bound" - used for the argument COUNT on a
    `b` line, which is encoded relative to `-1` and bounded by the arguments
    that actually follow. -/
def subid (c : Cursor) (id : Int) : Except String (Nat × Cursor) :=
  let (v, c') := scanArg c id
  if c'.pos == c.pos then .error "missing numeric argument"
  else if v < 0 || (id ≥ 0 && v ≥ id) then
    .error s!"numeric argument out of range: {v} (bound {id})"
  else .ok (v.toNat, c')

/- ---------------------------------------------------------------------- -/
/- Text arguments.                                                        -/
/- ---------------------------------------------------------------------- -/

/-- The rest of the line as text: the final argument of the tags that take a
    name (`a`, `b`, `c`, `d`, `/`, `C`, `A`).

    The caller has already checked that every byte of the line is printable
    ASCII, so this cannot fail to decode; `decodeErr` is unreachable and only
    keeps the function total. -/
def text (c : Cursor) : Except String String :=
  if c.atEnd then .error "missing text argument"
  else
    match String.fromUTF8? (c.buf.extract c.pos c.stop) with
    | some s => .ok s
    | none   => .error "text argument is not valid ASCII"

/-- Check that the line is fully consumed, for the tags that take a fixed
    number of arguments and no text. -/
def expectEnd (c : Cursor) : Except String Unit :=
  if c.atEnd then .ok () else .error "extra argument"

end Cursor

/- ---------------------------------------------------------------------- -/
/- Lines.                                                                 -/
/- ---------------------------------------------------------------------- -/

/-- The end of the line starting at `start`: the offset of the next LF.
    `none` when the file runs out first, which means a partial final line -
    the format guarantees a terminating LF, so that is an error. -/
def lineEnd (buf : ByteArray) (start : Nat) : Option Nat := Id.run do
  let mut i := start
  while i < buf.size do
    if byteAt buf i == 10 then return some i
    i := i + 1
  return none

/-- Reject the bytes a trace line may not contain.  LF has already been
    stripped by `lineEnd`, so anything outside 32-126 - a stray CR, a tab, a
    NUL, a byte of some other encoding - is malformed. -/
def checkPrintable (buf : ByteArray) (start stop : Nat) : Except String Unit := Id.run do
  let mut i := start
  while i < stop do
    let b := byteAt buf i
    if !isPrintable b then
      return .error s!"byte {b.toNat} is prohibited"
    i := i + 1
  return .ok ()

/-- The magic first line of a version 1 trace. -/
def magic : String := "HOLTrace 1"

end HolTrace
