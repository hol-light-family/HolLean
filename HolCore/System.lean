/- File: System.lean
Some miscellaneous OCaml system hacking before we get started.
Together with a translation of OCaml's Format engine, used by the printers.
Original (c) Copyright, John Harrison 1998-2014
Lean4 translation by Chris Walton 2026

The OCaml runtime setup (the GC stack limit and, to make sure user interrupts
generate an exception, not kill the process, `Sys.catch_break true`) has no
Lean equivalent and is omitted. -/

import HolCore.Lib
open HolCore.Lib

namespace HolCore.System

/- ---------------------------------------------------------------------- -/
/- The OCaml `Format` pretty-printing engine, which HOL Light's printers  -/
/- are written against.  A direct translation of OCaml 5's              -/
/- stdlib/format.ml (the queue, scan stack, size computation and the      -/
/- line-breaking rules for each box type), so terms break exactly where   -/
/- HOL Light breaks them.  Omitted, because the printers never use them:  -/
/- tabulation boxes, semantic tags and `pp_print_if_newline`.            -/
/- ---------------------------------------------------------------------- -/

/-- The pretty-printing boxes (format.ml): `hbox` never splits; `vbox`
    splits at every break hint; `hvbox` behaves as an hbox if it fits on the
    current line, otherwise as a vbox; `hovbox` packs as much as possible on
    every line; `box` is like hovbox but break hints also split the line if
    splitting would move to the left.  `fits` marks a box that fits. -/
inductive BoxType where
  | hbox | vbox | hvbox | hovbox | box | fits
  deriving BEq, Inhabited

/-- The pretty-printing tokens (the subset HOL Light's printers emit). -/
inductive Token where
  | text (s : String)
  | brk (fits breaks : String × Int × String)
  | begin (off : Int) (ty : BoxType)
  | endBox
  | newline
  deriving Inhabited

/-- A queue element: `size` is set once the enclosing box's size is known;
    `length` is the declared length of the token. -/
structure QElem where
  size   : Int
  token  : Token
  length : Int
  deriving Inhabited

/-- The formatter state (format.ml `formatter`).  The queue is an array read
    from `qhead`, so scan-stack entries can refer to elements by index and
    update their sizes, as the OCaml does through mutable fields. -/
structure FmtState where
  out           : String := ""
  queue         : Array QElem := #[]
  qhead         : Nat := 0
  scanStack     : List (Int × Option Nat) := []   -- (left_total, element)
  formatStack   : List (BoxType × Int) := []      -- (box_type, width)
  margin        : Int := 78
  minSpaceLeft  : Int := 10
  maxIndent     : Int := 68
  spaceLeft     : Int := 78
  currentIndent : Int := 0
  isNewLine     : Bool := true
  leftTotal     : Int := 1
  rightTotal    : Int := 1
  currDepth     : Int := 1
  maxBoxes      : Int := 4611686018427387903      -- max_int
  ellipsis      : String := "."
  deriving Inhabited

abbrev Fmt := StateM FmtState

namespace Fmt

/-- `pp_infinity`. -/
private def infinity : Int := 1000000010

private def outString (s : String) : Fmt Unit := modify fun st => { st with out := st.out ++ s }
private def outSpaces (n : Int) : Fmt Unit :=
  if n > 0 then outString (String.ofList (List.replicate n.toNat ' ')) else pure ()

private def enqueue (e : QElem) : Fmt Unit :=
  modify fun st => { st with rightTotal := st.rightTotal + e.length, queue := st.queue.push e }

private def clearQueue : Fmt Unit :=
  modify fun st => { st with leftTotal := 1, rightTotal := 1, queue := #[], qhead := 0 }

private def formatPpText (size : Int) (text : String) : Fmt Unit := do
  modify fun st => { st with spaceLeft := st.spaceLeft - size }
  outString text
  modify fun st => { st with isNewLine := false }

private def formatString (s : String) : Fmt Unit :=
  if s != "" then formatPpText s.length s else pure ()

private def breakNewLine (b : String × Int × String) (width : Int) : Fmt Unit := do
  let (before, offset, after) := b
  formatString before
  outString "\n"
  let st ← get
  let indent := st.margin - width + offset
  let realIndent := min st.maxIndent indent
  set { st with isNewLine := true, currentIndent := realIndent,
                spaceLeft := st.margin - realIndent }
  outSpaces realIndent
  formatString after

private def breakLine (width : Int) : Fmt Unit := breakNewLine ("", 0, "") width

private def breakSameLine (b : String × Int × String) : Fmt Unit := do
  let (before, width, after) := b
  formatString before
  modify fun st => { st with spaceLeft := st.spaceLeft - width }
  outSpaces width
  formatString after

private def forceBreakLine : Fmt Unit := do
  let st ← get
  match st.formatStack with
  | [] => outString "\n"
  | (ty, width) :: _ =>
    if width > st.spaceLeft then
      match ty with
      | .fits | .hbox => pure ()
      | _ => breakLine width

private def formatPpToken (size : Int) : Token → Fmt Unit
  | .text s => formatPpText size s
  | .begin off ty => do
    let st ← get
    if st.margin - st.spaceLeft > st.maxIndent then forceBreakLine
    let st ← get
    let width := st.spaceLeft - off
    let boxType := match ty with
      | .vbox => .vbox
      | _ => if size > st.spaceLeft then ty else .fits
    set { st with formatStack := (boxType, width) :: st.formatStack }
  | .endBox => modify fun st => { st with formatStack := st.formatStack.tailD [] }
  | .newline => do
    match (← get).formatStack with
    | [] => outString "\n"
    | (_, width) :: _ => breakLine width
  | .brk fits breaks => do
    let (before, off, _) := breaks
    let st ← get
    match st.formatStack with
    | [] => pure ()
    | (ty, width) :: _ =>
      match ty with
      | .hovbox =>
        if size + before.length > st.spaceLeft then breakNewLine breaks width
        else breakSameLine fits
      | .box =>
        if st.isNewLine then breakSameLine fits
        else if size + before.length > st.spaceLeft then breakNewLine breaks width
        else if st.currentIndent > st.margin - width + off then breakNewLine breaks width
        else breakSameLine fits
      | .hvbox => breakNewLine breaks width
      | .fits => breakSameLine fits
      | .vbox => breakNewLine breaks width
      | .hbox => breakSameLine fits

/-- `advance_left`: print tokens whose size is known, or that cannot fit. -/
private partial def advanceLeft : Fmt Unit := do
  let st ← get
  if h : st.qhead < st.queue.size then
    let e := st.queue[st.qhead]
    let pending := st.rightTotal - st.leftTotal
    if e.size >= 0 || pending >= st.spaceLeft then
      set { st with qhead := st.qhead + 1 }
      formatPpToken (if e.size >= 0 then e.size else infinity) e.token
      modify fun st => { st with leftTotal := e.length + st.leftTotal }
      advanceLeft

private def enqueueAdvance (e : QElem) : Fmt Unit := do enqueue e; advanceLeft

private def enqueueStringAs (size : Int) (s : String) : Fmt Unit :=
  enqueueAdvance { size, token := .text s, length := size }

private def initializeScanStack : Fmt Unit :=
  modify fun st => { st with scanStack := [(-1, none)] }

/-- `set_size`: if `ty`, set the size of a break, else of a box. -/
private def setSize (ty : Bool) : Fmt Unit := do
  let st ← get
  match st.scanStack with
  | [] => pure ()
  | (leftTotal, elem) :: rest =>
    if leftTotal < st.leftTotal then initializeScanStack
    else match elem with
      | none => pure ()                         -- the dummy `Pp_text ""`
      | some i =>
        let e := st.queue[i]!
        let upd := fun (_ : Unit) =>
          set { st with queue := st.queue.set! i { e with size := st.rightTotal + e.size },
                        scanStack := rest }
        match e.token with
        | .brk .. => if ty then upd () else pure ()
        | .begin .. => if !ty then upd () else pure ()
        | _ => pure ()

/-- `scan_push`.  For a break (`pp_enqueue_break`), the previous break's size
    is set BEFORE this break's own width is added to `pp_right_total`; that is
    OCaml 5's order (4.14 added it first, counting each break's width into the
    size of the break before it). -/
private def scanPush (b : Bool) (e : QElem) : Fmt Unit := do
  let idx := (← get).queue.size
  if b then
    modify fun st => { st with queue := st.queue.push e }
    setSize true
    modify fun st => { st with rightTotal := st.rightTotal + e.length }
  else enqueue e
  modify fun st => { st with scanStack := (st.rightTotal, some idx) :: st.scanStack }

private def openBoxGen (indent : Int) (ty : BoxType) : Fmt Unit := do
  modify fun st => { st with currDepth := st.currDepth + 1 }
  let st ← get
  if st.currDepth < st.maxBoxes then
    scanPush false { size := - st.rightTotal, token := .begin indent ty, length := 0 }
  else if st.currDepth == st.maxBoxes then
    enqueueStringAs st.ellipsis.length st.ellipsis

/-- `pp_close_box`. -/
def closeBox : Fmt Unit := do
  let st ← get
  if st.currDepth > 1 then
    if st.currDepth < st.maxBoxes then
      enqueue { size := 0, token := .endBox, length := 0 }
      setSize true; setSize false
    modify fun st => { st with currDepth := st.currDepth - 1 }

/-- `pp_rinit`. -/
private def rinit : Fmt Unit := do
  clearQueue
  initializeScanStack
  modify fun st => { st with formatStack := [], currentIndent := 0, currDepth := 0,
                              spaceLeft := st.margin }
  openBoxGen 0 .hovbox                          -- pp_open_sys_box

/-- `pp_flush_queue`. -/
private partial def flushQueue (b : Bool) : Fmt Unit := do
  let rec closeAll : Nat → Fmt Unit
    | 0 => pure ()
    | n + 1 => do if (← get).currDepth > 1 then do closeBox; closeAll n
  closeAll ((← get).currDepth.toNat)
  modify fun st => { st with rightTotal := infinity }
  advanceLeft
  if b then outString "\n"
  rinit

/-- `pp_print_as`: print `s` but count it as width `n` (0 for ANSI escapes). -/
def printAs (n : Nat) (s : String) : Fmt Unit := do
  if (← get).currDepth < (← get).maxBoxes then enqueueStringAs n s

/-- `pp_print_string`. -/
def printString (s : String) : Fmt Unit := printAs s.length s

/-- `pp_open_hbox`. -/
def openHBox : Fmt Unit := openBoxGen 0 .hbox
/-- `pp_open_vbox`. -/
def openVBox (n : Int) : Fmt Unit := openBoxGen n .vbox
/-- `pp_open_hvbox`. -/
def openHvBox (n : Int) : Fmt Unit := openBoxGen n .hvbox
/-- `pp_open_hovbox`. -/
def openHovBox (n : Int) : Fmt Unit := openBoxGen n .hovbox
/-- `pp_open_box` (a `box`, not an hovbox). -/
def openBox (n : Int) : Fmt Unit := openBoxGen n .box

/-- `pp_print_break width offset`. -/
def printBreak (width offset : Int) : Fmt Unit := do
  let st ← get
  if st.currDepth < st.maxBoxes then
    scanPush true { size := - st.rightTotal, token := .brk ("", width, "") ("", offset, ""),
                    length := width }

/-- `pp_print_space = pp_print_break 1 0`. -/
def printSpace : Fmt Unit := printBreak 1 0

/-- `pp_force_newline`. -/
def forceNewline : Fmt Unit := do
  let st ← get
  if st.currDepth < st.maxBoxes then enqueueAdvance { size := 0, token := .newline, length := 0 }

/-- `pp_print_newline`: flush (closing every open box), then a newline. -/
def printNewline : Fmt Unit := flushQueue true

/-- `pp_print_flush`. -/
def printFlush : Fmt Unit := flushQueue false

/-- `pp_get_max_boxes`. -/
def getMaxBoxes : Fmt Nat := do return (← get).maxBoxes.toNat

/-- `pp_set_max_boxes n`: ignored unless `n > 1`. -/
def setMaxBoxes (n : Nat) : Fmt Unit :=
  modify fun st => if n > 1 then { st with maxBoxes := n } else st

/-- `pp_set_margin` (with `pp_set_max_indent`/`pp_set_min_space_left`). -/
def setMargin (n : Nat) : Fmt Unit := do
  if n >= 1 then
    let n : Int := min n (infinity - 1)
    modify fun st => { st with margin := n }
    let st ← get
    let newMaxIndent :=
      if st.maxIndent <= st.margin then st.maxIndent
      else max (max (st.margin - st.minSpaceLeft) (st.margin / 2)) 1
    if newMaxIndent > 1 then
      let msl := st.margin - newMaxIndent
      if msl >= 1 then
        let msl := min msl (infinity - 1)
        modify fun st => { st with minSpaceLeft := msl, maxIndent := st.margin - msl }
        rinit

/-- A fresh formatter (`pp_make_formatter`): margin 78, the system box open. -/
private def initial : FmtState :=
  { queue := #[{ size := -1, token := .begin 0 .hovbox, length := 0 }],
    scanStack := [(1, some 0), (-1, none)] }

/-- Render with the given margin and `max_boxes`, flushing at the end. -/
def runWith (width maxBoxes : Nat) (act : Fmt Unit) : String :=
  ((do setMaxBoxes maxBoxes; setMargin width; act; printFlush) initial).2.out

/-- HOL Light's `print_to_string` (printer.ml 734-746): a buffer formatter
    with `pp_set_max_boxes fmt 100` and the current margin. -/
def run (width : Nat) (act : Fmt Unit) : String := runWith width 100 act

/-- `Format.std_formatter` at the given margin.  printer.ml 109 sets its
    `max_boxes` to 100 (`include Format;; set_max_boxes 100`). -/
def runStd (width : Nat) (act : Fmt Unit) : String := runWith width 100 act

end Fmt

/- ---------------------------------------------------------------------- -/
/- Set up a printer for num (Rat)                                         -/
/- ---------------------------------------------------------------------- -/

def pp_print_num (n : Rat) : Fmt Unit := do
  Fmt.openHBox
  Fmt.printString (string_of_num n)
  Fmt.closeBox

def print_num (n : Rat) : IO Unit :=
  IO.print (Fmt.runStd 78 (pp_print_num n))

/- ---------------------------------------------------------------------- -/
/- Install a trivial printer for the general polymorphic case (`func`).   -/
/- ---------------------------------------------------------------------- -/

/-- pp_print_fpf: trivial `<func>` printer for finite partial functions. -/
def pp_print_fpf (_f : Func α β) : Fmt Unit := Fmt.printString "<func>"

/-- print_fpf: render at width 78 and write to stdout. -/
def print_fpf (f : Func α β) : IO Unit :=
  IO.print (Fmt.runStd 78 (pp_print_fpf f))

end HolCore.System
