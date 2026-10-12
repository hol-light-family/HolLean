/- ========================================================================= -/
/- Binary decision diagrams with complement edges, as a HOL derived rule.    -/
/-                                                                           -/
/- The style of implementation follows Brace, Rudell and Bryant's paper      -/
/- "Efficient implementation of a BDD package" (DAC 1990). It's based on the -/
/- hol90 implementation in "Binary Decision Diagrams as a HOL Derived Rule", -/
/- but greatly simplified since HOL Light handles pointer-eq subterms more   -/
/- efficiently and so we can avoid introducing any additional variables.     -/
/- ========================================================================= -/
/- File: HolLibrary/BDD.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/bdd.ml`, in the style of
  HolLibrary/Prime.lean.  bdd.ml is procedure code.  `setupBDD` is its load:
  it proves the proformas each `let NAME = let pth = ... in fun ...` binds
  (in file order) and builds the rewrite rules; the procedures take the
  result as `K`.

  Translation notes.
  * The tables are OCaml refs, arrays and a `Hashtbl`; here `IO.Ref`s of an
    `Array`, a `Std.HashMap` and lib.ml's finite partial functions (`Func`).
  * `try ... with Not_Found -> ...` (records 21, 47, 162).  HOL Light's lexer
    reads `Not_Found` as an ordinary identifier, so the handler is a
    variable pattern and catches EVERY exception (OCaml's exception is
    `Not_found`); `tryWith` here.
  * Evaluation order is OCaml's: `let ... and ...` left to right; tuples,
    list literals and function arguments right to left.  It matters where
    the tables are extended: `BDD_OF_TERM` numbers variables and nodes as it
    goes, and builds the RIGHT operand of a connective first.
  * `BDD_1 = max_int` is OCaml's 63-bit `max_int`.
-/

import HolMath
import Std.Data.HashMap

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB
open HolCore.Equal (ioconv lhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolCore.Bool (mk_neg is_iff)
open HolCore.Classic (mk_cond dest_cond)
open HolLight HolLight.Syntax

namespace HolLibrary.BDD

private instance : Ord (Int × Int) := lexOrd
private instance : Ord (Int × Int × Int) := lexOrd

/-- `tfst (a,b,c) = a` (bdd.ml 11). -/
def tfst {α β γ : Type} (t : α × β × γ) : α := t.1
/-- `tsnd (a,b,c) = b` (bdd.ml 12). -/
def tsnd {α β γ : Type} (t : α × β × γ) : β := t.2.1

/-- The variable table `(varray, vnext, vhash)`. -/
abbrev VTable := IO.Ref (Array term) × IO.Ref Int × IO.Ref (Std.HashMap term Int)
/-- The unique table `(uarray, unext, uhash)`. -/
abbrev UTable := IO.Ref (Func Int ((Int × Int × Int) × thm)) × IO.Ref Int ×
                 IO.Ref (Func (Int × Int × Int) Int)
/-- The computed table `(carray, cnext, chash)`. -/
abbrev CTable := IO.Ref (Func Int (Int × (thm × List Int × List Int))) × IO.Ref Int ×
                 IO.Ref (Func (Int × Int) Int)
/-- The three tables, `tt` in bdd.ml. -/
abbrev Tables := VTable × UTable × CTable
/-- A BDD: its node number and the theorem `|- tm <=> btm`. -/
abbrev Bdd := Int × thm

/- ------------------------------------------------------------------------- -/
/- Handling of variable tables.                                              -/
/- ------------------------------------------------------------------------- -/

/-- `var_of_num varray n = Array.get varray n` (bdd.ml 18). -/
def var_of_num (varray : IO.Ref (Array term)) (n : Int) : ExceptT String IO term := do
  match (← varray.get)[n.toNat]? with
  | some t => if n < 0 then throw "index out of bounds" else pure t
  | none => throw "index out of bounds"

/-- `num_of_var (varray,vnext,vhash) v` (bdd.ml 20-24). -/
def num_of_var (vt : VTable) (v : term) : ExceptT String IO Int := do
  let (varray, vnext, vhash) := vt
  match (← vhash.get).get? v with
  | some n => pure n
  | none =>
    let n ← vnext.get
    vnext.set (n + 1)
    let a ← varray.get
    if n < 0 || n.toNat >= a.size then throw "index out of bounds"
    varray.set (a.set! n.toNat v)
    vhash.modify (·.insert v n)
    pure n

/-- `mk_vtable n` (bdd.ml 26-29). -/
def mk_vtable (n : Int) : ExceptT String IO VTable := do
  let t ← q "T"
  let varray ← IO.mkRef (Array.replicate (n + 1).toNat t)
  let vnext ← IO.mkRef (1 : Int)
  let vhash ← IO.mkRef (Std.HashMap.emptyWithCapacity (n + 1).toNat : Std.HashMap term Int)
  pure (varray, vnext, vhash)

/- ------------------------------------------------------------------------- -/
/- Handling of unique table.                                                 -/
/- ------------------------------------------------------------------------- -/

/-- `BDD_1 = max_int` (bdd.ml 35): OCaml's `max_int`, 2^62 - 1. -/
def BDD_1 : Int := 4611686018427387903
/-- `BDD_0 = -BDD_1` (bdd.ml 36). -/
def BDD_0 : Int := -BDD_1

/-- What bdd.ml proves and builds when it loads. -/
structure BDDThms where
  true_tm : term
  -- BDD_EXPAND (65-91)
  ex_pth1 : thm
  ex_pth2 : thm
  ex_pth3 : thm
  ex_pth4 : thm
  ex_neg_tm : term
  ex_v_tm : term
  ex_b1_tm : term
  ex_b2_tm : term
  -- BDD_LOOKUP (93-120)
  lk_pth1 : thm
  lk_pth2 : thm
  lk_pth3 : thm
  lk_b_tm : term
  lk_v_tm : term
  lk_l_tm : term
  lk_r_tm : term
  -- bdd_and (131-237)
  and_pth : Array thm
  b1_tm : term
  b2_tm : term
  b3_tm : term
  l1_tm : term
  l2_tm : term
  l3_tm : term
  r1_tm : term
  r2_tm : term
  r3_tm : term
  v_tm : term
  -- BDD_TRUE, BDD_FALSE (248-250)
  BDD_TRUE : Bdd
  BDD_FALSE : Bdd
  -- BDD_VAR (252-262)
  var_pth : thm
  var_x_tm : term
  var_v_tm : term
  -- BDD_NEG (264-274)
  neg_neg_tm : term
  neg_x_tm : term
  neg_pth : thm
  -- BDD_AND (276-292)
  conj_and_tm : term
  conj_t1_tm : term
  conj_t2_tm : term
  conj_pth : thm
  -- BDD_OR, BDD_IMP, BDD_IFF (294-320)
  or_rule : ioconv
  imp_rule : ioconv
  iff_rule : ioconv
  -- BDD_EXISTS (342-348)
  rule_e : ioconv
  rule_d : ioconv
  rule_t : ioconv
  rule_f : ioconv
  deriving Inhabited

/-- `btm_of_int uarray n` (bdd.ml 38-44). -/
partial def btm_of_int (K : BDDThms) (uarray : IO.Ref (Func Int ((Int × Int × Int) × thm)))
    (n : Int) : ExceptT String IO term := do
  if n < 0 then liftExcept (mk_neg (← btm_of_int K uarray (-n))) else
  if n == BDD_1 then pure K.true_tm else
  let e ← liftExcept (apply (← uarray.get) n)
  liftExcept (do rand (← rator (concl e.2)))

/-- `lookup_triple varray (uarray,unext,uhash) tr` (bdd.ml 46-57). -/
def lookup_triple (K : BDDThms) (varray : IO.Ref (Array term)) (ut : UTable)
    (tr : Int × Int × Int) : ExceptT String IO Int := do
  let (uarray, unext, uhash) := ut
  let (v, y, n) := tr
  tryWith (liftExcept (apply (← uhash.get) tr)) (do
    let ytm ← btm_of_int K uarray y
    let ntm ← btm_of_int K uarray n
    let vtm ← var_of_num varray v
    let m ← unext.get
    let ltm ← ExceptT.mk (mk_cond vtm ytm ntm)
    let dth := REFL ltm
    unext.set (m + 1)
    uarray.modify (update m (tr, dth))
    uhash.modify (update tr m)
    pure m)

/-- `bdd_expand uarray b` (bdd.ml 59-63). -/
def bdd_expand (uarray : IO.Ref (Func Int ((Int × Int × Int) × thm))) (b : Int) :
    ExceptT String IO (Int × Int × Int) := do
  let f ← uarray.get
  if b < 0 then
    let (v, l, r) := (← liftExcept (apply f (-b))).1
    pure (v, -l, -r)
  else pure (← liftExcept (apply f b)).1

/-- `BDD_EXPAND uarray b` (bdd.ml 65-91). -/
def BDD_EXPAND (K : BDDThms) (uarray : IO.Ref (Func Int ((Int × Int × Int) × thm)))
    (b : Int) : ExceptT String IO thm := do
  let f ← uarray.get
  if b < 0 then
    let def_ := (← liftExcept (apply f (-b))).2
    let (v, (y, n)) ← liftExcept (do dest_cond (← rand (concl def_)))
    let pth ←
      if is_neg y then
        if is_neg n then do
          INST [(v, K.ex_v_tm), (← liftExcept (rand y), K.ex_b1_tm),
                (← liftExcept (rand n), K.ex_b2_tm)] K.ex_pth4
        else do
          INST [(v, K.ex_v_tm), (← liftExcept (rand y), K.ex_b1_tm), (n, K.ex_b2_tm)] K.ex_pth3
      else
        if is_neg n then do
          INST [(v, K.ex_v_tm), (y, K.ex_b1_tm), (← liftExcept (rand n), K.ex_b2_tm)] K.ex_pth2
        else INST [(v, K.ex_v_tm), (y, K.ex_b1_tm), (n, K.ex_b2_tm)] K.ex_pth1
    TRANS (← AP_TERM K.ex_neg_tm def_) pth
  else pure (← liftExcept (apply f b)).2

/-- `(I F_F dest_cond) (dest_eq tm)`: `(c, (v, (l, r)))`. -/
private def destEqCond (tm : term) : Except String (term × (term × (term × term))) := do
  let (c, rhs) ← dest_eq tm
  pure (c, ← dest_cond rhs)

/-- `BDD_LOOKUP varray utable (v,l,r)` (bdd.ml 93-120). -/
def BDD_LOOKUP [HolBase] (K : BDDThms) (varray : IO.Ref (Array term)) (ut : UTable)
    (vlr : Int × Int × Int) : ExceptT String IO (thm × Int × Int) := do
  let (v, l, r) := vlr
  let uarray := tfst ut
  if l == r then
    let btm ← btm_of_int K uarray l
    let vtm ← var_of_num varray v
    pure (← INST [(vtm, K.lk_v_tm), (btm, K.lk_b_tm)] K.lk_pth1, l, 0)
  else if l < 0 then
    let i ← lookup_triple K varray ut (v, -l, -r)
    let dth := (← liftExcept (apply (← uarray.get) i)).2
    let (ctm, (vtm, (ltm, rtm))) ← liftExcept (destEqCond (concl dth))
    if r < 0 then
      pure (← MP (← INST [(ctm, K.lk_b_tm), (vtm, K.lk_v_tm), (ltm, K.lk_l_tm),
                          (rtm, K.lk_r_tm)] K.lk_pth2) dth, -i, i)
    else
      pure (← MP (← INST [(ctm, K.lk_b_tm), (vtm, K.lk_v_tm), (ltm, K.lk_l_tm),
                          (← liftExcept (rand rtm), K.lk_r_tm)] K.lk_pth3) dth, -i, i)
  else
    let i ← lookup_triple K varray ut (v, l, r)
    let dth := (← liftExcept (apply (← uarray.get) i)).2
    pure (dth, i, i)

/-- `mk_utable()` (bdd.ml 122-125). -/
def mk_utable [HolBase] : IO UTable := do
  let uarray ← IO.mkRef (pointFun (0 : Int) ((0, 0, 0), HolBase.B.TRUTH))
  let unext ← IO.mkRef (1 : Int)
  let uhash ← IO.mkRef (undefined : Func (Int × Int × Int) Int)
  pure (uarray, unext, uhash)

/- ------------------------------------------------------------------------- -/
/- Handling of computed table.                                               -/
/- ------------------------------------------------------------------------- -/

/-- OCaml's `abs` on ints. -/
private def abs (n : Int) : Int := if n < 0 then -n else n

/-- `rev_itlist (C MP) lis ith` (bdd.ml 190, 204, 218). -/
private def mpChain [HolBase] (lis : List thm) (ith : thm) : ExceptT String IO thm :=
  lis.foldlM (fun acc th => MP acc th) ith

/-- `lookup_pair (carray,cnext,chash) (l,r)` (bdd.ml 160-162). -/
private def lookup_pair (ct : CTable) (lr : Int × Int) : ExceptT String IO (Int × Int) := do
  let (carray, _, chash) := ct
  tryWith (do
      let i ← liftExcept (apply (← chash.get) lr)
      pure ((← liftExcept (apply (← carray.get) i)).1, i))
    (throw "lookup_pair")

mutual

/-- `bdd_and (varray,utable,ctable) (l,r)` (bdd.ml 163-224). -/
partial def bdd_and [HolBase] (K : BDDThms)
    (tt : IO.Ref (Array term) × UTable × CTable) (lr : Int × Int) :
    ExceptT String IO (Int × Int) := do
  let (varray, utable, ctable) := tt
  let (carray, cnext, chash) := ctable
  let (l, r) := lr
  let ua := tfst utable
  let P (i : Nat) : thm := K.and_pth[i]!
  tryWith (lookup_pair ctable (l, r)) (do
    let (ans, thm_, uargs, cargs) ← (do
      if l == BDD_0 then
        pure (BDD_0, ← INST [(← btm_of_int K ua r, K.r1_tm)] (P 0), [], [])
      else if r == BDD_1 then
        pure (l, ← INST [(← btm_of_int K ua l, K.l1_tm)] (P 1), [], [])
      else if l == r then
        pure (l, ← INST [(← btm_of_int K ua l, K.l1_tm)] (P 2), [], [])
      else if l == -r then
        pure (BDD_0, ← INST [(← btm_of_int K ua r, K.r1_tm)] (P 3), [], [])
      else
        let (lv, ly, ln) ← bdd_expand ua l
        let (rv, ry, rn) ← bdd_expand ua r
        if lv == rv then
          let (thy, cy, jy) ← bdd_ands K tt (ly, ry)
          let (thn, cn, jn) ← bdd_ands K tt (ln, rn)
          let thl ← BDD_EXPAND K ua l
          let thr ← BDD_EXPAND K ua r
          let (thc, c, jc) ← BDD_LOOKUP K varray utable (lv, cy, cn)
          let (b1, (_v1, (l1, r1))) ← liftExcept (destEqCond (concl thl))
          let (b2, (_v2, (l2, r2))) ← liftExcept (destEqCond (concl thr))
          let (b3, (v3, (l3, r3))) ← liftExcept (destEqCond (concl thc))
          let ith ← INST [(b1, K.b1_tm), (b2, K.b2_tm), (b3, K.b3_tm),
                          (l1, K.l1_tm), (l2, K.l2_tm), (l3, K.l3_tm),
                          (r1, K.r1_tm), (r2, K.r2_tm), (r3, K.r3_tm), (v3, K.v_tm)] (P 4)
          let xth ← mpChain [thl, thr, thc, thy, thn] ith
          pure (c, xth, [abs l, abs r, jc], [jy, jn])
        else if lv > rv then
          let (thy, cy, jy) ← bdd_ands K tt (ly, r)
          let (thn, cn, jn) ← bdd_ands K tt (ln, r)
          let thl ← BDD_EXPAND K ua l
          let (thc, c, jc) ← BDD_LOOKUP K varray utable (lv, cy, cn)
          let (b1, (_v1, (l1, r1))) ← liftExcept (destEqCond (concl thl))
          let (b3, (v3, (l3, r3))) ← liftExcept (destEqCond (concl thc))
          let b2 ← liftExcept (do rand (← rand (← rator (concl thy))))
          let ith ← INST [(b1, K.b1_tm), (b2, K.b2_tm), (b3, K.b3_tm),
                          (l1, K.l1_tm), (l3, K.l3_tm),
                          (r1, K.r1_tm), (r3, K.r3_tm), (v3, K.v_tm)] (P 5)
          let xth ← mpChain [thl, thc, thy, thn] ith
          pure (c, xth, [abs l, jc], [jy, jn])
        else
          let (thy, cy, jy) ← bdd_ands K tt (l, ry)
          let (thn, cn, jn) ← bdd_ands K tt (l, rn)
          let thr ← BDD_EXPAND K ua r
          let (thc, c, jc) ← BDD_LOOKUP K varray utable (rv, cy, cn)
          let (b2, (_v2, (l2, r2))) ← liftExcept (destEqCond (concl thr))
          let (b3, (v3, (l3, r3))) ← liftExcept (destEqCond (concl thc))
          let b1 ← liftExcept (do rand (← rator (← rand (← rator (concl thy)))))
          let ith ← INST [(b1, K.b1_tm), (b2, K.b2_tm), (b3, K.b3_tm),
                          (l2, K.l2_tm), (l3, K.l3_tm),
                          (r2, K.r2_tm), (r3, K.r3_tm), (v3, K.v_tm)] (P 6)
          let xth ← mpChain [thr, thc, thy, thn] ith
          pure (c, xth, [abs r, jc], [jy, jn])
      : ExceptT String IO (Int × thm × List Int × List Int))
    let m ← cnext.get
    cnext.set (m + 1)
    carray.modify (update m (ans, (thm_, uargs, cargs)))
    chash.modify (update (l, r) m)
    pure (ans, m))

/-- `bdd_ands (varray,utable,ctable) (l,r)` (bdd.ml 226-236). -/
partial def bdd_ands [HolBase] (K : BDDThms)
    (tt : IO.Ref (Array term) × UTable × CTable) (lr : Int × Int) :
    ExceptT String IO (thm × Int × Int) := do
  let (l, r) := lr
  let carray := tfst tt.2.2
  if l <= r then
    let (ans, i) ← bdd_and K tt (l, r)
    let th := tfst (← liftExcept (apply (← carray.get) i)).2
    pure (th, ans, i)
  else
    let (ans, i) ← bdd_and K tt (r, l)
    let th := tfst (← liftExcept (apply (← carray.get) i)).2
    let (lr', _ctm) ← liftExcept (dest_eq (concl th))
    let (ltm, rtm) ← liftExcept (HolCore.Bool.dest_conj lr')
    let eth ← INST [(rtm, K.l1_tm), (ltm, K.r1_tm)] K.and_pth[7]!
    pure (← TRANS eth th, ans, i)

end

/-- `mk_ctable()` (bdd.ml 239-242). -/
def mk_ctable : IO CTable := do
  let carray ← IO.mkRef (undefined : Func Int (Int × (thm × List Int × List Int)))
  let cnext ← IO.mkRef (0 : Int)
  let chash ← IO.mkRef (undefined : Func (Int × Int) Int)
  pure (carray, cnext, chash)

/- ------------------------------------------------------------------------- -/
/- Basic BDD-constructing operations for the logical connectives.            -/
/- ------------------------------------------------------------------------- -/

/-- `BDD_VAR (vtable,utable,ctable) tm` (bdd.ml 252-262). -/
def BDD_VAR [HolBase] (K : BDDThms) (tt : Tables) (tm : term) : ExceptT String IO Bdd := do
  let (vtable, utable, _) := tt
  let v ← num_of_var vtable tm
  let u ← lookup_triple K (tfst vtable) utable (v, BDD_1, BDD_0)
  let ltm ← btm_of_int K (tfst utable) u
  let sth ← INST [(ltm, K.var_x_tm), (tm, K.var_v_tm)] K.var_pth
  let th := (← liftExcept (apply (← (tfst utable).get) u)).2
  pure (u, ← MP sth th)

/-- `BDD_NEG (vtable,utable,ctable) (i,fth)` (bdd.ml 264-274). -/
def BDD_NEG [HolBase] (K : BDDThms) (tt : Tables) (b : Bdd) : ExceptT String IO Bdd := do
  let (_, utable, _) := tt
  let (i, fth) := b
  if i < 0 then
    let utm ← btm_of_int K (tfst utable) (-i)
    let th ← INST [(utm, K.neg_x_tm)] K.neg_pth
    pure (-i, ← TRANS (← AP_TERM K.neg_neg_tm fth) th)
  else
    pure (-i, ← AP_TERM K.neg_neg_tm fth)

/-- `BDD_AND (vtable,utable,ctable) ((i1,th1),(i2,th2))` (bdd.ml 276-292). -/
def BDD_AND [HolBase] (K : BDDThms) (tt : Tables) (bs : Bdd × Bdd) : ExceptT String IO Bdd := do
  let (vtable, utable, ctable) := tt
  let ((i1, th1), (i2, th2)) := bs
  if i2 < i1 then
    let (i3, j) ← bdd_and K (tfst vtable, utable, ctable) (i2, i1)
    let bt2 ← btm_of_int K (tfst utable) i2
    let bt1 ← btm_of_int K (tfst utable) i1
    let sth ← INST [(bt1, K.conj_t1_tm), (bt2, K.conj_t2_tm)] K.conj_pth
    let th := tfst (← liftExcept (apply (← (tfst ctable).get) j)).2
    let rth ← TRANS sth th
    pure (i3, ← TRANS (← MK_COMB (← AP_TERM K.conj_and_tm th1, th2)) rth)
  else
    let (i3, j) ← bdd_and K (tfst vtable, utable, ctable) (i1, i2)
    let th := tfst (← liftExcept (apply (← (tfst ctable).get) j)).2
    pure (i3, ← TRANS (← MK_COMB (← AP_TERM K.conj_and_tm th1, th2)) th)

/-- `BDD_OR tt (b1,b2)` (bdd.ml 294-301). -/
def BDD_OR [HolBase] (K : BDDThms) (tt : Tables) (bs : Bdd × Bdd) : ExceptT String IO Bdd := do
  let n2 ← BDD_NEG K tt bs.2
  let n1 ← BDD_NEG K tt bs.1
  let (i, fth) ← BDD_NEG K tt (← BDD_AND K tt (n1, n2))
  pure (i, ← CONV_RULE K.or_rule fth)

/-- `BDD_IMP tt (b1,b2)` (bdd.ml 303-310). -/
def BDD_IMP [HolBase] (K : BDDThms) (tt : Tables) (bs : Bdd × Bdd) : ExceptT String IO Bdd := do
  let n2 ← BDD_NEG K tt bs.2
  let (i, fth) ← BDD_NEG K tt (← BDD_AND K tt (bs.1, n2))
  pure (i, ← CONV_RULE K.imp_rule fth)

/-- `BDD_IFF tt (b1,b2)` (bdd.ml 312-320).  The pair is built right to
    left: the `~(~a /\ b)` half first. -/
def BDD_IFF [HolBase] (K : BDDThms) (tt : Tables) (bs : Bdd × Bdd) : ExceptT String IO Bdd := do
  let (b1, b2) := bs
  let right ← BDD_NEG K tt (← BDD_AND K tt (← BDD_NEG K tt b1, b2))
  let left ← BDD_NEG K tt (← BDD_AND K tt (b1, ← BDD_NEG K tt b2))
  let (i, fth) ← BDD_AND K tt (left, right)
  pure (i, ← CONV_RULE K.iff_rule fth)

/-- `BDD_OF_TERM defs tt tm` (bdd.ml 322-336).  Operands right first. -/
partial def BDD_OF_TERM [HolBase] (K : BDDThms) (defs : Func term Bdd) (tt : Tables)
    (tm : term) : ExceptT String IO Bdd := do
  let two (op : Tables → Bdd × Bdd → ExceptT String IO Bdd) (l r : term) := do
    let br ← BDD_OF_TERM K defs tt r
    let bl ← BDD_OF_TERM K defs tt l
    op tt (bl, br)
  match tm with
  | .Const "T" _ => pure K.BDD_TRUE
  | .Const "F" _ => pure K.BDD_FALSE
  | .Comb (.Comb (.Const "/\\" _) l) r => two (BDD_AND K) l r
  | .Comb (.Comb (.Const "\\/" _) l) r => two (BDD_OR K) l r
  | .Comb (.Comb (.Const "==>" _) l) r => two (BDD_IMP K) l r
  | .Comb (.Comb (.Const "=" (.Tyapp "fun" [.Tyapp "bool" [], _])) l) r => two (BDD_IFF K) l r
  | .Comb (.Const "~" _) _ =>
      BDD_NEG K tt (← BDD_OF_TERM K defs tt (← liftExcept (rand tm)))
  | _ => tryWith (liftExcept (apply defs tm)) (BDD_VAR K tt tm)

/- ------------------------------------------------------------------------- -/
/- Existential quantification of BDDs.                                       -/
/- ------------------------------------------------------------------------- -/

/-- The recursive `BDD_EXISTS` of bdd.ml 352-375. -/
private partial def bddExists [HolBase] (K : BDDThms) (tt : Tables) (x : term) (xn : Int)
    (etable : IO.Ref (Func Int Bdd)) (b : Bdd) : ExceptT String IO Bdd := do
  let (vtable, utable, _) := tt
  let (n, th) := b
  tryWith (liftExcept (apply (← etable.get) n)) (do
    let res ← (do
      if n == BDD_0 then
        pure (BDD_0, ← CONV_RULE K.rule_f (← MK_EXISTS x th))
      else if n == BDD_1 then
        pure (BDD_1, ← CONV_RULE K.rule_t (← MK_EXISTS x th))
      else
        let (v, nt, nf) ← bdd_expand (tfst utable) n
        let eth ← TRANS th (← BDD_EXPAND K (tfst utable) n)
        let (_, (ntm, nfm)) ← liftExcept (do dest_cond (← rand (concl eth)))
        if v == xn then
          let (onum, oth) ← BDD_OR K tt ((nt, REFL ntm), (nf, REFL nfm))
          pure (onum, ← TRANS (← CONV_RULE K.rule_e (← MK_EXISTS x eth)) oth)
        else
          let (lnum, lth) ← bddExists K tt x xn etable (nt, REFL ntm)
          let (rnum, rth) ← bddExists K tt x xn etable (nf, REFL nfm)
          let op ← liftExcept (do rator (← rator (← rand (concl eth))))
          let mth ← MK_COMB (← AP_TERM op lth, rth)
          let wth ← TRANS (← CONV_RULE K.rule_d (← MK_EXISTS x eth)) mth
          let (fth, wn, _) ← BDD_LOOKUP K (tfst vtable) utable (v, lnum, rnum)
          pure (wn, ← TRANS wth (← SYM fth))
      : ExceptT String IO Bdd)
    etable.modify (update n res)
    pure res)

/-- `BDD_EXISTS (vtable,utable,ctable) x` (bdd.ml 342-376): a fresh
    `etable` and `x`'s variable number, then the function. -/
def BDD_EXISTS [HolBase] (K : BDDThms) (tt : Tables) (x : term) :
    ExceptT String IO (Bdd → ExceptT String IO Bdd) := do
  let etable ← IO.mkRef (undefined : Func Int Bdd)
  let xn ← num_of_var tt.1 x
  pure (bddExists K tt x xn etable)

/- ------------------------------------------------------------------------- -/
/- Provide some information on output when verbose = 1                       -/
/- ------------------------------------------------------------------------- -/

/-- `bdd_stats nd (vt,ct,ut)` (bdd.ml 382-388). -/
def bdd_stats (nd : Int) (vt : VTable) (ct : CTable) (ut : UTable) : IO Unit := do
  let d := if nd == 0 then "" else toString nd ++ " definitions, "
  remark
   ("BDD with " ++ d ++
    toString (← (tsnd vt).get) ++ " variables, " ++
    toString (← (tsnd ut).get) ++ " nodes and " ++
    toString (← (tsnd ct).get) ++ " cached results")

/- ------------------------------------------------------------------------- -/
/- Basic tautology prover                                                    -/
/- ------------------------------------------------------------------------- -/

/-- `BDD_TAUT tm` (bdd.ml 394-399). -/
def BDD_TAUT [HolBase] (K : BDDThms) (tm : term) : ExceptT String IO thm := do
  let vt ← mk_vtable (← liftExcept (atoms tm)).length
  let ut ← mk_utable
  let ct ← mk_ctable
  let b ← BDD_OF_TERM K undefined (vt, ut, ct) tm
  bdd_stats 0 vt ct ut
  EQT_ELIM b.2

/- ------------------------------------------------------------------------- -/
/- A version that treats an input p ==> q specially, considering p           -/
/- as a list of "definitions" (required to be left-to-right acyclic)         -/
/- ------------------------------------------------------------------------- -/

/-- `BDD_DEFTAUT ivars tm` (bdd.ml 406-451). -/
def BDD_DEFTAUT [HolBase] (K : BDDThms) (ivars : List term) (tm : term) :
    ExceptT String IO thm := do
  let bdd_def (th : thm) (b : Bdd) : ExceptT String IO Bdd := do
    pure (b.1, ← TRANS th b.2)
  let rec bdd_of_defs (defs : Func term Bdd) (tt : Tables) :
      List thm → ExceptT String IO (Func term Bdd)
    | [] => pure defs
    | th :: oths => do
      let (lv, rt) ← liftExcept (dest_eq (concl th))
      let br ← BDD_OF_TERM K defs tt rt
      let bl ← bdd_def th br
      bdd_of_defs (update lv bl defs) tt oths
  let is_atomic (tm : term) : Bool :=
    !(is_neg tm || is_conj tm || is_disj tm || is_imp tm || is_iff tm)
  let is_literal (tm : term) : Bool :=
    (is_neg tm && (match rand tm with | .ok t => is_atomic t | .error _ => false)) ||
    is_atomic tm
  let valid_definition (tm : term) : Bool :=
    (is_iff tm && (match lhand tm with | .ok t => is_literal t | .error _ => false)) ||
    is_literal tm
  let ADJUST_DEF (th : thm) : ExceptT String IO thm := do
    let tm := concl th
    if is_neg tm then EQF_INTRO th
    else if is_iff tm then pure th
    else EQT_INTRO th
  let rec acyclic (oks : List term) : List term → Except String Bool
    | [] => pure true
    | tm :: otms => do
      let l ← lhs tm
      if (((← rand tm) :: oks).any (free_in l)) then pure false
      else acyclic (tm :: oks) otms
  let valid_definitions (tm : term) : ExceptT String IO Bool := do
    let tms ← (conjuncts tm).mapM (fun c => do pure (concl (← ADJUST_DEF (← ASSUME c))))
    if tms.all valid_definition then liftExcept (acyclic [] tms) else pure false
  let vars := ivars ++ subtract (← liftExcept (atoms tm)) ivars
  let vt ← mk_vtable vars.length
  let ut ← mk_utable
  let ct ← mk_ctable
  for v in ivars do
    let _ ← BDD_VAR K (vt, ut, ct) v
  if is_imp tm && (← valid_definitions (← liftExcept (lhand tm))) then
    let ths ← (CONJUNCTS (← ASSUME (← liftExcept (lhand tm)))).mapM ADJUST_DEF
    let defs ← bdd_of_defs undefined (vt, ut, ct) ths
    let b ← BDD_OF_TERM K defs (vt, ut, ct) (← liftExcept (rand tm))
    bdd_stats (dom defs).length vt ct ut
    DISCH (← liftExcept (lhand tm)) (← EQT_ELIM b.2)
  else
    let b ← BDD_OF_TERM K undefined (vt, ut, ct) tm
    bdd_stats 0 vt ct ut
    EQT_ELIM b.2

/- ------------------------------------------------------------------------- -/
/- The load: the proformas, in file order.                                   -/
/- ------------------------------------------------------------------------- -/

/-- bdd.ml's load-time values.  `MESON` is meson.ml's. -/
@[nospecialize]
def setupBDD [HolBase] (MESON : List thm → term → ExceptT String IO thm) :
    ExceptT String IO BDDThms := do
  -- btm_of_int (38-39)
  let true_tm ← q "T"
  -- BDD_EXPAND (65-77)
  let ex_pth1 ← TAUT (← q r"~(if v then b1 else b2) <=> (if v then ~b1 else ~b2)")
  let ex_pth2 ← TAUT (← q r"~(if v then b1 else ~b2) <=> (if v then ~b1 else b2)")
  let ex_pth3 ← TAUT (← q r"~(if v then ~b1 else b2) <=> (if v then b1 else ~b2)")
  let ex_pth4 ← TAUT (← q r"~(if v then ~b1 else ~b2) <=> (if v then b1 else b2)")
  let ex_neg_tm ← q "~"
  let ex_v_tm ← q "v:bool"
  let ex_b1_tm ← q "b1:bool"
  let ex_b2_tm ← q "b2:bool"
  -- BDD_LOOKUP (93-104)
  let lk_pth1 ← TAUT (← q r"b <=> (if v then b else b)")
  let lk_pth2 ← TAUT (← q r"(b <=> (if v then l else r))
     ==> (~b <=> (if v then ~l else ~r))")
  let lk_pth3 ← TAUT (← q r"(b <=> (if v then l else ~r))
     ==> (~b <=> (if v then ~l else r))")
  let lk_b_tm ← q "b:bool"
  let lk_v_tm ← q "v:bool"
  let lk_l_tm ← q "l:bool"
  let lk_r_tm ← q "r:bool"
  -- bdd_and (131-159)
  let p1 ← TAUT (← q r"~T /\ r1 <=> ~T")
  let p2 ← TAUT (← q r"l1 /\ T <=> l1")
  let p3 ← TAUT (← q r"l1 /\ l1 <=> l1")
  let p4 ← TAUT (← q r"~r1 /\ r1 <=> ~T")
  let p5 ← TAUT (← q r"(b1 <=> (if v then l1 else r1))
     ==> (b2 <=> (if v then l2 else r2))
         ==> (b3 <=> (if v then l3 else r3))
             ==> (l1 /\ l2 <=> l3) ==> (r1 /\ r2 <=> r3) ==> (b1 /\ b2 <=> b3)")
  let p6 ← TAUT (← q r"(b1 <=> (if v then l1 else r1))
    ==> (b3 <=> (if v then l3 else r3))
        ==> (l1 /\ b2 <=> l3) ==> (r1 /\ b2 <=> r3) ==> (b1 /\ b2 <=> b3)")
  let p7 ← TAUT (← q r"(b2 <=> (if v then l2 else r2))
     ==> (b3 <=> (if v then l3 else r3))
         ==> (b1 /\ l2 <=> l3) ==> (b1 /\ r2 <=> r3) ==> (b1 /\ b2 <=> b3)")
  let p8 ← TAUT (← q r"l1 /\ r1 <=> r1 /\ l1")
  let b1_tm ← q "b1:bool"
  let b2_tm ← q "b2:bool"
  let b3_tm ← q "b3:bool"
  let l1_tm ← q "l1:bool"
  let l2_tm ← q "l2:bool"
  let l3_tm ← q "l3:bool"
  let r1_tm ← q "r1:bool"
  let r2_tm ← q "r2:bool"
  let r3_tm ← q "r3:bool"
  let v_tm ← q "v:bool"
  -- BDD_TRUE, BDD_FALSE (248-250)
  let BDD_TRUE := (BDD_1, REFL (← q "T"))
  let BDD_FALSE := (BDD_0, ← TAUT (← q r"F <=> ~T"))
  -- BDD_VAR (252-255)
  let var_pth ← TAUT (← q r"(x <=> (if v then T else ~T)) ==> v = x")
  let var_x_tm ← q "x:bool"
  let var_v_tm ← q "v:bool"
  -- BDD_NEG (264-267)
  let neg_neg_tm ← q "~"
  let neg_x_tm ← q "x:bool"
  let neg_pth ← TAUT (← q r"~ ~ x <=> x")
  -- BDD_AND (276-280)
  let conj_and_tm ← q r"/\"
  let conj_t1_tm ← q "t1:bool"
  let conj_t2_tm ← q "t2:bool"
  let conj_pth ← SPECL [conj_t1_tm, conj_t2_tm] HolBase.T.CONJ_SYM
  -- BDD_OR, BDD_IMP, BDD_IFF (294-316): `CONV_RULE(LAND_CONV(REWR_CONV pth))`
  let or_pth ← TAUT (← q r"~(~a /\ ~b) <=> a \/ b")
  let imp_pth ← TAUT (← q r"~(a /\ ~b) <=> a ==> b")
  let iff_pth ← TAUT (← q r"~(a /\ ~b) /\ ~(~a /\ b) <=> (a <=> b)")
  -- BDD_EXISTS (343-348): the list literal is evaluated last element
  -- first; `map` then runs MESON on the elements in order.
  let e4 ← q r"(?p:bool. ~T) <=> ~T"
  let e3 ← q r"(?p:bool. T) <=> T"
  let e2 ← q r"(?p. if x then q p else r p) <=> (if x then (?p. q p) else (?p. r p))"
  let e1 ← q r"(?p. if p then q else r) <=> q \/ r"
  let rules ← [e1, e2, e3, e4].mapM (fun t => do
    GEN_REWRITE_CONV_NET RAND_CONV [← MESON [] t])
  let (rule_e, rule_d, rule_t, rule_f) ← match rules with
    | [a, b, c, d] => pure (a, b, c, d)
    | _ => throw "BDD_EXISTS"
  return {
    true_tm := true_tm,
    ex_pth1 := ex_pth1, ex_pth2 := ex_pth2, ex_pth3 := ex_pth3, ex_pth4 := ex_pth4,
    ex_neg_tm := ex_neg_tm, ex_v_tm := ex_v_tm, ex_b1_tm := ex_b1_tm, ex_b2_tm := ex_b2_tm,
    lk_pth1 := lk_pth1, lk_pth2 := lk_pth2, lk_pth3 := lk_pth3,
    lk_b_tm := lk_b_tm, lk_v_tm := lk_v_tm, lk_l_tm := lk_l_tm, lk_r_tm := lk_r_tm,
    and_pth := #[p1, p2, p3, p4, p5, p6, p7, p8],
    b1_tm := b1_tm, b2_tm := b2_tm, b3_tm := b3_tm,
    l1_tm := l1_tm, l2_tm := l2_tm, l3_tm := l3_tm,
    r1_tm := r1_tm, r2_tm := r2_tm, r3_tm := r3_tm, v_tm := v_tm,
    BDD_TRUE := BDD_TRUE, BDD_FALSE := BDD_FALSE,
    var_pth := var_pth, var_x_tm := var_x_tm, var_v_tm := var_v_tm,
    neg_neg_tm := neg_neg_tm, neg_x_tm := neg_x_tm, neg_pth := neg_pth,
    conj_and_tm := conj_and_tm, conj_t1_tm := conj_t1_tm, conj_t2_tm := conj_t2_tm,
    conj_pth := conj_pth,
    or_rule := LAND_CONV (REWR_CONV or_pth),
    imp_rule := LAND_CONV (REWR_CONV imp_pth),
    iff_rule := LAND_CONV (REWR_CONV iff_pth),
    rule_e := rule_e, rule_d := rule_d, rule_t := rule_t, rule_f := rule_f }

end HolLibrary.BDD
