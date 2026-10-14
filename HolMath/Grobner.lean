/- File: Grobner.lean
Generic Grobner basis algorithm.

Whatever the instantiation, it basically solves the universal theory of
the complex numbers, or equivalently something like the theory of all
commutative cancellation semirings with no nilpotent elements and having
characteristic zero.  We could do "all rings" by a more elaborate integer
version of Grobner bases, but I don't have any useful applications.

Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026 -/

import HolCore.Bool
import HolCore.Equal
import HolCore.Drule
import HolCore.Tactics
import HolCore.Itab
import HolCore.Simp
import HolCore.Parser
import HolCore.Printer
import HolCore.Nets
import HolCore.Theorems
import HolCore.IndDefs
import HolCore.Classic
import HolCore.Canon
import HolCore.Meson
import HolMath.Pair
import HolMath.Nums
import HolMath.Recursion
import HolMath.Arith
import HolMath.Wf
import HolMath.CalcNum
import HolMath.Normalizer
import HolMath.Base


namespace HolMath.Grobner

set_option maxRecDepth 8000

section Polynomials

open HolCore HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Bool HolCore.Equal
     HolCore.Drule HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Parser
     HolCore.Theorems HolCore.IndDefs HolCore.Classic HolCore.Canon


/- ---------------------------------------------------------------------- -/
/- Type for recording history, i.e. how a polynomial was obtained.        -/
/- ---------------------------------------------------------------------- -/

/-- `type history = Start of int | Mmul of (num * (int list)) * history
    | Add of history * history` (grobner.ml 18-21). -/
inductive history where
  | Start : Int → history
  | Mmul  : (Rat × List Int) → history → history
  | Add   : history → history → history
  deriving Inhabited, Repr, BEq

/-- A monomial: a coefficient paired with an exponent vector.  The OCaml uses
    the bare pair type `num * int list`. -/
abbrev mon := Rat × List Int

/-- A canonical polynomial: a list of monomials in descending monomial order.
    The OCaml uses the bare list type `(num * int list) list`. -/
abbrev poly := List mon

/-- A polynomial paired with the history recording how it was derived.  The
    OCaml writes this pair inline as `(pol,hist)`. -/
abbrev polyh := poly × history

/- ---------------------------------------------------------------------- -/
/- Overall function; everything else is local.                            -/
/- ---------------------------------------------------------------------- -/
-- (`RING_AND_IDEAL_CONV` is the whole parametrized closure; this port
-- decomposes its local `let`s into the top-level defs that follow.)

/- ---------------------------------------------------------------------- -/
/- Monomial ordering.                                                    -/
/- ---------------------------------------------------------------------- -/

/-- The inner `lexorder` of `morder_lt` (grobner.ml 35-38).  The OCaml raises
    `failwith "morder: inconsistent monomial lengths"` when the two exponent
    vectors have different lengths; here that is an `Except`. -/
def lexorderLt : List Int → List Int → Except String Bool
  | [], [] => .ok false
  | x1 :: o1, x2 :: o2 => do
      if x1 > x2 then return true
      else if x1 == x2 then lexorderLt o1 o2
      else return false
  | _, _ => .error "morder: inconsistent monomial lengths"

/-- `morder_lt` (grobner.ml 34-42): compare total degree first, then break ties
    lexicographically. -/
def morder_lt (m1 m2 : List Int) : Except String Bool := do
  let n1 := itlist (· + ·) m1 0
  let n2 := itlist (· + ·) m2 0
  if n1 < n2 then return true
  else if n1 == n2 then lexorderLt m1 m2
  else return false

/- ---------------------------------------------------------------------- -/
/- Arithmetic on canonical polynomials.                                  -/
/- ---------------------------------------------------------------------- -/

/-- `grob_neg = map (fun (c,m) -> (minus_num c,m))` (grobner.ml 48). -/
def grob_neg (l : poly) : poly := l.map (fun (c, m) => (-c, m))

/-- `grob_add` (grobner.ml 50-59): merge two ordered polynomials, cancelling
    monomials whose coefficients sum to zero. -/
partial def grob_add : poly → poly → Except String poly
  | [], l2 => .ok l2
  | l1, [] => .ok l1
  | l1@(((c1, m1)) :: o1), l2@(((c2, m2)) :: o2) => do
      if m1 == m2 then
        let c := c1 + c2
        let rest ← grob_add o1 o2
        if c == num_0 then return rest else return (c, m1) :: rest
      else if ← morder_lt m2 m1 then
        return (c1, m1) :: (← grob_add o1 l2)
      else
        return (c2, m2) :: (← grob_add l1 o2)

/-- `grob_sub l1 l2 = grob_add l1 (grob_neg l2)` (grobner.ml 61). -/
def grob_sub (l1 l2 : poly) : Except String poly := grob_add l1 (grob_neg l2)

/-- `grob_mmul (c1,m1) (c2,m2) = (c1*/c2, map2 (+) m1 m2)` (grobner.ml 63).
    `map2` raises on length mismatch, so this is an `Except`. -/
def grob_mmul : mon → mon → Except String mon
  | (c1, m1), (c2, m2) => do
      let m ← map2 (· + ·) m1 m2
      return (c1 * c2, m)

/-- `grob_cmul cm pol = map (grob_mmul cm) pol` (grobner.ml 65). -/
def grob_cmul (cm : mon) (pol : poly) : Except String poly :=
  pol.mapM (fun m => grob_mmul cm m)

/-- `grob_mul` (grobner.ml 67-70). -/
partial def grob_mul : poly → poly → Except String poly
  | [], _ => .ok []
  | h1 :: t1, l2 => do grob_add (← grob_cmul h1 l2) (← grob_mul t1 l2)

/-- `grob_inv` (grobner.ml 72-77). -/
def grob_inv : poly → Except String poly
  | [(c, vs)] =>
      if vs.all (fun x => x == 0) then
        if c == num_0 then .error "grob_inv: division by zero"
        else .ok [(num_1 / c, vs)]
      else .error "grob_inv: non-constant divisor polynomial"
  | _ => .error "grob_inv: non-constant divisor polynomial"

/-- `grob_div` (grobner.ml 79-84). -/
def grob_div (l1 : poly) : poly → Except String poly
  | [(c, l)] =>
      if l.all (fun x => x == 0) then
        if c == num_0 then .error "grob_div: division by zero"
        else grob_cmul (num_1 / c, l) l1
      else .error "grob_div: non-constant divisor polynomial"
  | _ => .error "grob_div: non-constant divisor polynomial"

/-- `grob_pow` (grobner.ml 86-89). -/
partial def grob_pow (vars : List α) (l : poly) (n : Int) : Except String poly :=
  if n < 0 then .error "grob_pow: negative power"
  else if n == 0 then .ok [(num_1, vars.map (fun _ => (0 : Int)))]
  else do grob_mul l (← grob_pow vars l (n - 1))

/- ---------------------------------------------------------------------- -/
/- Monomial division operation.                                          -/
/- ---------------------------------------------------------------------- -/

/-- `mdiv` (grobner.ml 95-97).  Fails (`failwith "mdiv"`) if any exponent of
    the divisor exceeds the corresponding exponent of the dividend. -/
def mdiv : mon → mon → Except String mon
  | (c1, m1), (c2, m2) => do
      let m ← map2 (fun n1 n2 => (n1, n2)) m1 m2
      let es ← m.mapM (fun (n1, n2) =>
        if n1 < n2 then (.error "mdiv" : Except String Int) else .ok (n1 - n2))
      return (c1 / c2, es)

/- ---------------------------------------------------------------------- -/
/- Lowest common multiple of two monomials.                              -/
/- ---------------------------------------------------------------------- -/

/-- `mlcm (c1,m1) (c2,m2) = (num_1, map2 max m1 m2)` (grobner.ml 103).  Note
    the coefficients are DISCARDED - the result always has coefficient 1. -/
def mlcm : mon → mon → Except String mon
  | (_, m1), (_, m2) => do
      let m ← map2 (fun a b => max a b) m1 m2
      return (num_1, m)

/- ---------------------------------------------------------------------- -/
/- Reduce monomial cm by polynomial pol, returning replacement for cm.    -/
/- ---------------------------------------------------------------------- -/

/-- `reduce1 cm (pol,hpol)` (grobner.ml 109-121): divide `cm` by the leading
    monomial, forming the replacement polynomial and history record.  Fails on
    the empty polynomial. -/
def reduce1 (cm : mon) : polyh → Except String polyh
  | ([], _) => .error "reduce1"
  | (cm1 :: cms, hpol) =>
      match mdiv cm cm1 with
      | .error _ => .error "reduce1"
      | .ok (c, m) => do
          let q ← grob_cmul (-c, m) cms
          return (q, .Mmul (-c, m) hpol)

/- ---------------------------------------------------------------------- -/
/- Try this for all polynomials in a basis.                               -/
/- ---------------------------------------------------------------------- -/

/-- `reduceb cm basis = tryfind (fun p -> reduce1 cm p) basis` (grobner.ml
    127). -/
def reduceb (cm : mon) (basis : List polyh) : Except String polyh :=
  tryfind (fun p => reduce1 cm p) basis

/- ---------------------------------------------------------------------- -/
/- Reduction of a polynomial (always picking largest monomial possible).  -/
/- ---------------------------------------------------------------------- -/

/-- `reduce basis (pol,hist)` (grobner.ml 127-133).  The OCaml uses
    `try ... with Failure _` as control flow: if `reduceb` fails on the leading
    monomial it recurses on the tail and conses the monomial back on; rendered
    here as a `match` on the `reduceb` result. -/
partial def reduce (basis : List polyh) : polyh → Except String polyh
  | ([], hist) => .ok ([], hist)
  | (cm :: ptl, hist) =>
      match reduceb cm basis with
      | .ok (q, hnew) => do
          reduce basis (← grob_add q ptl, .Add hnew hist)
      | .error _ => do
          let (q, hist') ← reduce basis (ptl, hist)
          return (cm :: q, hist')

/- ---------------------------------------------------------------------- -/
/- Check for orthogonality w.r.t. LCM.                                    -/
/- ---------------------------------------------------------------------- -/

/-- `orthogonal l p1 p2 = snd l = snd(grob_mmul (hd p1) (hd p2))`
    (grobner.ml 140-141). -/
def orthogonal (l : mon) (p1 p2 : poly) : Except String Bool := do
  let h1 ← hd p1
  let h2 ← hd p2
  let (_, m) ← grob_mmul h1 h2
  return l.2 == m

/- ---------------------------------------------------------------------- -/
/- Compute S-polynomial of two polynomials.                               -/
/- ---------------------------------------------------------------------- -/

/-- `spoly cm ph1 ph2` (grobner.ml 147-155): the S-polynomial of two
    polynomials, with its history record. -/
def spoly (cm : mon) : polyh → polyh → Except String polyh
  | ([], h), _ => .ok ([], h)
  | _, ([], h) => .ok ([], h)
  | (cm1 :: ptl1, his1), (cm2 :: ptl2, his2) => do
      let d1 ← mdiv cm cm1
      let d2 ← mdiv cm cm2
      let a ← grob_cmul d1 ptl1
      let b ← grob_cmul d2 ptl2
      let p ← grob_sub a b
      let d2h ← mdiv (-cm.1, cm.2) cm2
      return (p, .Add (.Mmul d1 his1) (.Mmul d2h his2))

/- ---------------------------------------------------------------------- -/
/- Make a polynomial monic.                                               -/
/- ---------------------------------------------------------------------- -/

/-- `monic (pol,hist)` (grobner.ml 161-165): scale a polynomial to make its
    leading coefficient 1, recording the scaling in the history. -/
def monic : polyh → Except String polyh
  | ([], hist) => .ok ([], hist)
  | (pol@((c', m') :: _), hist) => do
      let p := pol.map (fun (c, m) => (c / c', m))
      return (p, .Mmul (num_1 / c', m'.map (K 0)) hist)

/- ---------------------------------------------------------------------- -/
/- The most popular heuristic is to order critical pairs by LCM monomial. -/
/- ---------------------------------------------------------------------- -/

/-- `forder ((c1,m1),_) ((c2,m2),_) = morder_lt m1 m2` (grobner.ml 171).
    Since the port's `morder_lt` returns `Except String Bool` but `merge`
    and `mergesort` require a pure `Bool` comparator, we collapse an error
    (inconsistent monomial lengths, which cannot occur for a fixed variable
    count) to `false`. -/
def forder (a b : mon × β) : Bool :=
  match morder_lt a.1.2 b.1.2 with
  | .ok r => r
  | .error _ => false

/- ---------------------------------------------------------------------- -/
/- Stupid stuff forced on us by lack of equality test on num type.        -/
/- ---------------------------------------------------------------------- -/

/-- Explicit LEXICOGRAPHIC comparison on exponent vectors (`int list`).  In
    the OCaml `poly_lt`, the subterm `m1 < m2` is OCaml's POLYMORPHIC
    structural comparison on `int list`, which is lexicographic; we write it
    out here rather than relying on a derived instance. -/
def intListLt : List Int → List Int → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x1 :: o1, x2 :: o2 =>
      if x1 < x2 then true
      else if x1 == x2 then intListLt o1 o2
      else false

/-- `poly_lt` (grobner.ml 177-183): `p,[] -> false`, `[],q -> true`, and on
    a cons `c1 </ c2 || c1 =/ c2 && (m1 < m2 || m1 = m2 && poly_lt o1 o2)`,
    where `m1 < m2` is the lexicographic `intListLt` above. -/
def poly_lt : poly → poly → Bool
  | _, [] => false
  | [], _ => true
  | (c1, m1) :: o1, (c2, m2) :: o2 =>
      c1 < c2 ||
      c1 == c2 && (intListLt m1 m2 || m1 == m2 && poly_lt o1 o2)

/-- `align ((p,hp),(q,hq))` (grobner.ml 185-186): order a pair of polynomials
    canonically by `poly_lt` on their polynomial components. -/
def align (pr : polyh × polyh) : polyh × polyh :=
  let ((p, hp), (q, hq)) := pr
  if poly_lt p q then ((p, hp), (q, hq)) else ((q, hq), (p, hp))

/-- `poly_eq p1 p2 = forall2 (fun (c1,m1) (c2,m2) -> c1 =/ c2 && m1 = m2)`
    (grobner.ml 188-189).  `forall2` returns FALSE on a length mismatch (it
    does not raise). -/
def poly_eq (p1 p2 : poly) : Bool :=
  forall2 (fun (a : mon) (b : mon) => a.1 == b.1 && a.2 == b.2) p1 p2

/-- `memx ((p1,h1),(p2,h2)) ppairs` (grobner.ml 191-193).  Negated sense: it
    is `not (exists ...)`, returning TRUE when the pair is NOT found
    (`criterion2` then applies a second `not`). -/
def memx (pr : polyh × polyh) (ppairs : List (polyh × polyh)) : Bool :=
  let ((p1, _), (p2, _)) := pr
  !(exists' (fun (qq : polyh × polyh) =>
      poly_eq p1 qq.1.1 && poly_eq p2 qq.2.1) ppairs)

/- ---------------------------------------------------------------------- -/
/- Buchberger's second criterion.                                         -/
/- ---------------------------------------------------------------------- -/

/-- `criterion2 basis (lcm,((p1,h1),(p2,h2))) opairs` (grobner.ml 199-204):
    Buchberger's second criterion. -/
def criterion2 (basis : List polyh)
    (crit : mon × (polyh × polyh)) (opairs : List (mon × (polyh × polyh))) :
    Bool :=
  let (lcm, ((p1, h1), (p2, h2))) := crit
  let snds := opairs.map (fun x => x.2)
  exists' (fun (g : polyh) =>
    !(poly_eq g.1 p1) && !(poly_eq g.1 p2) &&
    (match hd g.1 with
     | .ok hg => can (fun m => mdiv lcm m) hg
     | .error _ => false) &&
    !(memx (align (g, (p1, h1))) snds) &&
    !(memx (align (g, (p2, h2))) snds)) basis

/- ---------------------------------------------------------------------- -/
/- Test for hitting constant polynomial.                                  -/
/- ---------------------------------------------------------------------- -/

/-- `constant_poly p = length p = 1 && forall ((=) 0) (snd(hd p))`
    (grobner.ml 209-210). -/
def constant_poly (p : poly) : Bool :=
  match p with
  | [(_, m)] => m.all (fun x => x == 0)
  | _ => false

/- ---------------------------------------------------------------------- -/
/- Grobner basis algorithm.                                               -/
/- ---------------------------------------------------------------------- -/


/-- grobner.ml prints its progress (`N basis elements and M critical pairs`,
    `Generating HOL version of proof`, `Translating certificate to HOL
    inferences`) unconditionally.  This flag, not in the OCaml, lets it be
    switched off; it defaults to `true`, HOL Light's behaviour.  The test suite
    sets it to `false` (HolTest/CommonTest.lean). -/
initialize grobner_messages : IO.Ref Bool ← IO.mkRef true

/-- `grobner_basis basis pairs` (grobner.ml 216-232).  Self-recursive.  The
    OCaml prints diagnostic progress, which forces this into `IO` (wrapped in
    `Except` for the failing sub-operations). -/
partial def grobner_basis (basis : List polyh)
    (pairs : List (mon × (polyh × polyh))) :
    ExceptT String IO (List polyh) := do
  -- OCaml diagnostic output.
  if ← grobner_messages.get then
    IO.print (s!"{length basis} basis elements and " ++
              s!"{length pairs} critical pairs")
    IO.println ""
  match pairs with
  | [] => return basis
  | (l, (p1, p2)) :: opairs =>
      let sph ← liftExcept (do
        let sp1 ← spoly l p1 p2
        let sp2 ← reduce basis sp1
        monic sp2)
      let (sp, _) := sph
      if sp == [] || criterion2 basis (l, (p1, p2)) opairs then
        grobner_basis basis opairs
      else if constant_poly sp then
        grobner_basis (sph :: basis) []
      else
        let newcps ← liftExcept (do
          let rawcps ← basis.mapM (fun p => do
            let hp ← hd p.1
            let hs ← hd sp
            let lm ← mlcm hp hs
            return (lm, align (p, sph)))
          rawcps.filterM (fun (l, (p, q)) => do
            return !(← orthogonal l p.1 q.1)))
        grobner_basis (sph :: basis)
          (merge forder opairs (mergesort forder newcps))

/- ---------------------------------------------------------------------- -/
/- Interreduce initial polynomials.                                       -/
/- ---------------------------------------------------------------------- -/

/-- `grobner_interreduce rpols ipols` (grobner.ml 238-244).  Self-recursive.
    On the empty `ipols` it returns `map monic (rev rpols)`. -/
partial def grobner_interreduce (rpols ipols : List polyh) :
    Except String (List polyh) :=
  match ipols with
  | [] => (rev rpols).mapM monic
  | p :: ps => do
      let p' ← reduce (rpols ++ ps) p
      if p'.1 == [] then grobner_interreduce rpols ps
      else grobner_interreduce (p' :: rpols) ps

/- ---------------------------------------------------------------------- -/
/- Overall function.                                                      -/
/- ---------------------------------------------------------------------- -/

/-- `grobner pols` (grobner.ml 249-259).  `map2 (fun p n -> p,Start n) pols
    (0--(length pols - 1))` pairs each polynomial with a `Start` history
    indexed by its position (`0--n` is `Lib.upto 0 n`); then the prs0/prs1/
    prs2/prs3 pipeline builds and filters the initial critical pairs, and
    finally `grobner_basis bas (mergesort forder prs3)`. -/
def grobner (pols : List poly) : ExceptT String IO (List polyh) := do
  let (bas, prs3) ← liftExcept (do
    let idxs := upto 0 (Int.ofNat (length pols) - 1)
    let npols ← map2 (fun p n => (p, history.Start n)) pols idxs
    let phists := filter (fun (x : polyh) => x.1 != []) npols
    let monphists ← phists.mapM monic
    let bas ← grobner_interreduce [] monphists
    let prs0 := allpairs (fun x y => (x, y)) bas bas
    let prs1 := filter (fun (pr : polyh × polyh) => poly_lt pr.1.1 pr.2.1) prs0
    let prs2 ← prs1.mapM (fun (p, q) => do
      let hp ← hd p.1
      let hq ← hd q.1
      let lm ← mlcm hp hq
      return (lm, (p, q)))
    let prs3 ← prs2.filterM (fun (l, (p, q)) => do
      return !(← orthogonal l p.1 q.1))
    return (bas, prs3))
  grobner_basis bas (mergesort forder prs3)

/- ---------------------------------------------------------------------- -/
/- Get proof of contradiction from Grobner basis.                         -/
/- ---------------------------------------------------------------------- -/

/-- `grobner_refute pols` (grobner.ml 264-267): run `grobner`, then
    `snd(find (fun (p,h) -> length p = 1 && forall ((=)0) (snd(hd p))) gb)`,
    i.e. the history of the constant polynomial witnessing contradiction. -/
def grobner_refute (pols : List poly) : ExceptT String IO history := do
  let gb ← grobner pols
  let (_, h) ← liftExcept (find (fun (ph : polyh) => constant_poly ph.1) gb)
  return h

/- ---------------------------------------------------------------------- -/
/- Turn proof into a certificate as sum of multipliers.                   -/
/-                                                                        -/
/- In principle this is very inefficient: in a heavily shared proof it may-/
/- make the same calculation many times.  Could add a cache or something. -/
/- ---------------------------------------------------------------------- -/

/-- `resolve_proof vars prf` (grobner.ml 275-289).  `Start(-1)` is a SENTINEL
    (the negated goal) yielding the empty certificate; `Start m` yields
    `[m,[num_1,map (K 0) vars]]`.  The `Add` case unions the domains via
    `setify(union (map fst lis1) (map fst lis2))`, looking each key up with
    `try assoc n lis1 with Failure _ -> []`.  `vars` is a `List term` here -
    only its LENGTH is used, via `map (K 0) vars`. -/
partial def resolve_proof (vars : List term) :
    history → Except String (List (Int × poly))
  | .Start (-1) => .ok []
  | .Start m => .ok [(m, [(num_1, vars.map (K 0))])]
  | .Mmul pol lin => do
      let lis ← resolve_proof vars lin
      lis.mapM (fun (n, p) => do return (n, ← grob_cmul pol p))
  | .Add lin1 lin2 => do
      let lis1 ← resolve_proof vars lin1
      let lis2 ← resolve_proof vars lin2
      let dom := setify (union (lis1.map (fun x => x.1)) (lis2.map (fun x => x.1)))
      dom.mapM (fun n => do
        let a := match assoc n lis1 with | .ok v => v | .error _ => []
        let b := match assoc n lis2 with | .ok v => v | .error _ => []
        return (n, ← grob_add a b))

/- ---------------------------------------------------------------------- -/
/- Run the procedure and produce Weak Nullstellensatz certificate.        -/
/- ---------------------------------------------------------------------- -/

/-- `grobner_weak vars pols` (grobner.ml 294-299).  `l = itlist (itlist
    (lcm_num o denominator o fst) o snd) cert num_1` clears denominators.
    Note: `denominator` returns `Int` while `lcm_num` takes `Rat`, so the
    denominator is converted to `Rat` (via `Rat.ofInt`) before the lcm; the
    composition `lcm_num o denominator o fst` is written as an explicit
    lambda. -/
def grobner_weak (vars : List term) (pols : List poly) :
    ExceptT String IO (Rat × List (Int × poly)) := do
  let prf ← grobner_refute pols
  let cert ← liftExcept (resolve_proof vars prf)
  let l : Rat :=
    itlist (fun (ip : Int × poly) acc =>
      itlist (fun (dm : mon) a =>
        lcm_num (Rat.ofInt (denominator dm.1)) a) ip.2 acc) cert num_1
  let out := cert.map (fun (i, p) => (i, p.map (fun (d, m) => (l * d, m))))
  return (l, out)

/- ---------------------------------------------------------------------- -/
/- Prove polynomial is in ideal generated by others, using Grobner basis. -/
/- ---------------------------------------------------------------------- -/

/-- `grobner_ideal vars pols pol` (grobner.ml 304-308): reduce `grob_neg pol`
    (with the `Start(-1)` sentinel history) by the Grobner basis of `pols`;
    if the residue is non-empty the polynomial is NOT in the ideal (failure
    `"grobner_ideal: not in the ideal"`), otherwise resolve the history into a
    certificate. -/
def grobner_ideal (vars : List term) (pols : List poly) (pol : poly) :
    ExceptT String IO (List (Int × poly)) := do
  let gb ← grobner pols
  let (pol', h) ← liftExcept (reduce gb (grob_neg pol, history.Start (-1)))
  if pol' != [] then throw "grobner_ideal: not in the ideal"
  else liftExcept (resolve_proof vars h)

/- ---------------------------------------------------------------------- -/
/- Produce Strong Nullstellensatz certificate for a power of pol.         -/
/- ---------------------------------------------------------------------- -/

/-- `grobner_strong vars pols pol` (grobner.ml 313-330).  `vars' = (concl
    TRUTH)::vars` uses the TERM `T` (`concl TRUTH`, passed in as `truth`) as a
    dummy extra variable, so only its presence in the length of `vars'`
    matters.  Transcribes `grob_z`, `grob_1`, `augment`, `pols'`/`pol'`,
    `allpols`, the `d` computation, `transform_monomial`,
    `transform_polynomial`, and the `cert'` filter
    (`filter (fun (k,_) -> k <> 0)` then `c-1`).  The `o` compositions
    (`max o hd o snd`, `grob_add o transform_monomial`) are written as
    explicit lambdas. -/
def grobner_strong (truth : term) (vars : List term) (pols : List poly)
    (pol : poly) : ExceptT String IO (Int × Rat × List (Int × poly)) := do
  if pol == [] then return (1, num_1, [])
  else
    let vars' := truth :: vars
    let grob_z : poly := [(num_1, (1 : Int) :: vars.map (K 0))]
    let grob_1 : poly := [(num_1, vars'.map (K 0))]
    let augment : poly → poly := fun p => p.map (fun (c, m) => (c, (0 : Int) :: m))
    let pols' := pols.map augment
    let pol' := augment pol
    let allpols ← liftExcept (do
      let zp ← grob_mul grob_z pol'
      let allpols0 ← grob_sub zp grob_1
      return allpols0 :: pols')
    let (l, cert) ← grobner_weak vars' allpols
    -- d = itlist (itlist (max o hd o snd) o snd) cert 0
    let d : Int :=
      itlist (fun (ip : Int × poly) acc =>
        itlist (fun (dm : mon) a =>
          max (match dm.2 with | x :: _ => x | [] => 0) a) ip.2 acc) cert 0
    -- transform_monomial (c,m) = grob_cmul (c,tl m) (grob_pow vars pol (d - hd m))
    let transform_monomial : mon → Except String poly := fun (c, m) => do
      let hm := match m with | x :: _ => x | [] => 0
      let tm := match m with | _ :: r => r | [] => []
      let gp ← grob_pow vars pol (d - hm)
      grob_cmul (c, tm) gp
    -- transform_polynomial q = itlist (grob_add o transform_monomial) q []
    let transform_polynomial : poly → Except String poly := fun q =>
      q.foldr (fun (m : mon) acc => do grob_add (← transform_monomial m) (← acc))
        (.ok [])
    let cert' ← liftExcept (do
      let filtered := filter (fun (kp : Int × poly) => kp.1 != 0) cert
      filtered.mapM (fun (c, q) => do
        return (c - 1, ← transform_polynomial q)))
    return (d, l, cert')

/- ---------------------------------------------------------------------- -/
/- Overall parametrized universal procedure for (semi)rings.              -/
/- We return an IDEAL_CONV and the actual ring prover.                    -/
/- ---------------------------------------------------------------------- -/

end Polynomials

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj is_iff mk_exists)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/-- `pth_step` (grobner.ml 336-352). -/
def pth_step [HolBase] (DE_MORGAN_THM CONTRAPOS_THM : thm) :
    ExceptT String IO thm := do
  prove
   r"!(add:A->A->A) (mul:A->A->A) (n0:A).
          (!x. mul n0 x = n0) /\
          (!x y z. (add x y = add x z) <=> (y = z)) /\
          (!w x y z. (add (mul w y) (mul x z) = add (mul w z) (mul x y)) <=>
                     (w = x) \/ (y = z))
          ==> (!a b c d. ~(a = b) /\ ~(c = d) <=>
                         ~(add (mul a c) (mul b d) =
                           add (mul a d) (mul b c))) /\
              (!n a b c d. ~(n = n0)
                           ==> (a = b) /\ ~(c = d)
                               ==> ~(add a (mul n c) = add b (mul n d)))"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [← GSYM DE_MORGAN_THM] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      pure (MP_TAC (← SPECL [← q r"n0:A", ← q r"n:A", ← q r"d:A", ← q r"c:A"] th))) THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN ASM_SIMP_TAC [])

end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj is_iff mk_exists)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax


/-- The parameter-independent values `RING_AND_IDEAL_CONV` builds once, before
    `fun parms -> ...` (grobner.ml 336-354): `pth_step`, `FINAL_RULE` and
    `false_tm`. -/
structure GrobnerGlobals where
  pth_step   : thm
  FINAL_RULE : thm → IO (Except String thm)
  false_tm   : term

instance : Inhabited GrobnerGlobals := ⟨⟨default, fun _ => pure (.error ""), default⟩⟩

/-- Build `GrobnerGlobals` (grobner.ml 336-354), in the `let ... and ...`
    order. -/
@[nospecialize]
def setupGrobnerGlobals [HolBase] (DE_MORGAN_THM CONTRAPOS_THM : thm) :
    ExceptT String IO GrobnerGlobals := do
  let pth_step ← pth_step DE_MORGAN_THM CONTRAPOS_THM
  let finalTaut ← TAUT (← q r"(p ==> F) ==> (~q = p) ==> q")
  let FINAL_RULE : thm → IO (Except String thm) := fun th => (MATCH_MP finalTaut th).run
  let false_tm ← q r"F"
  return { pth_step, FINAL_RULE, false_tm }

/-- `refute_disj rfn tm` (grobner.ml 355-359).  OCaml evaluates
    `DISJ_CASES (ASSUME tm) (refute_disj rfn l) (refute_disj rfn r)` right to
    left. -/
partial def refute_disj [HolBase] (rfn : ioconv) : ioconv
  | tm@(.Comb (.Comb (.Const "\\/" _) l) r) => ExceptT.run do
      let rth ← ExceptT.mk (refute_disj rfn r)
      let lth ← ExceptT.mk (refute_disj rfn l)
      DISJ_CASES (← ASSUME tm) lth rth
  | tm => rfn tm

/- ---------------------------------------------------------------------- -/
/- The 13-component parameter tuple (grobner.ml 360-363).                 -/
/- ---------------------------------------------------------------------- -/

/-- The `fun (ring_dest_const,ring_mk_const,RING_EQ_CONV, ring_neg_tm,
    ring_add_tm,ring_sub_tm, ring_inv_tm,ring_mul_tm,ring_div_tm,ring_pow_tm,
    RING_INTEGRAL,RABINOWITSCH_THM,RING_NORMALIZE_CONV) -> ...` parameter tuple
    (grobner.ml 360-363), fields in the OCaml order. -/
structure RingParms where
  ring_dest_const     : term → Except String Rat
  ring_mk_const       : Rat → Except String term
  RING_EQ_CONV        : ioconv
  ring_neg_tm         : term
  ring_add_tm         : term
  ring_sub_tm         : term
  ring_inv_tm         : term
  ring_mul_tm         : term
  ring_div_tm         : term
  ring_pow_tm         : term
  RING_INTEGRAL       : thm
  RABINOWITSCH_THM    : thm
  RING_NORMALIZE_CONV : ioconv
  deriving Inhabited

/-- `INITIAL_CONV` (grobner.ml 364-381).  Both rewrite nets are built here,
    once per parameter tuple. -/
def INITIAL_CONV [HolBase] (K : RingParms)
    (PRESIMP_CONV CONDS_ELIM_CONV NNF_CONV : ioconv)
    (AND_FORALL_THM LEFT_AND_FORALL_THM RIGHT_AND_FORALL_THM
     LEFT_OR_FORALL_THM RIGHT_OR_FORALL_THM OR_EXISTS_THM
     LEFT_OR_EXISTS_THM RIGHT_OR_EXISTS_THM LEFT_AND_EXISTS_THM
     RIGHT_AND_EXISTS_THM : thm) : ExceptT String IO ioconv := do
  let finalLink ← GEN_REWRITE_CONV_NET REDEPTH_CONV
      [AND_FORALL_THM, LEFT_AND_FORALL_THM, RIGHT_AND_FORALL_THM,
       LEFT_OR_FORALL_THM, RIGHT_OR_FORALL_THM, OR_EXISTS_THM,
       LEFT_OR_EXISTS_THM, RIGHT_OR_EXISTS_THM, LEFT_AND_EXISTS_THM,
       RIGHT_AND_EXISTS_THM]
  let rabLink ←
    if is_iff (strip_forall (concl K.RABINOWITSCH_THM)).2
    then GEN_REWRITE_CONV_NET ONCE_DEPTH_CONV [K.RABINOWITSCH_THM]
    else pure ALL_CONV
  return TOP_DEPTH_CONV BETA_CONV THENC
         PRESIMP_CONV THENC
         CONDS_ELIM_CONV THENC
         NNF_CONV THENC
         rabLink THENC
         finalLink

/- ---------------------------------------------------------------------- -/
/- The ring destructors and constructors (grobner.ml 382-394).            -/
/- ---------------------------------------------------------------------- -/

/-- `ring_dest_neg` (grobner.ml 382-384). -/
def ring_dest_neg (K : RingParms) (t : term) : Except String term := do
  let (l, r) ← dest_comb t
  if l == K.ring_neg_tm then .ok r else failwith "ring_dest_neg"

/-- `ring_dest_inv` (grobner.ml 385-387). -/
def ring_dest_inv (K : RingParms) (t : term) : Except String term := do
  let (l, r) ← dest_comb t
  if l == K.ring_inv_tm then .ok r else failwith "ring_dest_inv"

/-- `ring_dest_add = dest_binop ring_add_tm` (grobner.ml 388). -/
def ring_dest_add (K : RingParms) : term → Except String (term × term) :=
  dest_binop K.ring_add_tm

/-- `ring_dest_sub = dest_binop ring_sub_tm` (grobner.ml 390). -/
def ring_dest_sub (K : RingParms) : term → Except String (term × term) :=
  dest_binop K.ring_sub_tm

/-- `ring_dest_mul = dest_binop ring_mul_tm` (grobner.ml 391). -/
def ring_dest_mul (K : RingParms) : term → Except String (term × term) :=
  dest_binop K.ring_mul_tm

/-- `ring_dest_div = dest_binop ring_div_tm` (grobner.ml 393). -/
def ring_dest_div (K : RingParms) : term → Except String (term × term) :=
  dest_binop K.ring_div_tm

/-- `ring_dest_pow = dest_binop ring_pow_tm` (grobner.ml 394). -/
def ring_dest_pow (K : RingParms) : term → Except String (term × term) :=
  dest_binop K.ring_pow_tm

/-- `ring_mk_add = mk_binop ring_add_tm` (grobner.ml 389). -/
def ring_mk_add (K : RingParms) (a b : term) : Except String term := do
  (← mk_binop K.ring_add_tm a) b

/-- `ring_mk_mul = mk_binop ring_mul_tm` (grobner.ml 392). -/
def ring_mk_mul (K : RingParms) (a b : term) : Except String term := do
  (← mk_binop K.ring_mul_tm a) b

/-- `ring_mk_pow = mk_binop ring_pow_tm` (grobner.ml 394). -/
def ring_mk_pow (K : RingParms) (a b : term) : Except String term := do
  (← mk_binop K.ring_pow_tm a) b

/- ---------------------------------------------------------------------- -/
/- grobvars, grobify_term, grobify_equation(s) (grobner.ml 395-442).      -/
/- ---------------------------------------------------------------------- -/

/-- `grobvars tm acc` (grobner.ml 395-410). -/
partial def grobvars (K : RingParms) (tm : term) (acc : List term) : List term :=
  let rnd := match rand tm with | .ok r => r | .error _ => tm
  let lhd := match lhand tm with | .ok l => l | .error _ => tm
  if can K.ring_dest_const tm then acc
  else if can (ring_dest_neg K) tm then grobvars K rnd acc
  else if can (ring_dest_pow K) tm && HolMath.Nums.is_numeral rnd then grobvars K lhd acc
  else if can (ring_dest_add K) tm || can (ring_dest_sub K) tm ||
          can (ring_dest_mul K) tm then
    grobvars K lhd (grobvars K rnd acc)
  else if can (ring_dest_inv K) tm then
    let gvs := grobvars K rnd []
    if gvs == [] then acc else tm :: acc
  else if can (ring_dest_div K) tm then
    let lvs := grobvars K lhd acc
    let gvs := grobvars K rnd []
    if gvs == [] then lvs else tm :: acc
  else tm :: acc

/-- `grobify_term vars tm` (grobner.ml 411-431).  Each OCaml `try` covers
    the whole level, including the recursive calls, so any failure in a
    level falls through to the next one. -/
partial def grobify_term (K : RingParms) (vars : List term) (tm : term) :
    Except String poly :=
  let orElse (a : Except String poly) (b : Unit → Except String poly) : Except String poly :=
    match a with | .ok p => .ok p | .error _ => b ()
  orElse (if mem tm vars then .ok [(num_1, vars.map (fun i => if i == tm then (1 : Int) else 0))]
          else failwith "") fun _ =>
  orElse (do let x ← K.ring_dest_const tm
             if x == num_0 then .ok [] else .ok [(x, vars.map (fun _ => (0 : Int)))]) fun _ =>
  orElse (do return grob_neg (← grobify_term K vars (← ring_dest_neg K tm))) fun _ =>
  orElse (do grob_inv (← grobify_term K vars (← ring_dest_inv K tm))) fun _ =>
  orElse (do let (l, r) ← ring_dest_add K tm
             grob_add (← grobify_term K vars l) (← grobify_term K vars r)) fun _ =>
  orElse (do let (l, r) ← ring_dest_sub K tm
             grob_sub (← grobify_term K vars l) (← grobify_term K vars r)) fun _ =>
  orElse (do let (l, r) ← ring_dest_mul K tm
             grob_mul (← grobify_term K vars l) (← grobify_term K vars r)) fun _ =>
  orElse (do let (l, r) ← ring_dest_div K tm
             grob_div (← grobify_term K vars l) (← grobify_term K vars r)) fun _ =>
  orElse (do let (l, r) ← ring_dest_pow K tm
             grob_pow vars (← grobify_term K vars l) (← HolMath.Nums.dest_small_numeral r)) fun _ =>
  failwith "grobify_term: unknown or invalid term"

/-- `grobify_equation vars tm` (grobner.ml 432-434). -/
def grobify_equation (K : RingParms) (vars : List term) (tm : term) :
    Except String poly := do
  let (l, r) ← dest_eq tm
  grob_sub (← grobify_term K vars l) (← grobify_term K vars r)

/-- `grobify_equations tm` (grobner.ml 435-442).  `x < y` is OCaml's
    polymorphic `<` on terms (see `Normalizer.variable_order`). -/
def grobify_equations (K : RingParms) (tm : term) :
    Except String (List term × List poly) := do
  let cjs := conjuncts tm
  let rawvars := itlist (fun eq a =>
      grobvars K (match lhand eq with | .ok l => l | .error _ => eq)
        (grobvars K (match rand eq with | .ok r => r | .error _ => eq) a))
    cjs []
  let vars := sort (fun x y => compare x y == Ordering.lt) (setify rawvars)
  return (vars, ← cjs.mapM (grobify_equation K vars))

/-- `holify_polynomial` (grobner.ml 443-456). -/
def holify_polynomial (K : RingParms) (Nm : HolMath.Nums.NumeralConsts)
    (vars : List term) (p : poly) : Except String term := do
  let holify_varpow : term × Int → Except String term := fun (v, n) =>
    if n == 1 then .ok v
    else do ring_mk_pow K v (← HolMath.Nums.mk_small_numeral Nm n)
  let holify_monomial : mon → Except String term := fun (c, m) => do
    let xps ← (filter (fun (vn : term × Int) => vn.2 != 0) (← zip vars m)).mapM holify_varpow
    end_itlistM (ring_mk_mul K) ((← K.ring_mk_const c) :: xps)
  if p == [] then K.ring_mk_const num_0
  else end_itlistM (ring_mk_add K) (← p.mapM holify_monomial)

/- ---------------------------------------------------------------------- -/
/- execute_proof (grobner.ml 467-527).                                    -/
/- ---------------------------------------------------------------------- -/

/-- `run_proof` (grobner.ml 483-490), hoisted from `execute_proof`.  The
    OCaml `assoceq` cache uses physical equality; here it is structural
    (`BEq history`), which can only hit more often and returns the same
    theorem. -/
partial def run_proof
    (initpols : List thm)
    (ADD_RULE : thm → thm → ExceptT String IO thm)
    (MUL_RULE : List term → mon → thm → ExceptT String IO thm)
    (execache : IO.Ref (List (history × thm)))
    (vars : List term) (prf : history) : ExceptT String IO thm := do
  match Lib.assoc prf (← execache.get) with
  | .ok th => return th
  | .error _ =>
    let ans ← match prf with
      | .Start m => liftExcept (Lib.el m.toNat initpols)
      | .Add p1 p2 => do
          -- OCaml evaluates `ADD_RULE (run_proof vars p1) (run_proof vars p2)`
          -- right to left.
          let t2 ← run_proof initpols ADD_RULE MUL_RULE execache vars p2
          let t1 ← run_proof initpols ADD_RULE MUL_RULE execache vars p1
          ADD_RULE t1 t2
      | .Mmul m p2 => do
          MUL_RULE vars m (← run_proof initpols ADD_RULE MUL_RULE execache vars p2)
    if !(match prf with | .Start _ => true | _ => false) then
      execache.modify (fun c => (prf, ans) :: c)
    return ans

/-- `run_scaled_proof` (grobner.ml 500-514), hoisted from `execute_proof`;
    `km = map (fun x -> 0) vars`.  Same cache note as `run_proof`. -/
partial def run_scaled_proof
    (initpols : List thm)
    (ADD_RULE : thm → thm → ExceptT String IO thm)
    (MUL_RULE : List term → mon → thm → ExceptT String IO thm)
    (km : List Int)
    (execache : IO.Ref (List (history × (Rat × thm))))
    (vars : List term) (prf : history) : ExceptT String IO (Rat × thm) := do
  match Lib.assoc prf (← execache.get) with
  | .ok dth => return dth
  | .error _ =>
    let ans ← match prf with
      | .Start m => do pure (num_1, ← liftExcept (Lib.el m.toNat initpols))
      | .Add p1 p2 => do
          let (d1, th1) ← run_scaled_proof initpols ADD_RULE MUL_RULE km execache vars p1
          let (d2, th2) ← run_scaled_proof initpols ADD_RULE MUL_RULE km execache vars p2
          let d := lcm_num d1 d2
          let th2' ← MUL_RULE vars (d / d2, km) th2
          let th1' ← MUL_RULE vars (d / d1, km) th1
          pure (d, ← ADD_RULE th1' th2')
      | .Mmul (c, xs) p2 => do
          let e : Int := denominator c
          let (d, th) ← run_scaled_proof initpols ADD_RULE MUL_RULE km execache vars p2
          pure (d * Rat.ofInt e, ← MUL_RULE vars (c * Rat.ofInt e, xs) th)
    if !(match prf with | .Start _ => true | _ => false) then
      execache.modify (fun c => (prf, ans) :: c)
    return ans

/-- What `RING_AND_IDEAL_CONV` builds from the parameter tuple before
    `execute_proof` (grobner.ml 364-465): `INITIAL_CONV`, `pth_idom`,
    `pth_ine`, `NOT_EQ_01`, plus the inputs the procedures read. -/
structure RingCtx where
  K            : RingParms
  Nm           : HolMath.Nums.NumeralConsts
  G            : GrobnerGlobals
  truth        : term
  WEAK_DNF_CONV : ioconv
  INITIAL_CONV : ioconv
  pth_idom     : thm
  pth_ine      : thm
  NOT_EQ_01    : thm
  deriving Inhabited

/-- `PROVE_NZ n = EQF_ELIM(RING_EQ_CONV (mk_eq(ring_mk_const n,ring_mk_const
    num_0)))` (grobner.ml 462-463).  OCaml evaluates `mk_eq`'s pair right to
    left. -/
def PROVE_NZ [HolBase] (K : RingParms) (n : Rat) : ExceptT String IO thm := do
  let c0 ← liftExcept (K.ring_mk_const num_0)
  let cn ← liftExcept (K.ring_mk_const n)
  EQF_ELIM (← ExceptT.mk (K.RING_EQ_CONV (safe_mk_eq cn c0)))

/-- Build the `RingCtx` (grobner.ml 364-465), in OCaml order:
    `INITIAL_CONV`, then `CONJ_PAIR(MATCH_MP pth_step RING_INTEGRAL)`, then
    `NOT_EQ_01 = PROVE_NZ num_1`. -/
@[nospecialize]
def setupRingCtx [HolBase] (G : GrobnerGlobals) (Nm : HolMath.Nums.NumeralConsts)
    (truth : term) (PRESIMP_CONV CONDS_ELIM_CONV NNF_CONV WEAK_DNF_CONV : ioconv)
    (AND_FORALL_THM LEFT_AND_FORALL_THM RIGHT_AND_FORALL_THM
     LEFT_OR_FORALL_THM RIGHT_OR_FORALL_THM OR_EXISTS_THM
     LEFT_OR_EXISTS_THM RIGHT_OR_EXISTS_THM LEFT_AND_EXISTS_THM
     RIGHT_AND_EXISTS_THM : thm) (K : RingParms) : ExceptT String IO RingCtx := do
  let INITIAL_CONV ← INITIAL_CONV K PRESIMP_CONV CONDS_ELIM_CONV NNF_CONV
    AND_FORALL_THM LEFT_AND_FORALL_THM RIGHT_AND_FORALL_THM
    LEFT_OR_FORALL_THM RIGHT_OR_FORALL_THM OR_EXISTS_THM
    LEFT_OR_EXISTS_THM RIGHT_OR_EXISTS_THM LEFT_AND_EXISTS_THM RIGHT_AND_EXISTS_THM
  let (pth_idom, pth_ine) ← CONJ_PAIR (← MATCH_MP G.pth_step K.RING_INTEGRAL)
  let NOT_EQ_01 ← PROVE_NZ K num_1
  return { K, Nm, G, truth, WEAK_DNF_CONV, INITIAL_CONV, pth_idom, pth_ine, NOT_EQ_01 }

/-- `IDOM_RULE = CONV_RULE(REWR_CONV pth_idom)` (grobner.ml 460). -/
def IDOM_RULE [HolBase] (R : RingCtx) : thm → ExceptT String IO thm :=
  CONV_RULE (REWR_CONV R.pth_idom)

/-- `INE_RULE n = MATCH_MP(MATCH_MP pth_ine (PROVE_NZ n))` (grobner.ml 464). -/
def INE_RULE [HolBase] (R : RingCtx) (n : Rat) (th : thm) : ExceptT String IO thm := do
  MATCH_MP (← MATCH_MP R.pth_ine (← PROVE_NZ R.K n)) th

/-- `MK_ADD th1 th2 = MK_COMB(AP_TERM ring_add_tm th1,th2)` (grobner.ml 465). -/
def MK_ADD [HolBase] (K : RingParms) (th1 th2 : thm) : ExceptT String IO thm := do
  MK_COMB (← AP_TERM K.ring_add_tm th1, th2)

/-- `execute_proof vars eths prf` (grobner.ml 467-527). -/
def execute_proof [HolBase] (R : RingCtx) (vars : List term) (eths : List thm)
    (prf : history) : ExceptT String IO thm := do
  let K := R.K
  let (x, th1) ← (SPEC_VAR (← CONJUNCT1 (← CONJUNCT2 K.RING_INTEGRAL)))
  let (_y, th2) ← (SPEC_VAR th1)
  let (z, th3) ← (SPEC_VAR th2)
  let SUB_EQ_RULE := GEN_REWRITE_RULE id
    [← SYM (← INST [(← liftExcept (mk_comb K.ring_neg_tm z), x)] th3)]
  let initpols ← eths.mapM (fun th => do
    CONV_RULE (BINOP_CONV K.RING_NORMALIZE_CONV) (← SUB_EQ_RULE th))
  let ADD_RULE (th1 th2 : thm) : ExceptT String IO thm := do
    CONV_RULE (BINOP_CONV K.RING_NORMALIZE_CONV) (← MK_COMB (← AP_TERM K.ring_add_tm th1, th2))
  let MUL_RULE (vars : List term) (m : mon) (th : thm) : ExceptT String IO thm := do
    CONV_RULE (BINOP_CONV K.RING_NORMALIZE_CONV)
      (← AP_TERM (← liftExcept (mk_comb K.ring_mul_tm (← liftExcept (holify_polynomial K R.Nm vars [m])))) th)
  let th ←
    if is_iff (strip_forall (concl K.RABINOWITSCH_THM)).2 then do
      if ← grobner_messages.get then IO.println "Generating HOL version of proof"
      let execache ← IO.mkRef ([] : List (history × thm))
      let ans ← run_proof initpols ADD_RULE MUL_RULE execache vars prf
      execache.set []
      pure ans
    else do
      if ← grobner_messages.get then IO.println "Generating HOL version of scaled proof"
      let km := vars.map (fun _ => (0 : Int))
      let execache ← IO.mkRef ([] : List (history × (Rat × thm)))
      let (_, ans) ← run_scaled_proof initpols ADD_RULE MUL_RULE km execache vars prf
      execache.set []
      pure ans
  CONV_RULE K.RING_EQ_CONV th

/-- `end_itlist` with a monadic step. -/
partial def endItlistM {α : Type} (f : α → α → ExceptT String IO α) :
    List α → ExceptT String IO α
  | [] => throw "end_itlist"
  | [x] => pure x
  | x :: xs => do f x (← endItlistM f xs)

/-- `REFUTE tm` (grobner.ml 529-580).  The OCaml rebinds `l` at the end
    (`let l,r = dest_eq(rand(concl th4))`); the certificate multiplier is
    `certL` here and the new left-hand side `l`. -/
def REFUTE [HolBase] (R : RingCtx) : ioconv := fun tm => ExceptT.run do
  let K := R.K
  if tm == R.G.false_tm then return ← ASSUME tm
  let (nths0, eths0) := partition (is_neg o concl) (CONJUNCTS (← ASSUME tm))
  let nths := filter (fun th => match rand (concl th) with
                                | .ok r => is_eq r | .error _ => false) nths0
  let eths := filter (is_eq o concl) eths0
  if eths == [] then
    let th1 ← endItlistM (fun th1 th2 => do IDOM_RULE R (← CONJ th1 th2)) nths
    let th2 ← CONV_RULE (RAND_CONV (BINOP_CONV K.RING_NORMALIZE_CONV)) th1
    let (l, _r) ← liftExcept (do dest_eq (← rand (concl th2)))
    EQ_MP (← EQF_INTRO th2) (REFL l)
  else if nths == [] && !(is_var K.ring_neg_tm) then
    let (vars, pols) ← liftExcept (grobify_equations K (← liftExcept (list_mk_conj (eths.map concl))))
    execute_proof R vars eths (← grobner_refute pols)
  else
    let (vars, certL, cert, noteqth) ←
      if nths == [] then do
        let (vars, pols) ← liftExcept (grobify_equations K (← liftExcept (list_mk_conj (eths.map concl))))
        let (l, cert) ← grobner_weak vars pols
        pure (vars, l, cert, R.NOT_EQ_01)
      else do
        let nth ← endItlistM (fun th1 th2 => do IDOM_RULE R (← CONJ th1 th2)) nths
        let (vars, polAll) ← liftExcept (grobify_equations K
          (← liftExcept (list_mk_conj ((← liftExcept (rand (concl nth))) :: eths.map concl))))
        let (pol, pols) ← match polAll with
          | p :: ps => pure (p, ps)
          | [] => throw "REFUTE: empty grobified equations"
        let (deg, l, cert) ← grobner_strong R.truth vars pols pol
        let th1 ← CONV_RULE (RAND_CONV (BINOP_CONV K.RING_NORMALIZE_CONV)) nth
        let mut th2 := R.NOT_EQ_01
        for _ in [0:deg.toNat] do
          th2 ← IDOM_RULE R (← CONJ th1 th2)
        pure (vars, l, cert, th2)
    if ← grobner_messages.get then IO.println "Translating certificate to HOL inferences"
    let cert_pos := cert.map (fun (i, p) => (i, filter (fun (c, _m) => c > num_0) p))
    let cert_neg := cert.map (fun (i, p) =>
      (i, (filter (fun (c, _m) => c < num_0) p).map (fun (c, m) => (-c, m))))
    let herts_pos ← liftExcept (cert_pos.mapM (fun (i, p) => do
      return (i, ← holify_polynomial K R.Nm vars p)))
    let herts_neg ← liftExcept (cert_neg.mapM (fun (i, p) => do
      return (i, ← holify_polynomial K R.Nm vars p)))
    let thm_fn (pols : List (Int × term)) : ExceptT String IO thm :=
      if pols == [] then do return REFL (← liftExcept (K.ring_mk_const num_0))
      else do
        endItlistM (MK_ADD K) (← pols.mapM (fun (i, p) => do
          AP_TERM (← liftExcept (mk_comb K.ring_mul_tm p)) (← liftExcept (Lib.el i.toNat eths))))
    let th1 ← thm_fn herts_pos
    let th2 ← thm_fn herts_neg
    let th3 ← CONJ (← MK_ADD K (← SYM th1) th2) noteqth
    let th4 ← CONV_RULE (RAND_CONV (BINOP_CONV K.RING_NORMALIZE_CONV)) (← INE_RULE R certL th3)
    let (l, _r) ← liftExcept (do dest_eq (← rand (concl th4)))
    EQ_MP (← EQF_INTRO th4) (REFL l)

/-- `ring_ty` (grobner.ml 581). -/
def ring_ty (K : RingParms) : Except String hol_type := do
  let (_, t1) ← dest_fun_ty (type_of K.ring_add_tm)
  return (← dest_fun_ty t1).2

/-- The inner `CHOOSES` of `RING` (grobner.ml 594-598). -/
partial def RING_CHOOSES [HolBase] :
    List term → term × thm → ExceptT String IO (term × thm)
  | [], (etm, th) => pure (etm, th)
  | ev :: oevs, (etm, th) => do
      let (etm', th') ← RING_CHOOSES oevs (etm, th)
      let ex ← liftExcept (mk_exists ev etm')
      return (ex, ← CHOOSE (ev, ← ASSUME ex) th')

/-- `RING tm` (grobner.ml 582-601). -/
def RING [HolBase] (R : RingCtx) : ioconv := fun tm => ExceptT.run do
  let rty ← liftExcept (ring_ty R.K)
  let avs := filter (fun v => type_of v == rty) (frees tm)
  let tm' ← liftExcept (list_mk_forall avs tm)
  let th1 ← ExceptT.mk (R.INITIAL_CONV (← liftExcept (mk_neg tm')))
  let (evs, bod) := strip_exists (← liftExcept (rand (concl th1)))
  if is_forall bod then throw "RING: non-universal formula"
  let th1a ← ExceptT.mk (R.WEAK_DNF_CONV bod)
  let boda ← liftExcept (rand (concl th1a))
  let th2a ← ExceptT.mk (refute_disj (REFUTE R) boda)
  let th2b ← TRANS th1a (← EQF_INTRO (← NOT_INTRO (← DISCH boda th2a)))
  let th2 ← UNDISCH (← NOT_ELIM (← EQF_ELIM th2b))
  let (finbod, th3) ← RING_CHOOSES evs (bod, th2)
  SPECL avs (← MATCH_MP (← ExceptT.mk (R.G.FINAL_RULE (← DISCH finbod th3))) th1)

/-- `ideal tms tm` (grobner.ml 602-610). -/
def ideal (R : RingCtx) (tms : List term) (tm : term) : ExceptT String IO (List term) := do
  let K := R.K
  let rawvars := itlist (grobvars K) (tm :: tms) []
  let vars := sort (fun x y => compare x y == Ordering.lt) (setify rawvars)
  let pols ← liftExcept (tms.mapM (grobify_term K vars))
  let pol ← liftExcept (grobify_term K vars tm)
  let cert ← grobner_ideal vars pols pol
  liftExcept ((upto 0 (Int.ofNat (length pols) - 1)).mapM (fun n =>
    holify_polynomial K R.Nm vars (assocd n cert [])))
/- ---------------------------------------------------------------------- -/
/- Separate out the cases.                                                -/
/- ---------------------------------------------------------------------- -/

/-- `RING parms = fst(RING_AND_IDEAL_CONV parms)` (grobner.ml 616). -/
def RING' [HolBase] (R : RingCtx) : ioconv := RING R

/-- `ideal_cofactors parms = snd(RING_AND_IDEAL_CONV parms)` (grobner.ml 618). -/
def ideal_cofactors (R : RingCtx) (tms : List term) (tm : term) :
    IO (Except String (List term)) :=
  (ideal R tms tm).run

end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj is_iff mk_exists)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/-- `pth_evenodd` (grobner.ml 644-650), part of `NUM_SIMPLIFY_CONV`. -/
def pth_evenodd [HolBase]
    (NOT_EXISTS_THM EVEN_EXISTS ODD_EXISTS NOT_EVEN NOT_ODD : thm) :
    ExceptT String IO thm := do
  prove
   r"(EVEN(x) <=> (!y. ~(x = SUC(2 * y)))) /\
     (ODD(x) <=> (!y. ~(x = 2 * y))) /\
     (~EVEN(x) <=> (!y. ~(x = 2 * y))) /\
     (~ODD(x) <=> (!y. ~(x = SUC(2 * y))))"
   (REWRITE_TAC [← GSYM NOT_EXISTS_THM, ← GSYM EVEN_EXISTS, ← GSYM ODD_EXISTS] THEN
    REWRITE_TAC [NOT_EVEN, NOT_ODD])

end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj is_iff mk_exists)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax


/-- The values `NUM_SIMPLIFY_CONV` builds before its recursive
    `NUM_MULTIPLY_CONV` (grobner.ml 628-650).  The OCaml quotes `PRE`,
    `(DIV)`, `(MOD)` and `(-)` directly; here they are read off the
    elimination theorems, since at this point in the load some of those
    quotations would parse as variables. -/
structure NumSimplifyConsts where
  pre_tm : term
  div_tm : term
  mod_tm : term
  sub_tm : term
  p_tm   : term
  n_tm   : term
  m_tm   : term
  q_tm   : term
  a_tm   : term
  b_tm   : term
  PRE_ELIM_THM''    : thm
  SUB_ELIM_THM''    : thm
  DIVMOD_ELIM_THM'' : thm
  PRE_ELIM_THM'     : thm
  SUB_ELIM_THM'     : thm
  DIVMOD_ELIM_THM'  : thm
  pth_evenodd       : thm
  deriving Inhabited

/-- Build `NumSimplifyConsts` (grobner.ml 628-650). -/
@[nospecialize]
def setupNumSimplifyConsts [HolBase] (NNF_CONV : ioconv)
    (PRE_ELIM_THM SUB_ELIM_THM DIVMOD_ELIM_THM
     PRE_ELIM_THM' SUB_ELIM_THM' DIVMOD_ELIM_THM'
     NOT_EXISTS_THM EVEN_EXISTS ODD_EXISTS NOT_EVEN NOT_ODD : thm) :
    ExceptT String IO NumSimplifyConsts := do
  -- `PRE_ELIM_THM = |- P(PRE n) <=> ...`
  let pre_tm ← liftExcept (do rator (← rand (← lhand (concl PRE_ELIM_THM))))
  -- `DIVMOD_ELIM_THM = |- P (m DIV n) (m MOD n) <=> ...`
  let (div_tm, mod_tm) ← liftExcept (do
    let l ← lhand (concl DIVMOD_ELIM_THM)
    return (← rator (← rator (← lhand l)), ← rator (← rator (← rand l))))
  -- `SUB_ELIM_THM = |- P(a - b) <=> ...`
  let sub_tm ← liftExcept (do rator (← rator (← rand (← lhand (concl SUB_ELIM_THM)))))
  let p_tm ← q r"P:num->bool"
  let n_tm ← q r"n:num"
  let m_tm ← q r"m:num"
  let q_tm ← q r"P:num->num->bool"
  let a_tm ← q r"a:num"
  let b_tm ← q r"b:num"
  let PRE_ELIM_THM'' ← CONV_RULE (RAND_CONV NNF_CONV) PRE_ELIM_THM
  let SUB_ELIM_THM'' ← CONV_RULE (RAND_CONV NNF_CONV) SUB_ELIM_THM
  let DIVMOD_ELIM_THM'' ← CONV_RULE (RAND_CONV NNF_CONV) DIVMOD_ELIM_THM
  let pth_evenodd ← pth_evenodd NOT_EXISTS_THM EVEN_EXISTS ODD_EXISTS NOT_EVEN NOT_ODD
  return {
    pre_tm, div_tm, mod_tm, sub_tm, p_tm, n_tm, m_tm, q_tm, a_tm, b_tm,
    PRE_ELIM_THM'', SUB_ELIM_THM'', DIVMOD_ELIM_THM'',
    PRE_ELIM_THM', SUB_ELIM_THM', DIVMOD_ELIM_THM', pth_evenodd }

/-- `is_pre tm = is_comb tm && rator tm = pre_tm` (grobner.ml 633). -/
def is_pre (C : NumSimplifyConsts) (tm : term) : Bool :=
  is_comb tm && (match rator tm with | .ok r => r == C.pre_tm | .error _ => false)

/-- `is_sub = is_binop `(-):num->num->num`` (grobner.ml 634). -/
def is_sub (C : NumSimplifyConsts) (tm : term) : Bool := is_binop C.sub_tm tm

/-- `is_divmod` (grobner.ml 635-637). -/
def is_divmod (C : NumSimplifyConsts) (tm : term) : Bool :=
  is_binop C.div_tm tm || is_binop C.mod_tm tm

/-- `contains_quantifier` (grobner.ml 638-639). -/
def contains_quantifier (tm : term) : Bool :=
  can (find_term (fun t => is_forall t || is_exists t || is_uexists t)) tm

/-- `BETA2_CONV = RATOR_CONV BETA_CONV THENC BETA_CONV` (grobner.ml 640). -/
def BETA2_CONV [HolBase] : ioconv := RATOR_CONV BETA_CONV THENC BETA_CONV

/-- `NUM_MULTIPLY_CONV pos tm` (grobner.ml 651-687).  Each `try` covers its
    whole block, so any failure in it falls through to the next. -/
partial def numMultiplyConv [HolBase] (C : NumSimplifyConsts) (pos : Bool) : ioconv :=
  fun tm => ExceptT.run do
  let NUM_MULTIPLY_CONV := numMultiplyConv C
  if is_forall tm || is_exists tm || is_uexists tm then
    ExceptT.mk (BINDER_CONV (NUM_MULTIPLY_CONV pos) tm)
  else if is_imp tm && contains_quantifier tm then
    ExceptT.mk (COMB2_CONV (RAND_CONV (NUM_MULTIPLY_CONV (!pos))) (NUM_MULTIPLY_CONV pos) tm)
  else if (is_conj tm || is_disj tm || is_iff tm) && contains_quantifier tm then
    ExceptT.mk (BINOP_CONV (NUM_MULTIPLY_CONV pos) tm)
  else if is_neg tm && !pos && contains_quantifier tm then
    ExceptT.mk (RAND_CONV (NUM_MULTIPLY_CONV (!pos)) tm)
  else
  tryWith (do
    let t ← liftExcept (find_term (fun t => is_pre C t && free_in t tm) tm)
    let v ← liftM (genvar (type_of t) : IO term)
    let p ← liftExcept (mk_abs v (← ExceptT.mk ((← ExceptT.mk (subst [(v, t)])) tm)))
    let th0 := if pos then C.PRE_ELIM_THM'' else C.PRE_ELIM_THM'
    let th1 ← INST [(p, C.p_tm), (← liftExcept (rand t), C.n_tm)] th0
    let th2 ← CONV_RULE (COMB2_CONV (RAND_CONV BETA_CONV) (BINDER_CONV (RAND_CONV BETA_CONV))) th1
    CONV_RULE (RAND_CONV (NUM_MULTIPLY_CONV pos)) th2) <|
  tryWith (do
    let t ← liftExcept (find_term (fun t => is_sub C t && free_in t tm) tm)
    let v ← liftM (genvar (type_of t) : IO term)
    let p ← liftExcept (mk_abs v (← ExceptT.mk ((← ExceptT.mk (subst [(v, t)])) tm)))
    let th0 := if pos then C.SUB_ELIM_THM'' else C.SUB_ELIM_THM'
    let th1 ← INST [(p, C.p_tm), (← liftExcept (lhand t), C.a_tm), (← liftExcept (rand t), C.b_tm)] th0
    let th2 ← CONV_RULE (COMB2_CONV (RAND_CONV BETA_CONV) (BINDER_CONV (RAND_CONV BETA_CONV))) th1
    CONV_RULE (RAND_CONV (NUM_MULTIPLY_CONV pos)) th2) <|
  tryWith (do
    let t ← liftExcept (find_term (fun t => is_divmod C t && free_in t tm) tm)
    let x ← liftExcept (lhand t)
    let y ← liftExcept (rand t)
    let dtm ← liftExcept (do mk_comb (← mk_comb C.div_tm x) y)
    let mtm ← liftExcept (do mk_comb (← mk_comb C.mod_tm x) y)
    let vd ← liftM (genvar (type_of dtm) : IO term)
    let vm ← liftM (genvar (type_of mtm) : IO term)
    let p ← liftExcept (list_mk_abs [vd, vm] (← ExceptT.mk ((← ExceptT.mk (subst [(vd, dtm), (vm, mtm)])) tm)))
    let th0 := if pos then C.DIVMOD_ELIM_THM'' else C.DIVMOD_ELIM_THM'
    let th1 ← INST [(p, C.q_tm), (x, C.m_tm), (y, C.n_tm)] th0
    let th2 ← CONV_RULE (COMB2_CONV (RAND_CONV BETA2_CONV)
                (BINDER_CONV (BINDER_CONV (RAND_CONV BETA2_CONV)))) th1
    CONV_RULE (RAND_CONV (NUM_MULTIPLY_CONV pos)) th2) <|
  pure (REFL tm)
/- ---------------------------------------------------------------------- -/
/- Simplify a natural number assertion to eliminate conditionals, DIV,    -/
/- MOD, PRE, cutoff subtraction, EVEN and ODD. Try to do it in a way that -/
/- makes new quantifiers universal. At the moment we don't split "<=>"    -/
/- which would make this quantifier selection work there too; better to   -/
/- do NNF first if you care. This also applies to EVEN and ODD.           -/
/- ---------------------------------------------------------------------- -/

/-- `NUM_SIMPLIFY_CONV` (grobner.ml 651-703).  The `pth_evenodd` net is
    built here, once. -/
def NUM_SIMPLIFY_CONV [HolBase] (C : NumSimplifyConsts)
    (NUM_REDUCE_CONV CONDS_CELIM_CONV NNF_CONV : ioconv) : ExceptT String IO ioconv := do
  let evenodd ← GEN_REWRITE_CONV_NET ONCE_DEPTH_CONV [C.pth_evenodd]
  return NUM_REDUCE_CONV THENC
         CONDS_CELIM_CONV THENC
         NNF_CONV THENC
         numMultiplyConv C true THENC
         NUM_REDUCE_CONV THENC
         evenodd

end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj is_iff mk_exists)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/-- `NUM_INTEGRAL_LEMMA` (grobner.ml 708-715), local to `NUM_RING`. -/
def NUM_INTEGRAL_LEMMA [HolBase]
    (ADD_AC LEFT_ADD_DISTRIB RIGHT_ADD_DISTRIB ADD_ASSOC
     EQ_ADD_LCANCEL EQ_ADD_LCANCEL_0 MULT_EQ_0 : thm) :
    ExceptT String IO thm := do
  prove
   r"(w = x + d) /\ (y = z + e)
     ==> ((w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))"
   (DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
    REWRITE_TAC [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, ← GSYM ADD_ASSOC] THEN
    ONCE_REWRITE_TAC [← AC ADD_AC
     (← q r"a + b + c + d + e = a + c + e + b + d")] THEN
    REWRITE_TAC [EQ_ADD_LCANCEL, EQ_ADD_LCANCEL_0, MULT_EQ_0])

/-- `NUM_INTEGRAL` (grobner.ml 716-726), local to `NUM_RING`. -/
def NUM_INTEGRAL [HolBase]
    (ASM_MESON_TAC : List thm → tactic)
    (NUM_INTEGRAL_LEMMA MULT_CLAUSES EQ_ADD_LCANCEL LE_CASES LE_EXISTS
     ADD_SYM MULT_SYM : thm) :
    ExceptT String IO thm := do
  prove
   r"(!x. 0 * x = 0) /\
     (!x y z. (x + y = x + z) <=> (y = z)) /\
     (!w x y z. (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))"
   (REWRITE_TAC [MULT_CLAUSES, EQ_ADD_LCANCEL] THEN
    REPEAT GEN_TAC THEN
    DISJ_CASES_TAC (← SPECL [← q r"w:num", ← q r"x:num"] LE_CASES) THEN
    DISJ_CASES_TAC (← SPECL [← q r"y:num", ← q r"z:num"] LE_CASES) THEN
    REPEAT (FIRST_X_ASSUM
     (fun th => tactic_of do
        pure ((CHOOSE_THEN SUBST1_TAC) (← REWRITE_RULE [LE_EXISTS] th)))) THEN
    ASM_MESON_TAC [NUM_INTEGRAL_LEMMA, ADD_SYM, MULT_SYM])

end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj is_iff mk_exists)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax


/-- The natural-number parameter tuple passed to `RING` (grobner.ml 727-732):
    `dest_numeral, mk_numeral, NUM_EQ_CONV, genvar bool_ty, (+), genvar
    bool_ty, genvar bool_ty, (*), genvar bool_ty, (EXP), NUM_INTEGRAL,
    TRUTH, NUM_NORMALIZE_CONV`.  OCaml evaluates the tuple right to left, so
    the four `genvar`s are made in the order div, inv, sub, neg.  The `num`
    constants are passed in. -/
def numRingParms (Nm : HolMath.Nums.NumeralConsts)
    (NUM_EQ_CONV NUM_NORMALIZE_CONV : ioconv)
    (add_tm mul_tm exp_tm : term)
    (NUM_INTEGRAL TRUTH : thm) : IO RingParms := do
  let div_dummy ← genvar bool_ty
  let inv_dummy ← genvar bool_ty
  let sub_dummy ← genvar bool_ty
  let neg_dummy ← genvar bool_ty
  return {
    ring_dest_const     := dest_numeral
    ring_mk_const       := HolMath.Nums.mk_numeral Nm
    RING_EQ_CONV        := NUM_EQ_CONV
    ring_neg_tm         := neg_dummy
    ring_add_tm         := add_tm
    ring_sub_tm         := sub_dummy
    ring_inv_tm         := inv_dummy
    ring_mul_tm         := mul_tm
    ring_div_tm         := div_dummy
    ring_pow_tm         := exp_tm
    RING_INTEGRAL       := NUM_INTEGRAL
    RABINOWITSCH_THM    := TRUTH
    RING_NORMALIZE_CONV := NUM_NORMALIZE_CONV }
/- ---------------------------------------------------------------------- -/
/- Natural number version of ring procedure with this normalization.      -/
/- ---------------------------------------------------------------------- -/

/-- `NUM_RING` (grobner.ml 707-737): builds `initconv` (and its `ADD1` net)
    once and returns the procedure.  `rawring` is `RING` at the
    natural-number parameters. -/
def NUM_RING [HolBase] (NUM_SIMPLIFY_CONV : ioconv) (ADD1 : thm)
    (rawring : ioconv) : ExceptT String IO ioconv := do
  let initconv := NUM_SIMPLIFY_CONV THENC (← GEN_REWRITE_CONV_NET DEPTH_CONV [ADD1])
  let t_tm ← q r"T"
  return fun tm => ExceptT.run do
    let th ← ExceptT.mk (initconv tm)
    let r ← liftExcept (rand (concl th))
    if r == t_tm then pure th
    else EQ_MP (← SYM th) (← ExceptT.mk (rawring r))

end

end HolMath.Grobner
