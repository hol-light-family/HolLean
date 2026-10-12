/- File: Quot.lean
Tools for defining quotient types and lifting first order theorems (`quot.ml`).
Original       John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026
-/

import HolCore.Bool
import HolCore.Equal
import HolCore.Drule
import HolCore.Tactics
import HolCore.Simp
import HolCore.Parser
import HolCore.Theorems

open HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Bool HolCore.Equal
     HolCore.Drule HolCore.Tactics HolCore.Simp HolCore.Parser HolCore.Theorems

namespace HolCore.Quot

set_option maxRecDepth 4000

/- ---------------------------------------------------------------------- -/
/- Given a type name "ty" and a curried binary relation R, this defines   -/
/- a new type "ty" of R-equivalence classes. The abstraction and          -/
/- representation functions for the new type are called "mk_ty" and       -/
/- "dest_ty". The type bijections (after beta-conversion) are returned:   -/
/-                                                                        -/
/-             |- mk_ty (dest_ty a) = a                                   -/
/-                                                                        -/
/-             |- (?x. r = R x) <=> (dest_ty (mk_ty r) = r)               -/
/- ---------------------------------------------------------------------- -/

/-- `define_quotient_type tyname (absname, repname) eqv`: define a new type of
    `eqv`-equivalence classes.  Returns the two (beta-converted) type
    bijection theorems.  Faithful to `quot.ml`'s `define_quotient_type`. -/
def define_quotient_type (B : BoolThms)
    (tyname : String) (absrep : String × String) (eqv : term) :
    IO (Except String (thm × thm)) := ExceptT.run do
  let (absname, repname) := absrep
  let ty ← liftExcept do
    let (_, args) ← dest_type (type_of eqv)
    hd args
  let pty ← ExceptT.mk (mk_fun_ty ty bool_ty)
  let mkEq ← (mk_eq : IO (Except String ((term × term) → Except String term)))
  -- `pred = \s. ?x. s = R x`; instantiate at `R x` and derive the predicate
  -- witness `th2` fed to `new_basic_type_definition`.
  let th2 ← liftExcept do
    let s := mk_var "s" pty
    let x := mk_var "x" ty
    let eqvx ← mk_comb eqv x
    let pred ← mk_abs s (← mk_exists x (← mkEq (s, eqvx)))
    let th0 ← BETA_CONV (← mk_comb pred eqvx)
    let th1 ← B.EXISTS (← rand (concl th0), x) (REFL eqvx)
    EQ_MP (← SYM th0) th1
  let (abs, rep) ← ExceptT.mk (new_basic_type_definition tyname absname repname th2)
  let rep' ← liftExcept (CONV_RULE (LAND_CONV BETA_CONV) rep)
  pure (abs, rep')

/- ---------------------------------------------------------------------- -/
/- Given a welldefinedness theorem for a curried function f, of the form: -/
/-                                                                        -/
/- |- !x1 x1' .. xn xn'. (x1 == x1') /\ ... /\ (xn == xn')                -/
/-                       ==> (f x1 .. xn == f x1' .. f nx')               -/
/-                                                                        -/
/- where each "==" is either equality or some fixed binary relation R, a  -/
/- new operator called "opname" is introduced which lifts "f" up to the   -/
/- R-equivalence classes. Two theorems are returned: the actual definition-/
/- and a useful consequence for lifting theorems.                         -/
/-                                                                        -/
/- The function also needs the second (more complicated) type bijection,  -/
/- and the reflexivity and transitivity (not symmetry!) of the equivalence-/
/- relation. The use also gives a name for the new function.              -/
/- ---------------------------------------------------------------------- -/

/-- `lift_function B SELECT_LEMMA ETA_CONV tybij2 (refl_th, trans_th) fname wth`:
    introduce an operator `fname` lifting `f` to the `R`-equivalence classes.
    Returns `(eth, GSYM th9)`.  `SELECT_LEMMA` (`|- !x. (@y. x = y) = x`) and
    `ETA_CONV` are supplied pre-built (proved once, in `Session`).  Faithful to
    `quot.ml`'s `lift_function`. -/
def lift_function (B : BoolThms) (SELECT_LEMMA : thm) (ETA_CONV : conv)
    (tybij2 : thm) (reflTrans : thm × thm) (fname : String) (wth : thm) :
    IO (Except String (thm × thm)) := ExceptT.run do
  let (refl_th, trans_th) := reflTrans
  let mkEq ← (mk_eq : IO (Except String ((term × term) → Except String term)))
  -- Take apart the second type bijection to recover the relation `eqv`, the
  -- rep/abs functions (`dest`/`mk`), and the class-membership type `ety`; then
  -- split the well-definedness theorem into hypotheses and conclusion.
  let (eqv, xtm, dest, mk, rtm, eqvx, ety) ← liftExcept do
    let (tybl, tybr) ← dest_comb (concl tybij2)
    let eqvx ← rand (← body (← rand (← rand tybl)))
    let (eqv, xtm) ← dest_comb eqvx
    let (dmr, rtm) ← dest_eq tybr
    let (dest, mrt) ← dest_comb dmr
    let mk ← rator mrt
    pure (eqv, xtm, dest, mk, rtm, eqvx, type_of mrt)
  let wtm := repeat' (fun t => (Prod.snd <$> dest_forall t)) (concl wth)
  let wfvs := frees wtm
  let (hyps, con) : List term × term :=
    match Bool.dest_imp wtm with
    | .ok (l, r) => (conjuncts l, r)
    | .error _ => ([], wtm)
  let (eqs, rels) := partition is_eq hyps
  -- Relational/equality argument variables, fresh class variables `evs`, and the
  -- body of the operator's defining SELECT term.
  let (rvs, qvs, evs, u, datm) ← liftExcept do
    let rvs ← rels.mapM lhand
    let qvs ← eqs.mapM lhs
    let cand ← rvs.mapM (fun v => do let (n, _) ← dest_var v; pure (mk_var n ety))
    let evs ← variants wfvs cand
    let mems ← (← map2 (fun rv ev => do mk_comb (← mk_comb dest ev) rv) rvs evs).mapM id
    let (lcon, rcon) ← dest_comb con
    let u ← variant (evs ++ wfvs) (mk_var "u" (type_of rcon))
    let dbod ← list_mk_conj ((← mk_comb lcon u) :: mems)
    let datm ← mk_abs u (← list_mk_exists rvs dbod)
    pure (rvs, qvs, evs, u, datm)
  let defn ←
    if is_eq con then ExceptT.mk (list_mk_icomb "@" [datm])
    else liftExcept (mk_comb mk datm)
  -- Each argument keeps its `lhs` (for the equality hyps) or its paired class
  -- variable `ev` (for the relational hyps); introduce the new operator.
  let (newargs, rdef) ← liftExcept do
    let rvevs ← zip rvs evs
    let newargs ← hyps.mapM (fun e =>
      match lhs e with | .ok v => .ok v | .error _ => do assoc (← lhand e) rvevs)
    pure (newargs, ← list_mk_abs newargs defn)
  let ldef := mk_var fname (type_of rdef)
  let dth ← ExceptT.mk (new_definition B (← liftExcept (mkEq (ldef, rdef))))
  let eth ← liftExcept (rev_itlistM
    (fun v th => do CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM th v)) newargs dth)
  -- Rewrite the definition through the type bijection to expose the SELECT body.
  let (dme_th, ith) ← liftExcept do
    let targs ← rvs.mapM (fun v => do mk_comb mk (← mk_comb eqv v))
    let dme_th ← do
      let th ← INST [(eqvx, rtm)] tybij2
      EQ_MP th (← B.EXISTS (← lhs (concl th), xtm) (REFL eqvx))
    let ith ← INST (← zip targs evs) eth
    pure (dme_th, ith)
  let jth ← ExceptT.mk (SUBS (← liftExcept (rvs.mapM (fun v => INST [(v, xtm)] dme_th))) ith)
  let (apop, extm) ← liftExcept do
    let (apop, uxtm) ← dest_comb (← rand (concl jth))
    pure (apop, ← body uxtm)
  let (evs, bod) := strip_exists extm      -- NB: shadows the earlier `evs`
  let th1 ← liftExcept (ASSUME bod)
  -- Forward direction: from the SELECT body, discharge the memberships against
  -- the well-definedness theorem (chaining through transitivity if needed).
  let th2 ←
    if evs == [] then liftExcept (Except.ok th1 : Except String thm)
    else do
      let (th2a, th2c) ← liftExcept do
        let (th2a, th2b) ← B.CONJ_PAIR th1
        let ethlist := B.CONJUNCTS th2b ++ qvs.map REFL
        let picked ← hyps.mapM (fun v => do
          let lv ← lhand v
          find (fun t => match lhand (concl t) with | .ok l => l == lv | .error _ => false) ethlist)
        pure (th2a, ← end_itlistM B.CONJ picked)
      let th2d ← ExceptT.mk (MATCH_MP B wth th2c)
      let th2e ←
        match TRANS th2d th2a with
        | .ok t => liftExcept (Except.ok t : Except String thm)
        | .error _ => ExceptT.mk (MATCH_MP B trans_th (← liftExcept (B.CONJ th2d th2a)))
      liftExcept (itlistM B.SIMPLE_CHOOSE evs th2e)
  -- Reverse direction, then combine into an equivalence and fold into `jth`.
  let (th4, th5) ← liftExcept do
    let th3 ← ASSUME (concl th2)
    let th4 ← end_itlistM B.CONJ (th3 :: (← rvs.mapM (fun v => B.SPEC v refl_th)))
    let th5 ← itlistM B.SIMPLE_EXISTS evs (← ASSUME bod)
    pure (th4, th5)
  let th6 ← ExceptT.mk (MATCH_MP B (← liftExcept (B.DISCH_ALL th5)) th4)
  let th8 ← liftExcept do
    let th7 ← B.IMP_ANTISYM_RULE (← B.DISCH_ALL th2) (← B.DISCH_ALL th6)
    TRANS jth (← AP_TERM apop (← ABS u th7))
  -- Final tidy-up: collapse the SELECT (`SELECT_LEMMA`) or eta-reduce (`ETA_CONV`).
  -- (`REWR_CONV` is an `ioconv` here, so its `RAND_CONV` is applied in IO.)
  let th9 ←
    if is_eq con then
      ExceptT.mk (Simp.convRuleIO (Simp.randConvIO (REWR_CONV B SELECT_LEMMA)) th8)
    else
      liftExcept (CONV_RULE (RAND_CONV (RAND_CONV ETA_CONV)) th8)
  pure (eth, ← liftExcept (GSYM th9))

/- ---------------------------------------------------------------------- -/
/- Lifts a theorem. This can be done by higher order rewriting alone.     -/
/-                                                                        -/
/- NB! All and only the first order variables must be bound by            -/
/- quantifiers.                                                           -/
/- ---------------------------------------------------------------------- -/

/-- `lift_theorem B pth tybij (refl_th, sym_th, trans_th) trths`: lift a theorem
    through the quotient.  `pth` is the auxiliary implication theorem (proved
    once, in `Session`).  Returns a `REWRITE_RULE (ith :: trths)`-style rule as
    an applied result.  Faithful to `quot.ml`'s `lift_theorem`. -/
def lift_theorem (B : BoolThms) (pth : thm)
    (tybij : thm × thm) (reflSymTrans : thm × thm × thm) (trths : List thm) (th : thm) :
    IO (Except String thm) := ExceptT.run do
  let (refl_th, sym_th, trans_th) := reflSymTrans
  let cth ← liftExcept do
    let tybij1 ← B.GEN_ALL tybij.1
    let tybij2 ← B.GEN_ALL tybij.2
    end_itlistM B.CONJ [refl_th, sym_th, trans_th, tybij1, tybij2]
  let ith ← ExceptT.mk (MATCH_MP B pth cth)
  ExceptT.mk (REWRITE_RULE B (ith :: trths) th)

end HolCore.Quot
