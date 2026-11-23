/- File: Bool.lean
Boolean theory including (intuitionistic) defs of logical connectives.
John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026 -/

import HolCore.Equal
import HolCore.Basics
import HolCore.Fusion
import HolCore.Printer
import HolCore.Preterm
import HolCore.Parser

open HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Equal HolCore.Printer HolCore.Preterm

namespace HolCore.Bool

/- Special syntax for Boolean equations (IFF). -/

/-- Is `tm` a Boolean equation (`=` at type `bool -> bool -> _`)? -/
def is_iff (tm : term) : Bool :=
  match tm with
  | .Comb (.Comb (.Const "=" (.Tyapp "fun" [.Tyapp "bool" [], _])) _) _ => true
  | _ => false

/-- Destruct a Boolean equation into its two sides; fails with "dest_iff". -/
def dest_iff (tm : term) : Except String (term × term) :=
  match tm with
  | .Comb (.Comb (.Const "=" (.Tyapp "fun" [.Tyapp "bool" [], _])) l) r => .ok (l, r)
  | _ => failwith "dest_iff"

/- Rule allowing easy instantiation of polymorphic proformas. -/
/-- Instantiate a polymorphic proforma by types then terms; fails with
    "PINST". -/
def PINST (tyin : List (hol_type × hol_type)) (tmin : List (term × term)) :
    thm → Except String thm :=
  let iterm_fn := INST (tmin.map (F_F I (inst tyin)))
  let itype_fn := INST_TYPE tyin
  fun th => (do iterm_fn (← itype_fn th)).mapError (fun _ => "PINST")

/- The theorems and derived rules established by loading bool.ml, produced
once by `setupBool` and returned as a record. -/

/-- The theorems and derived rules produced by loading `bool.ml`. -/
structure BoolThms where
  T_DEF     : thm
  TRUTH     : thm
  EQT_ELIM  : thm → Except String thm
  EQT_INTRO : thm → Except String thm
  AND_DEF   : thm
  CONJ      : thm → thm → Except String thm
  CONJUNCT1 : thm → Except String thm
  CONJUNCT2 : thm → Except String thm
  CONJ_PAIR : thm → Except String (thm × thm)
  CONJUNCTS : thm → List thm
  IMP_DEF          : thm
  MP               : thm → thm → Except String thm
  DISCH            : term → thm → Except String thm
  DISCH_ALL        : thm → Except String thm
  UNDISCH          : thm → Except String thm
  UNDISCH_ALL      : thm → Except String thm
  IMP_ANTISYM_RULE : thm → thm → Except String thm
  ADD_ASSUM        : term → thm → Except String thm
  EQ_IMP_RULE      : thm → Except String (thm × thm)
  IMP_TRANS        : thm → thm → Except String thm
  FORALL_DEF : thm
  SPEC       : term → thm → Except String thm
  SPECL      : List term → thm → Except String thm
  SPEC_VAR   : thm → Except String (term × thm)
  SPEC_ALL   : thm → Except String thm
  GEN        : term → thm → Except String thm
  GENL       : List term → thm → Except String thm
  GEN_ALL    : thm → Except String thm
  ISPEC      : term → thm → Except String thm
  ISPECL     : List term → thm → Except String thm
  EXISTS_DEF    : thm
  EXISTS        : term × term → thm → Except String thm
  SIMPLE_EXISTS : term → thm → Except String thm
  CHOOSE        : term × thm → thm → Except String thm
  SIMPLE_CHOOSE : term → thm → Except String thm
  OR_DEF            : thm
  DISJ1             : thm → term → Except String thm
  DISJ2             : term → thm → Except String thm
  DISJ_CASES        : thm → thm → thm → Except String thm
  SIMPLE_DISJ_CASES : thm → thm → Except String thm
  F_DEF     : thm
  NOT_DEF   : thm
  NOT_ELIM  : thm → Except String thm
  NOT_INTRO : thm → Except String thm
  EQF_INTRO : thm → Except String thm
  EQF_ELIM  : thm → Except String thm
  CONTR     : term → thm → Except String thm
  EXISTS_UNIQUE_DEF : thm
  EXISTENCE         : thm → Except String thm

/- Binary-operator term builder: `(op l) r` with `op` at `bool→bool→bool`.
   (Built directly, avoiding the IO `mk_binary` factory.) -/
private def bbbTy : hol_type := .Tyapp "fun" [bool_ty, .Tyapp "fun" [bool_ty, bool_ty]]
private def mkBinop (op : String) (l r : term) : Except String term := do
  mk_comb (← mk_comb (.Const op bbbTy) l) r

/- `mk_binary s` (basics.ml 78): `try mk_comb(mk_comb(c,l),r) with Failure _ ->
   failwith "mk_binary"`.  Used by mk_conj, mk_imp and mk_disj; mk_iff
   (bool.ml 49) calls mk_comb directly and keeps its message. -/
private def mkBinary (op : String) (l r : term) : Except String term :=
  match mkBinop op l r with
  | .ok t => .ok t
  | .error _ => .error "mk_binary"

/- Syntax for conjunctions. -/
/-- Build a conjunction `l /\ r`. -/
def mk_conj (l r : term) : Except String term := mkBinary "/\\" l r
/-- Destruct a conjunction into its two conjuncts. -/
def dest_conj : term → Except String (term × term) := dest_binary "/\\"
/-- Build the conjunction of a non-empty list of terms. -/
def list_mk_conj (tms : List term) : Except String term :=
  (end_itlist (fun a b => do mk_conj (← a) (← b)) (tms.map .ok)).bind id

/- Special syntax for Boolean equations (`<=>`, which is `=` at bool). -/
/-- Build a Boolean equation `l <=> r` (i.e. `=` at type `bool`). -/
def mk_iff (l r : term) : Except String term := mkBinop "=" l r

/- Syntax for implications. -/
/-- Build an implication `l ==> r`. -/
def mk_imp (l r : term) : Except String term := mkBinary "==>" l r
/-- Destruct an implication into antecedent and consequent. -/
def dest_imp : term → Except String (term × term) := dest_binary "==>"

/- Universal quantification of `bod` over `v`: `(!) (\v. bod)`, with the `!`
   constant at `(type_of v → bool) → bool`. (Built directly, like `mk_exists`,
   avoiding the IO `mk_binder "!"` factory.) -/
/-- Universally quantify `bod` over the variable `v`. -/
def mk_forall (v : term) (bod : term) : Except String term := do
  let vty := type_of v
  let allTy : hol_type := .Tyapp "fun" [.Tyapp "fun" [vty, bool_ty], bool_ty]
  mk_comb (.Const "!" allTy) (← mk_abs v bod)

/- Iterated universal quantification (right fold). -/
/-- Universally quantify `bod` over a list of variables. -/
def list_mk_forall (vs : List term) (bod : term) : Except String term :=
  itlist (fun v acc => acc.bind (fun b => mk_forall v b)) vs (.ok bod)

/- Existential quantification of `bod` over `v`: `(?) (\v. bod)`, with the
   `?` constant at the type `(type_of v → bool) → bool`. (Avoids the IO
   `mk_binder "?"` factory by building directly.) -/
/-- Existentially quantify `bod` over the variable `v`. -/
def mk_exists (v : term) (bod : term) : Except String term := do
  let vty := type_of v
  let exTy : hol_type := .Tyapp "fun" [.Tyapp "fun" [vty, bool_ty], bool_ty]
  mk_comb (.Const "?" exTy) (← mk_abs v bod)

/- Iterated existential quantification (right fold). -/
/-- Existentially quantify `bod` over a list of variables. -/
def list_mk_exists (vs : List term) (bod : term) : Except String term :=
  itlist (fun v acc => acc.bind (fun b => mk_exists v b)) vs (.ok bod)

/- Syntax for disjunctions. -/
/-- Build a disjunction `l \/ r`. -/
def mk_disj (l r : term) : Except String term := mkBinary "\\/" l r
/-- Destruct a disjunction into its two disjuncts. -/
def dest_disj : term → Except String (term × term) := dest_binary "\\/"
/-- Build the disjunction of a non-empty list of terms. -/
def list_mk_disj (tms : List term) : Except String term :=
  (end_itlist (fun a b => do mk_disj (← a) (← b)) (tms.map .ok)).bind id

/- Negation syntax. -/
/-- Build a negation `~ tm`; fails with "mk_neg". -/
def mk_neg (tm : term) : Except String term :=
  (mk_comb (.Const "~" (.Tyapp "fun" [bool_ty, bool_ty])) tm).mapError (fun _ => "mk_neg")

/- Unique-existence quantification: `(?!) (\v. bod)` at `(type_of v → bool) → bool`. -/
/-- Uniquely-existentially quantify `bod` over the variable `v`. -/
def mk_uexists (v : term) (bod : term) : Except String term := do
  let vty := type_of v
  let uexTy : hol_type := .Tyapp "fun" [.Tyapp "fun" [vty, bool_ty], bool_ty]
  mk_comb (.Const "?!" uexTy) (← mk_abs v bod)

/- Monadic fold helpers (`itlistM`/`rev_itlistM`/`itlist2M`) now live in Lib. -/

/- DISCH_ALL, parameterized by DISCH (recursive; discharges all hypotheses). -/
/-- Discharge all hypotheses of a theorem, given the `DISCH` rule. -/
partial def DISCH_ALL (DISCH : term → thm → Except String thm) (th : thm) :
    Except String thm :=
  match hyp th with
  | h :: _ => match DISCH h th with
              | .ok th' => DISCH_ALL DISCH th'
              | .error _ => .ok th
  | [] => .ok th

/- UNDISCH_ALL, parameterized by UNDISCH (recursive). -/
/-- Undischarge all leading antecedents of a theorem, given `UNDISCH`. -/
partial def UNDISCH_ALL (UNDISCH : thm → Except String thm) (th : thm) :
    Except String thm :=
  if is_imp (concl th) then
    match UNDISCH th with
    | .ok th' => UNDISCH_ALL UNDISCH th'
    | .error _ => .ok th
  else .ok th

/- SPEC_ALL (bool.ml 271-284): the same variables as iterating SPEC_VAR, but
   the free variables of the theorem are computed only once: `SPEC v'` on
   `|- !v. bod` adds `v'` to them just when `v` is free in `bod`. -/
/-- `spec_all fvs th`, given `SPEC`. -/
partial def specAllAux (SPEC : term → thm → Except String thm) (fvs : List term) (th : thm) :
    Except String thm := do
  let tm := concl th
  if !(is_forall tm) then return th
  let (v, bod) ← dest_forall tm
  let v' ← variant fvs v
  specAllAux SPEC (if vfree_in v bod then v' :: fvs else fvs) (← SPEC v' th)
/-- Specialize away all leading universal quantifiers, given `SPEC`. -/
def SPEC_ALL (SPEC : term → thm → Except String thm) (th : thm) : Except String thm :=
  if is_forall (concl th) then specAllAux SPEC (thm_frees th) th else .ok th

/- Run all of bool.ml's definitions and derived rules once, in order,
returning the resulting theorems and rules. -/
/-- Run all of `bool.ml`'s definitions and derived rules once, in order.
    Each quotation of bool.ml is parsed where OCaml parses it, in OCaml's
    order (arguments right to left), since parsing uses type-variable
    numbers. -/
def setupBool : ExceptT String IO BoolThms := do
  let pt (s : String) : ExceptT String IO term := ExceptT.mk (HolCore.Parser.parse_term s)
  -- Set up parse status of basic and derived logical constants.
  parse_as_prefix "~"
  parse_as_binder "\\"
  parse_as_binder "!"
  parse_as_binder "?"
  parse_as_binder "?!"
  parse_as_infix ("==>", (4, "right"))
  parse_as_infix ("\\/", (6, "right"))
  parse_as_infix ("/\\", (8, "right"))
  -- Set up more orthodox notation for equations and equivalence.
  parse_as_infix ("<=>", (2, "right"))
  -- `override_interface("<=>",...)` (bool.ml:32): top-level stmt, raises on
  -- failure; propagate via ExceptT.mk.
  let _ ← ExceptT.mk (override_interface "<=>" (← pt "(=):bool->bool->bool"))
  parse_as_infix ("=", (12, "right"))
  -- mk_iff's `eq_tm = `(<=>)`` (bool.ml 50); `mk_iff` builds the term directly.
  let _ ← pt "(<=>)"

  -- Useful derived deductive rule.
  let PROVE_HYP : thm → thm → Except String thm := fun ath bth =>
    if exists' (fun h => aconv (concl ath) h) (hyp bth) then
      EQ_MP (DEDUCT_ANTISYM_RULE ath bth) ath
    else .ok bth

/- ---------------------------------------------------------------------- -/
/- Rules for T                                                            -/
/- ---------------------------------------------------------------------- -/
  -- Rules for T
  -- T_DEF = new_basic_definition `T = ((\p:bool. p) = (\p:bool. p))`
  let T_DEF ← new_basic_definition (← pt "T = ((\\p:bool. p) = (\\p:bool. p))")

  -- TRUTH = EQ_MP (SYM T_DEF) (REFL `\p:bool. p`)
  let idfn ← pt "\\p:bool. p"
  let TRUTH ← liftExcept (do EQ_MP (← SYM T_DEF) (REFL idfn))

  -- EQT_ELIM th = try EQ_MP (SYM th) TRUTH with _ -> failwith "EQT_ELIM"
  let EQT_ELIM : thm → Except String thm := fun th =>
    (do EQ_MP (← SYM th) TRUTH).mapError (fun _ => "EQT_ELIM")

  -- EQT_INTRO: proforma over `t:bool`, then fun th -> EQ_MP (INST[concl th,t] pth) th
  let t ← pt "t:bool"
  let EQT_INTRO_pth ← liftExcept (do
    let th1 := DEDUCT_ANTISYM_RULE (← ASSUME t) TRUTH
    let th2 ← EQT_ELIM (← ASSUME (concl th1))
    pure (DEDUCT_ANTISYM_RULE th2 th1))
  let EQT_INTRO : thm → Except String thm := fun th =>
    (do EQ_MP (← INST [(concl th, t)] EQT_INTRO_pth) th).mapError (fun _ => "EQT_INTRO")

/- ---------------------------------------------------------------------- -/
/- Rules for /\                                                           -/
/- ---------------------------------------------------------------------- -/
  -- Rules for /\
  -- AND_DEF = `(/\) = \p q. (\f:bool->bool->bool. f p q) = (\f. f T T)`
  let AND_DEF ← new_basic_definition
    (← pt "(/\\) = \\p q. (\\f:bool->bool->bool. f p q) = (\\f. f T T)")

  -- CONJ's `f`, `p`, `q`, and pth1's `\(p:bool) (q:bool). q`.
  let f ← pt "f:bool->bool->bool"
  let p ← pt "p:bool"
  let q ← pt "q:bool"
  let selQ ← pt "\\(p:bool) (q:bool). q"

  -- CONJ
  let CONJ_pth1 ← liftExcept (do
    let th1 ← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM AND_DEF p)
    let th2 ← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM th1 q)
    let th3 ← EQ_MP th2 (← ASSUME (← mk_conj p q))
    EQT_ELIM (← BETA_RULE (← AP_THM th3 selQ)))
  let CONJ_pth2 ← liftExcept (do
    let pth ← ASSUME p
    let qth ← ASSUME q
    let th1 ← MK_COMB (← AP_TERM f (← EQT_INTRO pth)) (← EQT_INTRO qth)
    let th2 ← ABS f th1
    let th3 ← BETA_RULE (← AP_THM (← AP_THM AND_DEF p) q)
    EQ_MP (← SYM th3) th2)
  let CONJ_pth := DEDUCT_ANTISYM_RULE CONJ_pth1 CONJ_pth2
  let CONJ : thm → thm → Except String thm := fun th1 th2 => do
    let th ← INST [(concl th1, p), (concl th2, q)] CONJ_pth
    EQ_MP (← EQ_MP (DEDUCT_ANTISYM_RULE th1 th) th1) th2

  -- CONJUNCT1 / CONJUNCT2  (proformas over P, Q; each binds its own)
  let cP ← pt "P:bool"
  let cQ ← pt "Q:bool"
  let selP ← pt "\\(p:bool) (q:bool). p"
  let conj1_pth ← liftExcept (do
    let th1 ← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM AND_DEF cP)
    let th2 ← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM th1 cQ)
    let th3 ← EQ_MP th2 (← ASSUME (← mk_conj cP cQ))
    EQT_ELIM (← BETA_RULE (← AP_THM th3 selP)))
  let _ ← pt "P:bool"
  let _ ← pt "Q:bool"
  let selQ2 ← pt "\\(p:bool) (q:bool). q"
  let conj2_pth ← liftExcept (do
    let th1 ← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM AND_DEF cP)
    let th2 ← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM th1 cQ)
    let th3 ← EQ_MP th2 (← ASSUME (← mk_conj cP cQ))
    EQT_ELIM (← BETA_RULE (← AP_THM th3 selQ2)))
  let CONJUNCT1 : thm → Except String thm := fun th =>
    (do let (l, r) ← dest_conj (concl th)
        EQ_MP (DEDUCT_ANTISYM_RULE th (← INST [(l, cP), (r, cQ)] conj1_pth)) th
    ).mapError (fun _ => "CONJUNCT1")
  let CONJUNCT2 : thm → Except String thm := fun th =>
    (do let (l, r) ← dest_conj (concl th)
        EQ_MP (DEDUCT_ANTISYM_RULE th (← INST [(l, cP), (r, cQ)] conj2_pth)) th
    ).mapError (fun _ => "CONJUNCT2")
  let CONJ_PAIR : thm → Except String (thm × thm) := fun th =>
    (do return (← CONJUNCT1 th, ← CONJUNCT2 th)).mapError (fun _ => "CONJ_PAIR: Not a conjunction")
  let CONJUNCTS : thm → List thm := striplist CONJ_PAIR

/- ---------------------------------------------------------------------- -/
/- Rules for ==>                                                          -/
/- ---------------------------------------------------------------------- -/
  -- Rules for ==>
  -- IMP_DEF = `(==>) = \p q. p /\ q <=> p`
  let IMP_DEF ← new_basic_definition (← pt "(==>) = \\p q. p /\\ q <=> p")
  -- MP's `p`, `q`.
  let _ ← pt "p:bool"
  let _ ← pt "q:bool"

  -- MP
  let MP_pth ← liftExcept (do
    let th1 ← BETA_RULE (← AP_THM (← AP_THM IMP_DEF p) q)
    let th2 ← CONJ (← ASSUME p) (← ASSUME q)
    let th3 ← CONJUNCT1 (← ASSUME (← mk_conj p q))
    EQ_MP (← SYM th1) (DEDUCT_ANTISYM_RULE th2 th3))
  let MP_qth ← liftExcept (do
    let th1 ← BETA_RULE (← AP_THM (← AP_THM IMP_DEF p) q)
    let th2 ← EQ_MP th1 (← ASSUME (← mk_imp p q))
    CONJUNCT2 (← EQ_MP (← SYM th2) (← ASSUME p)))
  let MP_rth := DEDUCT_ANTISYM_RULE MP_pth MP_qth
  let MP : thm → thm → Except String thm := fun ith th => do
    let (ant, con) ← dest_imp (concl ith)
    if aconv ant (concl th) then
      EQ_MP (← EQ_MP (DEDUCT_ANTISYM_RULE th (← INST [(ant, p), (con, q)] MP_rth)) th) ith
    else failwith "MP: theorems do not agree"

  -- DISCH (its `p`, `q`)
  let _ ← pt "p:bool"
  let _ ← pt "q:bool"
  let DISCH_pth ← liftExcept (SYM (← BETA_RULE (← AP_THM (← AP_THM IMP_DEF p) q)))
  let DISCH : term → thm → Except String thm := fun a th => do
    let th1 ← CONJ (← ASSUME a) th
    let th2 ← CONJUNCT1 (← ASSUME (concl th1))
    let th4 ← INST [(a, p), (concl th, q)] DISCH_pth
    EQ_MP th4 (DEDUCT_ANTISYM_RULE th1 th2)
  let DISCH_ALL := DISCH_ALL DISCH

  -- UNDISCH
  let UNDISCH : thm → Except String thm := fun th =>
    (do MP th (← ASSUME (← rand (← rator (concl th))))).mapError (fun _ => "UNDISCH")
  let UNDISCH_ALL := UNDISCH_ALL UNDISCH

  -- IMP_ANTISYM_RULE
  let _ ← pt "p:bool"
  let _ ← pt "q:bool"
  let imp_tm ← pt "(==>)"
  let IAR_pth ← liftExcept (do
    let pq ← mk_imp p q
    let qp ← mk_imp q p
    let (pth1, pth2) ← CONJ_PAIR (← ASSUME (← mk_conj pq qp))
    let pth3 := DEDUCT_ANTISYM_RULE (← UNDISCH pth2) (← UNDISCH pth1)
    let pth4 ← DISCH_ALL (← ASSUME q)
    let pth5 ← ASSUME (safe_mk_eq p q)
    let pth6 ← CONJ
      (← EQ_MP (← SYM (← AP_THM (← AP_TERM imp_tm pth5) q)) pth4)
      (← EQ_MP (← SYM (← AP_TERM (← mk_comb imp_tm q) pth5)) pth4)
    pure (DEDUCT_ANTISYM_RULE pth6 pth3))
  let IMP_ANTISYM_RULE : thm → thm → Except String thm := fun th1 th2 => do
    let (p1, q1) ← dest_imp (concl th1)
    EQ_MP (← INST [(p1, p), (q1, q)] IAR_pth) (← CONJ th1 th2)

  -- ADD_ASSUM
  let ADD_ASSUM : term → thm → Except String thm := fun tm th => do
    MP (← DISCH tm th) (← ASSUME tm)

  -- EQ_IMP_RULE
  let peq ← pt "p <=> q"
  let EQ_IMP_pth1 ← liftExcept (DISCH peq (← DISCH p (← EQ_MP (← ASSUME peq) (← ASSUME p))))
  let EQ_IMP_pth2 ← liftExcept (DISCH peq (← DISCH q (← EQ_MP (← SYM (← ASSUME peq)) (← ASSUME q))))
  let EQ_IMP_RULE : thm → Except String (thm × thm) := fun th => do
    let (l, r) ← dest_iff (concl th)
    return (← MP (← INST [(l, p), (r, q)] EQ_IMP_pth1) th,
            ← MP (← INST [(l, p), (r, q)] EQ_IMP_pth2) th)

  -- IMP_TRANS
  let pq ← pt "p ==> q"
  let qr ← pt "q ==> r"
  let rr ← liftExcept (rand qr)
  let IMP_TRANS_pth ← liftExcept (do
    itlistM DISCH [pq, qr, p]
      (← MP (← ASSUME qr) (← MP (← ASSUME pq) (← ASSUME p))))
  let IMP_TRANS : thm → thm → Except String thm := fun th1 th2 => do
    let (x, y)  ← dest_imp (concl th1)
    let (y', z) ← dest_imp (concl th2)
    if y != y' then failwith "IMP_TRANS"
    else MP (← MP (← INST [(x, p), (y, q), (z, rr)] IMP_TRANS_pth) th1) th2

/- ---------------------------------------------------------------------- -/
/- Rules for !                                                            -/
/- ---------------------------------------------------------------------- -/
  -- Rules for !
  -- FORALL_DEF = `(!) = \P:A->bool. P = \x. T`
  let FORALL_DEF ← new_basic_definition (← pt "(!) = \\P:A->bool. P = \\x. T")

  -- SPEC: `P`, `x`, then th1's arguments right to left, then th2's `x:A`.
  let PAb ← pt "P:A->bool"
  let xA ← pt "x:A"
  let allP ← pt "(!)(P:A->bool)"
  let PAb1 ← pt "P:A->bool"
  let xA1 ← pt "x:A"
  let SPEC_pth ← liftExcept (do
    let th1 ← EQ_MP (← AP_THM FORALL_DEF PAb1) (← ASSUME allP)
    let th2 ← AP_THM (← CONV_RULE BETA_CONV th1) xA1
    let th3 ← CONV_RULE (RAND_CONV BETA_CONV) th2
    DISCH_ALL (← EQT_ELIM th3))
  let SPEC : term → thm → Except String thm := fun tm th =>
    (do let abs ← rand (concl th)
        let (_, bvTy) ← dest_var (← bndvar abs)
        CONV_RULE BETA_CONV
          (← MP (← PINST [(bvTy, aty)] [(abs, PAb), (tm, xA)] SPEC_pth) th)
    ).mapError (fun _ => "SPEC")

  let SPECL : List term → thm → Except String thm := fun tms th =>
    (rev_itlistM SPEC tms th).mapError (fun _ => "SPECL")

  let SPEC_VAR : thm → Except String (term × thm) := fun th => do
    let bv ← variant (thm_frees th) (← bndvar (← rand (concl th)))
    return (bv, ← SPEC bv th)

  let SPEC_ALL := SPEC_ALL SPEC

  -- GEN
  let PAbG ← pt "P:A->bool"
  let GEN_pth ← liftExcept (SYM (← CONV_RULE (RAND_CONV BETA_CONV)
                                             (← AP_THM FORALL_DEF PAbG)))
  let GEN : term → thm → Except String thm := fun x th => do
    let (_, xty) ← dest_var x
    let qth ← INST_TYPE [(xty, aty)] GEN_pth
    let ptm ← rand (← rand (concl qth))
    let th' ← ABS x (← EQT_INTRO th)
    let phi ← lhand (concl th')
    EQ_MP (← INST [(phi, ptm)] qth) th'

  let GENL : List term → thm → Except String thm := fun vs th => itlistM GEN vs th

  let GEN_ALL : thm → Except String thm := fun th => do
    let (asl, c) := dest_thm th
    GENL (subtract (frees c) (freesl asl)) th

  -- ISPEC: type-instantiate then specialize.
  let ISPEC : term → thm → Except String thm := fun t th =>
    (do let (x, _) ← (dest_forall (concl th)).mapError
                        (fun _ => "ISPEC: input theorem not universally quantified")
        let tyins ← (type_match (← dest_var x |>.map Prod.snd) (type_of t) []).mapError
                        (fun _ => "ISPEC can't type-instantiate input theorem")
        (SPEC t (← INST_TYPE tyins th)).mapError
          (fun _ => "ISPEC: type variable(s) free in assumptions")
    ).mapError (fun e => e)

  let ISPECL : List term → thm → Except String thm := fun tms th =>
    (do if tms.isEmpty then pure th
        else
          let (avs, _) ← chop_list tms.length (strip_forall (concl th)).1
          let vtys ← avs.mapM (fun v => do return (← dest_var v).2)
          let tyins ← itlist2M type_match vtys (tms.map type_of) []
          SPECL tms (← INST_TYPE tyins th)
    ).mapError (fun _ => "ISPECL")

/- ---------------------------------------------------------------------- -/
/- Rules for ?                                                            -/
/- ---------------------------------------------------------------------- -/
  -- Rules for ?
  -- EXISTS_DEF = `(?) = \P:A->bool. !q. (!x. P x ==> q) ==> q`
  let EXISTS_DEF ← new_basic_definition
    (← pt "(?) = \\P:A->bool. !q. (!x. P x ==> q) ==> q")

  -- EXISTS: `P`, `x`, then the quotations of pth in OCaml's order.
  let PAb ← pt "P:A->bool"
  let xA ← pt "x:A"
  let EXISTS_pth ← do
    let th1 ← liftExcept (do CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM EXISTS_DEF PAb))
    let allxPxQ ← pt "!x:A. P x ==> Q"
    let x2 ← pt "x:A"
    let th2 ← liftExcept (do SPEC x2 (← ASSUME allxPxQ))
    let pxA ← pt "(P:A->bool) x"
    let allxPxQ' ← pt "!x:A. P x ==> Q"
    let th3 ← liftExcept (do DISCH allxPxQ' (← MP th2 (← ASSUME pxA)))
    let QB ← pt "Q:bool"
    liftExcept (do EQ_MP (← SYM th1) (← GEN QB th3))
  let EXISTS : term × term → thm → Except String thm := fun (etm, stm) th =>
    (do let (_, abs) ← dest_comb etm
        let bth ← BETA_CONV (← mk_comb abs stm)
        let cth ← PINST [(type_of stm, aty)] [(abs, PAb), (stm, xA)] EXISTS_pth
        PROVE_HYP (← EQ_MP (← SYM bth) th) cth
    ).mapError (fun _ => "EXISTS")

  let SIMPLE_EXISTS : term → thm → Except String thm := fun v th => do
    EXISTS (← mk_exists v (concl th), v) th

  -- CHOOSE: `P`, `Q`, then pth's `Q:bool` and `(?) (P:A->bool)`.
  let PAbC ← pt "P:A->bool"
  let QB ← pt "Q:bool"
  let CHOOSE_pth ← do
    let th1 ← liftExcept (do CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM EXISTS_DEF PAbC))
    let Q2 ← pt "Q:bool"
    let th2 ← liftExcept (do SPEC Q2 (← UNDISCH (← Prod.fst <$> EQ_IMP_RULE th1)))
    let exP ← pt "(?) (P:A->bool)"
    liftExcept (do DISCH_ALL (← DISCH exP (← UNDISCH th2)))
  let CHOOSE : term × thm → thm → Except String thm := fun (v, th1) th2 =>
    (do let abs ← rand (concl th1)
        let (bv, bod) ← dest_abs abs
        let cmb ← mk_comb abs v
        let pat := (← vsubst [(v, bv)]) bod
        let th3 ← CONV_RULE BETA_CONV (← ASSUME cmb)
        let th4 ← GEN v (← DISCH cmb (← MP (← DISCH pat th2) th3))
        let (_, vty) ← dest_var v
        let th5 ← PINST [(vty, aty)] [(abs, PAb), (concl th2, QB)] CHOOSE_pth
        MP (← MP th5 th4) th1
    ).mapError (fun _ => "CHOOSE")

  let SIMPLE_CHOOSE : term → thm → Except String thm := fun v th => do
    CHOOSE (v, ← ASSUME (← mk_exists v (← hd (hyp th)))) th

/- ---------------------------------------------------------------------- -/
/- Rules for \/                                                           -/
/- ---------------------------------------------------------------------- -/
  -- Rules for \/
  -- OR_DEF = `(\/) = \p q. !r. (p ==> r) ==> (q ==> r) ==> r`
  let OR_DEF ← new_basic_definition
    (← pt "(\\/) = \\p q. !r. (p ==> r) ==> (q ==> r) ==> r")

  -- DISJ1 (its `P`, `Q`, then pth's quotations in OCaml's order)
  let _ ← pt "P:bool"
  let _ ← pt "Q:bool"
  let DISJ1_pth ← do
    let P1 ← pt "P:bool"
    let th1 ← liftExcept (do CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM OR_DEF P1))
    let Q1 ← pt "Q:bool"
    let th2 ← liftExcept (do CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM th1 Q1))
    let a1 ← pt "P:bool"
    let a2 ← pt "P ==> t"
    let th3 ← liftExcept (do MP (← ASSUME a2) (← ASSUME a1))
    let d2 ← pt "Q ==> t"
    let d1 ← pt "P ==> t"
    let tB ← pt "t:bool"
    let th4 ← liftExcept (do GEN tB (← DISCH d1 (← DISCH d2 th3)))
    liftExcept (EQ_MP (← SYM th2) th4)
  let DISJ1 : thm → term → Except String thm := fun th tm =>
    (do EQ_MP (DEDUCT_ANTISYM_RULE th (← INST [(concl th, cP), (tm, cQ)] DISJ1_pth)) th
    ).mapError (fun _ => "DISJ1")

  -- DISJ2
  let _ ← pt "P:bool"
  let _ ← pt "Q:bool"
  let DISJ2_pth ← do
    let P1 ← pt "P:bool"
    let th1 ← liftExcept (do CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM OR_DEF P1))
    let Q1 ← pt "Q:bool"
    let th2 ← liftExcept (do CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM th1 Q1))
    let a1 ← pt "Q:bool"
    let a2 ← pt "Q ==> t"
    let th3 ← liftExcept (do MP (← ASSUME a2) (← ASSUME a1))
    let d2 ← pt "Q ==> t"
    let d1 ← pt "P ==> t"
    let tB ← pt "t:bool"
    let th4 ← liftExcept (do GEN tB (← DISCH d1 (← DISCH d2 th3)))
    liftExcept (EQ_MP (← SYM th2) th4)
  let DISJ2 : term → thm → Except String thm := fun tm th =>
    (do EQ_MP (DEDUCT_ANTISYM_RULE th (← INST [(tm, cP), (concl th, cQ)] DISJ2_pth)) th
    ).mapError (fun _ => "DISJ2")

  -- DISJ_CASES
  let _ ← pt "P:bool"
  let _ ← pt "Q:bool"
  let cR ← pt "R:bool"
  let DISJ_CASES_pth ← do
    let P1 ← pt "P:bool"
    let th1 ← liftExcept (do CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM OR_DEF P1))
    let Q1 ← pt "Q:bool"
    let th2 ← liftExcept (do CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM th1 Q1))
    let pq ← pt "P \\/ Q"
    let r ← pt "R:bool"
    let th3 ← liftExcept (do SPEC r (← EQ_MP th2 (← ASSUME pq)))
    liftExcept (do UNDISCH (← UNDISCH th3))
  let DISJ_CASES : thm → thm → thm → Except String thm := fun th0 th1 th2 =>
    (do let c1 := concl th1
        let c2 := concl th2
        if !(aconv c1 c2) then failwith "DISJ_CASES"
        else
          let (l, r) ← dest_disj (concl th0)
          let th ← INST [(l, cP), (r, cQ), (c1, cR)] DISJ_CASES_pth
          PROVE_HYP (← DISCH r th2)
            (← PROVE_HYP (← DISCH l th1)
              (← EQ_MP (DEDUCT_ANTISYM_RULE th0 th) th0))
    ).mapError (fun _ => "DISJ_CASES")

  let SIMPLE_DISJ_CASES : thm → thm → Except String thm := fun th1 th2 => do
    DISJ_CASES (← ASSUME (← mk_disj (← hd (hyp th1)) (← hd (hyp th2)))) th1 th2

/- ---------------------------------------------------------------------- -/
/- Rules for negation and falsity                                         -/
/- ---------------------------------------------------------------------- -/
  -- Rules for negation and falsity.
  -- F_DEF = `F = !p:bool. p`
  let F_DEF ← new_basic_definition (← pt "F = !p:bool. p")
  -- NOT_DEF = `(~) = \p. p ==> F`
  let NOT_DEF ← new_basic_definition (← pt "(~) = \\p. p ==> F")
  -- mk_neg's `neg_tm = `(~)`` (bool.ml 431); `mk_neg` builds the term directly.
  let _ ← pt "(~)"

  -- NOT_ELIM
  let _ ← pt "P:bool"
  let NOT_ELIM_pth ← liftExcept (CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM NOT_DEF cP))
  let NOT_ELIM : thm → Except String thm := fun th =>
    (do EQ_MP (← INST [(← rand (concl th), cP)] NOT_ELIM_pth) th
    ).mapError (fun _ => "NOT_ELIM")

  -- NOT_INTRO
  let _ ← pt "P:bool"
  let NOT_INTRO_pth ← liftExcept
    (SYM (← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM NOT_DEF cP)))
  let NOT_INTRO : thm → Except String thm := fun th =>
    (do EQ_MP (← INST [(← rand (← rator (concl th)), cP)] NOT_INTRO_pth) th
    ).mapError (fun _ => "NOT_INTRO")

  -- EQF_INTRO
  let _ ← pt "P:bool"
  let EQF_INTRO_pth ← do
    let nP ← pt "~ P"
    let th1 ← liftExcept (do NOT_ELIM (← ASSUME nP))
    let f1 ← pt "F"
    let f2 ← pt "F"
    let th2 ← liftExcept (do DISCH f2 (← SPEC cP (← EQ_MP F_DEF (← ASSUME f1))))
    liftExcept (do DISCH_ALL (← IMP_ANTISYM_RULE th1 th2))
  let EQF_INTRO : thm → Except String thm := fun th =>
    (do MP (← INST [(← rand (concl th), cP)] EQF_INTRO_pth) th
    ).mapError (fun _ => "EQF_INTRO")

  -- EQF_ELIM
  let _ ← pt "P:bool"
  let EQF_ELIM_pth ← do
    let a1 ← pt "P:bool"
    let a2 ← pt "P = F"
    let th1 ← liftExcept (do EQ_MP (← ASSUME a2) (← ASSUME a1))
    liftExcept (do DISCH_ALL (← NOT_INTRO (← DISCH cP th1)))
  let EQF_ELIM : thm → Except String thm := fun th =>
    (do MP (← INST [(← rand (← rator (concl th)), cP)] EQF_ELIM_pth) th
    ).mapError (fun _ => "EQF_ELIM")

  -- CONTR
  let _ ← pt "P:bool"
  let cF ← pt "F"
  let CONTR_pth ← do
    let f1 ← pt "F"
    liftExcept (do SPEC cP (← EQ_MP F_DEF (← ASSUME f1)))
  let CONTR : term → thm → Except String thm := fun tm th =>
    if concl th != cF then failwith "CONTR"
    else (do EQ_MP (DEDUCT_ANTISYM_RULE th (← INST [(tm, cP)] CONTR_pth)) th
         ).mapError (fun _ => "CONTR")

/- ---------------------------------------------------------------------- -/
/- Rules for unique existence                                             -/
/- ---------------------------------------------------------------------- -/
  -- Rules for unique existence.
  -- EXISTS_UNIQUE_DEF =
  --   `(?!) = \P:A->bool. ((?) P) /\ (!x y. P x /\ P y ==> x = y)`
  let EXISTS_UNIQUE_DEF ← new_basic_definition
    (← pt "(?!) = \\P:A->bool. ((?) P) /\\ (!x y. P x /\\ P y ==> x = y)")
  -- EXISTENCE's `P`.
  let _ ← pt "P:A->bool"

  -- EXISTENCE
  let EXISTENCE_pth ← liftExcept (do
    let th1 ← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM EXISTS_UNIQUE_DEF PAb)
    let th2 ← UNDISCH (← Prod.fst <$> EQ_IMP_RULE th1)
    DISCH_ALL (← CONJUNCT1 th2))
  let EXISTENCE : thm → Except String thm := fun th =>
    (do let abs ← rand (concl th)
        let (_, ty) ← dest_var (← bndvar abs)
        MP (← PINST [(ty, aty)] [(abs, PAb)] EXISTENCE_pth) th
    ).mapError (fun _ => "EXISTENCE")

  return { T_DEF, TRUTH, EQT_ELIM, EQT_INTRO, AND_DEF, CONJ, CONJUNCT1, CONJUNCT2,
           CONJ_PAIR, CONJUNCTS, IMP_DEF, MP, DISCH, DISCH_ALL, UNDISCH, UNDISCH_ALL,
           IMP_ANTISYM_RULE, ADD_ASSUM, EQ_IMP_RULE, IMP_TRANS,
           FORALL_DEF, SPEC, SPECL, SPEC_VAR, SPEC_ALL, GEN, GENL, GEN_ALL,
           ISPEC, ISPECL,
           EXISTS_DEF, EXISTS, SIMPLE_EXISTS, CHOOSE, SIMPLE_CHOOSE,
           OR_DEF, DISJ1, DISJ2, DISJ_CASES, SIMPLE_DISJ_CASES,
           F_DEF, NOT_DEF, NOT_ELIM, NOT_INTRO, EQF_INTRO, EQF_ELIM, CONTR,
           EXISTS_UNIQUE_DEF, EXISTENCE }

/- ---------------------------------------------------------------------- -/
/- Optionally select more verbose syntax for quantifiers, as well         -/
/- ---------------------------------------------------------------------- -/

/- Optionally select more verbose syntax for quantifiers, as well as the
logical constants T (true) and F (false). Enabled by default. Run after
`setupBool` establishes the constants. -/

/-- Select the more verbose quantifier and constant syntax. -/
def set_verbose_symbols : IO (Except String Unit) := do
  do_list parse_as_binder ["forall", "exists", "existsunique"]
  -- bool.ml 493-497, in order: each quotation is parsed just before its
  -- override_interface; any failure propagates, as OCaml's would.
  for (sym, q) in [("true", "T"), ("false", "F"), ("forall", "(!):(A->bool)->bool"),
                   ("exists", "(?):(A->bool)->bool"), ("existsunique", "(?!):(A->bool)->bool")] do
    match ← HolCore.Parser.parse_term q with
    | .error e => return .error e
    | .ok tm =>
      match ← override_interface sym tm with
      | .ok () => pure ()
      | .error e => return .error e
  return .ok ()

/-- Undo `set_verbose_symbols`, restoring the terse syntax. -/
def unset_verbose_symbols : IO Unit := do
  do_list unparse_as_binder ["forall", "exists", "existsunique"]
  do_list remove_interface ["true", "false", "forall", "exists", "existsunique"]

end HolCore.Bool
