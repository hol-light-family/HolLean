/- File: Bool.lean
Boolean theory including (intuitionistic) defs of logical connectives.
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026 -/

import HolCore.Equal
import HolCore.Basics
import HolCore.Fusion
import HolCore.Printer
import HolCore.Preterm

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

/- SPEC_ALL, parameterized by SPEC_VAR (recursive; specializes all leading ∀s). -/
/-- Specialize away all leading universal quantifiers, given `SPEC_VAR`. -/
partial def SPEC_ALL (SPEC_VAR : thm → Except String (term × thm)) (th : thm) :
    Except String thm :=
  if is_forall (concl th) then
    match SPEC_VAR th with
    | .ok (_, th') => SPEC_ALL SPEC_VAR th'
    | .error e => .error e
  else .ok th

/- Run all of bool.ml's definitions and derived rules once, in order,
returning the resulting theorems and rules. -/
/-- Run all of `bool.ml`'s definitions and derived rules once, in order. -/
def setupBool : ExceptT String IO BoolThms := do
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
  let _ ← override_interface "<=>"
            (.Const "=" (.Tyapp "fun" [bool_ty, .Tyapp "fun" [bool_ty, bool_ty]]))
  parse_as_infix ("=", (12, "right"))

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
  let idfn : term := .Abs (.Var "p" bool_ty) (.Var "p" bool_ty)
  let T_DEF ← new_basic_definition (safe_mk_eq (.Var "T" bool_ty) (safe_mk_eq idfn idfn))

  -- TRUTH = EQ_MP (SYM T_DEF) (REFL `\p:bool. p`)
  let TRUTH ← liftExcept (do EQ_MP (← SYM T_DEF) (REFL idfn))

  -- EQT_ELIM th = try EQ_MP (SYM th) TRUTH with _ -> failwith "EQT_ELIM"
  let EQT_ELIM : thm → Except String thm := fun th =>
    (do EQ_MP (← SYM th) TRUTH).mapError (fun _ => "EQT_ELIM")

  -- EQT_INTRO: proforma over `t:bool`, then fun th -> EQ_MP (INST[concl th,t] pth) th
  let t : term := .Var "t" bool_ty
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
  let bbb : hol_type := .Tyapp "fun" [bool_ty, .Tyapp "fun" [bool_ty, bool_ty]]
  let p : term := .Var "p" bool_ty
  let q : term := .Var "q" bool_ty
  let f : term := .Var "f" bbb
  let cT : term := .Const "T" bool_ty
  -- AND_DEF = `(/\) = \p q. (\f:bool->bool->bool. f p q) = (\f. f T T)`
  let fpq ← liftExcept (do mk_abs f (← mk_comb (← mk_comb f p) q))   -- \f. f p q
  let fTT ← liftExcept (do mk_abs f (← mk_comb (← mk_comb f cT) cT)) -- \f. f T T
  let andBody ← liftExcept (do mk_abs p (← mk_abs q (safe_mk_eq fpq fTT)))
  let AND_DEF ← new_basic_definition (safe_mk_eq (.Var "/\\" bbb) andBody)

  -- selector lambdas  \(p:bool)(q:bool). p   and   \(p:bool)(q:bool). q
  let selP : term := .Abs p (.Abs q p)
  let selQ : term := .Abs p (.Abs q q)

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

  -- CONJUNCT1 / CONJUNCT2  (proformas over P, Q)
  let cP : term := .Var "P" bool_ty
  let cQ : term := .Var "Q" bool_ty
  let conj1_pth ← liftExcept (do
    let th1 ← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM AND_DEF cP)
    let th2 ← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM th1 cQ)
    let th3 ← EQ_MP th2 (← ASSUME (← mk_conj cP cQ))
    EQT_ELIM (← BETA_RULE (← AP_THM th3 selP)))
  let conj2_pth ← liftExcept (do
    let th1 ← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM AND_DEF cP)
    let th2 ← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM th1 cQ)
    let th3 ← EQ_MP th2 (← ASSUME (← mk_conj cP cQ))
    EQT_ELIM (← BETA_RULE (← AP_THM th3 selQ)))
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
  let impBody ← liftExcept (do
    let conj ← mk_conj p q
    mk_abs p (← mk_abs q (safe_mk_eq conj p)))
  let IMP_DEF ← new_basic_definition (safe_mk_eq (.Var "==>" bbb) impBody)

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

  -- DISCH
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
  let imp_tm : term := .Const "==>" bbb
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
  let peq : term := safe_mk_eq p q
  let EQ_IMP_pth1 ← liftExcept (DISCH peq (← DISCH p (← EQ_MP (← ASSUME peq) (← ASSUME p))))
  let EQ_IMP_pth2 ← liftExcept (DISCH peq (← DISCH q (← EQ_MP (← SYM (← ASSUME peq)) (← ASSUME q))))
  let EQ_IMP_RULE : thm → Except String (thm × thm) := fun th => do
    let (l, r) ← dest_iff (concl th)
    return (← MP (← INST [(l, p), (r, q)] EQ_IMP_pth1) th,
            ← MP (← INST [(l, p), (r, q)] EQ_IMP_pth2) th)

  -- IMP_TRANS
  let rr : term := .Var "r" bool_ty
  let IMP_TRANS_pth ← liftExcept (do
    let pq ← mk_imp p q
    let qr ← mk_imp q rr
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
  let Abool : hol_type := .Tyapp "fun" [aty, bool_ty]        -- A → bool
  let allTy : hol_type := .Tyapp "fun" [Abool, bool_ty]      -- (A→bool) → bool
  let PAb : term := .Var "P" Abool
  let xA : term := .Var "x" aty
  -- FORALL_DEF = `(!) = \P:A->bool. P = \x. T`
  let allTrue ← liftExcept (mk_abs xA cT)                    -- \x. T
  let forallBody ← liftExcept (mk_abs PAb (safe_mk_eq PAb allTrue))
  let FORALL_DEF ← new_basic_definition (safe_mk_eq (.Var "!" allTy) forallBody)

  -- SPEC
  let SPEC_pth ← liftExcept (do
    let th1 ← EQ_MP (← AP_THM FORALL_DEF PAb)
                    (← ASSUME (← mk_comb (.Const "!" allTy) PAb))
    let th2 ← AP_THM (← CONV_RULE BETA_CONV th1) xA
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

  let SPEC_ALL := SPEC_ALL SPEC_VAR

  -- GEN
  let GEN_pth ← liftExcept (SYM (← CONV_RULE (RAND_CONV BETA_CONV)
                                             (← AP_THM FORALL_DEF PAb)))
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
  let qB : term := .Var "q" bool_ty
  let QB : term := .Var "Q" bool_ty
  let boolAllTy : hol_type := .Tyapp "fun" [.Tyapp "fun" [bool_ty, bool_ty], bool_ty]
  -- EXISTS_DEF = `(?) = \P:A->bool. !q. (!x. P x ==> q) ==> q`
  let existsBody ← liftExcept (do
    let px ← mk_comb PAb xA                                   -- P x
    let pxq ← mk_imp px qB                                    -- P x ==> q
    let allx ← mk_comb (.Const "!" allTy) (← mk_abs xA pxq)   -- !x. P x ==> q
    let inner ← mk_imp allx qB                                -- (!x. P x ==> q) ==> q
    let allq ← mk_comb (.Const "!" boolAllTy) (← mk_abs qB inner)  -- !q. ...
    mk_abs PAb allq)
  let EXISTS_DEF ← new_basic_definition (safe_mk_eq (.Var "?" allTy) existsBody)

  -- EXISTS
  let EXISTS_pth ← liftExcept (do
    let th1 ← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM EXISTS_DEF PAb)
    let allxPxQ ← mk_comb (.Const "!" allTy)
                    (← mk_abs xA (← mk_imp (← mk_comb PAb xA) QB))
    let th2 ← SPEC xA (← ASSUME allxPxQ)
    let th3 ← DISCH allxPxQ (← MP th2 (← ASSUME (← mk_comb PAb xA)))
    EQ_MP (← SYM th1) (← GEN QB th3))
  let EXISTS : term × term → thm → Except String thm := fun (etm, stm) th =>
    (do let (_, abs) ← dest_comb etm
        let bth ← BETA_CONV (← mk_comb abs stm)
        let cth ← PINST [(type_of stm, aty)] [(abs, PAb), (stm, xA)] EXISTS_pth
        PROVE_HYP (← EQ_MP (← SYM bth) th) cth
    ).mapError (fun _ => "EXISTS")

  let SIMPLE_EXISTS : term → thm → Except String thm := fun v th => do
    EXISTS (← mk_exists v (concl th), v) th

  -- CHOOSE
  let CHOOSE_pth ← liftExcept (do
    let th1 ← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM EXISTS_DEF PAb)
    let th2 ← SPEC QB (← UNDISCH (← Prod.fst <$> EQ_IMP_RULE th1))
    DISCH_ALL (← DISCH (← mk_comb (.Const "?" allTy) PAb) (← UNDISCH th2)))
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
  let rB : term := .Var "r" bool_ty
  let tB : term := .Var "t" bool_ty
  let cR : term := .Var "R" bool_ty
  -- OR_DEF = `(\/) = \p q. !r. (p ==> r) ==> (q ==> r) ==> r`
  let orBody ← liftExcept (do
    let pr ← mk_imp p rB
    let qr ← mk_imp q rB
    let inner ← mk_imp pr (← mk_imp qr rB)
    let allr ← mk_comb (.Const "!" boolAllTy) (← mk_abs rB inner)
    mk_abs p (← mk_abs q allr))
  let OR_DEF ← new_basic_definition (safe_mk_eq (.Var "\\/" bbb) orBody)

  -- DISJ1
  let DISJ1_pth ← liftExcept (do
    let th1 ← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM OR_DEF cP)
    let th2 ← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM th1 cQ)
    let th3 ← MP (← ASSUME (← mk_imp cP tB)) (← ASSUME cP)
    let th4 ← GEN tB (← DISCH (← mk_imp cP tB) (← DISCH (← mk_imp cQ tB) th3))
    EQ_MP (← SYM th2) th4)
  let DISJ1 : thm → term → Except String thm := fun th tm =>
    (do EQ_MP (DEDUCT_ANTISYM_RULE th (← INST [(concl th, cP), (tm, cQ)] DISJ1_pth)) th
    ).mapError (fun _ => "DISJ1")

  -- DISJ2
  let DISJ2_pth ← liftExcept (do
    let th1 ← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM OR_DEF cP)
    let th2 ← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM th1 cQ)
    let th3 ← MP (← ASSUME (← mk_imp cQ tB)) (← ASSUME cQ)
    let th4 ← GEN tB (← DISCH (← mk_imp cP tB) (← DISCH (← mk_imp cQ tB) th3))
    EQ_MP (← SYM th2) th4)
  let DISJ2 : term → thm → Except String thm := fun tm th =>
    (do EQ_MP (DEDUCT_ANTISYM_RULE th (← INST [(tm, cP), (concl th, cQ)] DISJ2_pth)) th
    ).mapError (fun _ => "DISJ2")

  -- DISJ_CASES
  let DISJ_CASES_pth ← liftExcept (do
    let th1 ← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM OR_DEF cP)
    let th2 ← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM th1 cQ)
    let th3 ← SPEC cR (← EQ_MP th2 (← ASSUME (← mk_disj cP cQ)))
    UNDISCH (← UNDISCH th3))
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
  let notTy : hol_type := .Tyapp "fun" [bool_ty, bool_ty]
  let cF : term := .Const "F" bool_ty
  -- F_DEF = `F = !p:bool. p`
  let fBody ← liftExcept (mk_comb (.Const "!" boolAllTy) idfn)
  let F_DEF ← new_basic_definition (safe_mk_eq (.Var "F" bool_ty) fBody)
  -- NOT_DEF = `(~) = \p. p ==> F`
  let notBody ← liftExcept (mk_abs p (← mk_imp p cF))
  let NOT_DEF ← new_basic_definition (safe_mk_eq (.Var "~" notTy) notBody)

  -- NOT_ELIM
  let NOT_ELIM_pth ← liftExcept (CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM NOT_DEF cP))
  let NOT_ELIM : thm → Except String thm := fun th =>
    (do EQ_MP (← INST [(← rand (concl th), cP)] NOT_ELIM_pth) th
    ).mapError (fun _ => "NOT_ELIM")

  -- NOT_INTRO
  let NOT_INTRO_pth ← liftExcept
    (SYM (← CONV_RULE (RAND_CONV BETA_CONV) (← AP_THM NOT_DEF cP)))
  let NOT_INTRO : thm → Except String thm := fun th =>
    (do EQ_MP (← INST [(← rand (← rator (concl th)), cP)] NOT_INTRO_pth) th
    ).mapError (fun _ => "NOT_INTRO")

  -- EQF_INTRO
  let EQF_INTRO_pth ← liftExcept (do
    let th1 ← NOT_ELIM (← ASSUME (← mk_neg cP))
    let th2 ← DISCH cF (← SPEC cP (← EQ_MP F_DEF (← ASSUME cF)))
    DISCH_ALL (← IMP_ANTISYM_RULE th1 th2))
  let EQF_INTRO : thm → Except String thm := fun th =>
    (do MP (← INST [(← rand (concl th), cP)] EQF_INTRO_pth) th
    ).mapError (fun _ => "EQF_INTRO")

  -- EQF_ELIM
  let EQF_ELIM_pth ← liftExcept (do
    let th1 ← EQ_MP (← ASSUME (safe_mk_eq cP cF)) (← ASSUME cP)
    let th2 ← DISCH cP (← SPEC cF (← EQ_MP F_DEF th1))
    DISCH_ALL (← NOT_INTRO th2))
  let EQF_ELIM : thm → Except String thm := fun th =>
    (do MP (← INST [(← rand (← rator (concl th)), cP)] EQF_ELIM_pth) th
    ).mapError (fun _ => "EQF_ELIM")

  -- CONTR
  let CONTR_pth ← liftExcept (SPEC cP (← EQ_MP F_DEF (← ASSUME cF)))
  let CONTR : term → thm → Except String thm := fun tm th =>
    if concl th != cF then failwith "CONTR"
    else (do EQ_MP (DEDUCT_ANTISYM_RULE th (← INST [(tm, cP)] CONTR_pth)) th
         ).mapError (fun _ => "CONTR")

/- ---------------------------------------------------------------------- -/
/- Rules for unique existence                                             -/
/- ---------------------------------------------------------------------- -/
  -- Rules for unique existence.
  let yA : term := .Var "y" aty
  -- EXISTS_UNIQUE_DEF =
  --   `(?!) = \P:A->bool. ((?) P) /\ (!x y. P x /\ P y ==> x = y)`
  let uexBody ← liftExcept (do
    let exP ← mk_comb (.Const "?" allTy) PAb
    let px ← mk_comb PAb xA
    let py ← mk_comb PAb yA
    let imp ← mk_imp (← mk_conj px py) (safe_mk_eq xA yA)
    let ally ← mk_comb (.Const "!" allTy) (← mk_abs yA imp)
    let allx ← mk_comb (.Const "!" allTy) (← mk_abs xA ally)
    mk_abs PAb (← mk_conj exP allx))
  let EXISTS_UNIQUE_DEF ← new_basic_definition (safe_mk_eq (.Var "?!" allTy) uexBody)

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
  let allTy : hol_type := .Tyapp "fun" [.Tyapp "fun" [aty, bool_ty], bool_ty]
  -- bool.ml 493-497, in order; any failure propagates, as OCaml's would.
  for (sym, tm) in [("true", (.Const "T" bool_ty : term)), ("false", .Const "F" bool_ty),
                    ("forall", .Const "!" allTy), ("exists", .Const "?" allTy),
                    ("existsunique", .Const "?!" allTy)] do
    match ← override_interface sym tm with
    | .ok () => pure ()
    | .error e => return .error e
  return .ok ()

/-- Undo `set_verbose_symbols`, restoring the terse syntax. -/
def unset_verbose_symbols : IO Unit := do
  do_list unparse_as_binder ["forall", "exists", "existsunique"]
  do_list remove_interface ["true", "false", "forall", "exists", "existsunique"]

end HolCore.Bool
