/- File: IndDefs.lean
Mutually inductively defined relations (the `ind_defs.ml` package).
Original       John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026
-/

import HolCore.Bool
import HolCore.Equal
import HolCore.Drule
import HolCore.Tactics
import HolCore.Itab
import HolCore.Simp
import HolCore.Parser
import HolCore.Theorems

open HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Bool HolCore.Equal
     HolCore.Drule HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Parser HolCore.Theorems

namespace HolCore.IndDefs

/- ---------------------------------------------------------------------- -/
/- Strip off exactly n arguments from combination.                        -/
/- ---------------------------------------------------------------------- -/

/-- `strip_ncomb n tm = (hd, [a1;…;an])` where `tm = hd a1 … an`. -/
private partial def strip_ncomb_go (n : Int) (tm : term) (acc : List term) :
    Except String (term × List term) :=
  if n < 1 then .ok (tm, acc)
  else do
    let (l, r) ← dest_comb tm
    strip_ncomb_go (n - 1) l (r :: acc)

def strip_ncomb (n : Int) (tm : term) : Except String (term × List term) :=
  strip_ncomb_go n tm []

/- ---------------------------------------------------------------------- -/
/-      A, x = t |- P[x]                                                  -/
/-     ------------------ EXISTS_EQUATION                                 -/
/-        A |- ?x. P[x]                                                   -/
/- ---------------------------------------------------------------------- -/

/-- Parse a term in the `ExceptT String IO` monad (mirrors Theorems' `pt`). -/
private def pt (s : String) : ExceptT String IO term := parse_term s

/-- The auxiliary theorem `pth` for `EXISTS_EQUATION`:
    `|- !P t. (!x. x = t ==> P x) ==> (?) P`. Proved once. -/
def EXISTS_EQUATION_pth (B : BoolThms) : ExceptT String IO thm := do
  let prove := Tactics.prove B
  let REWRITE_TAC := Simp.REWRITE_TAC B
  let BETA_TAC := Tactics.BETA_TAC B
  let STRIP_TAC := Tactics.STRIP_TAC B
  let MATCH_MP_TAC := Tactics.MATCH_MP_TAC B
  let EXISTS_TAC := Tactics.EXISTS_TAC B
  let REFL_TAC := Tactics.REFL_TAC B
  let goal ← pt "!P t. (!x:A. (x = t) ==> P x) ==> (?) P"
  (prove goal
    (THEN B (REWRITE_TAC [B.EXISTS_DEF])
      (THEN B BETA_TAC
        (THEN B (REPEAT B STRIP_TAC)
          (THEN B (FIRST_ASSUM MATCH_MP_TAC)
            (THEN B (EXISTS_TAC (← pt "t:A"))
              (THEN B (FIRST_ASSUM MATCH_MP_TAC) REFL_TAC)))))) : IO (Except String thm))

/-- `EXISTS_EQUATION pth tm th`: from `th = A, x = t |- P[x]` derive
    `A |- ?x. P[x]`.  (`pth` is `EXISTS_EQUATION_pth`.) -/
def EXISTS_EQUATION (B : BoolThms) (pth : thm) (tm : term) (th : thm) :
    Except String thm := do
  let (l, r) ← dest_eq tm
  let P ← mk_abs l (concl th)
  let th1 ← BETA_CONV (← mk_comb P l)
  let th2 ← B.ISPECL [P, r] pth
  let th3 ← EQ_MP (← SYM th1) th
  let th4 ← B.GEN l (← B.DISCH tm th3)
  B.MP th2 th4

/- ---------------------------------------------------------------------- -/
/- Expand lambda-term function definition with its arguments.             -/
/- ---------------------------------------------------------------------- -/

/-- `RIGHT_BETAS [a1;…;an] th`: apply `th` (an equation whose RHS is a lambda)
    to `a1 … an`, beta-reducing after each application.
    OCaml: `rev_itlist (fun a -> CONV_RULE (RAND_CONV BETA_CONV) o C AP_THM a)`. -/
def RIGHT_BETAS (args : List term) (th : thm) : Except String thm :=
  -- `C AP_THM a` is `fun t => AP_THM t a`; both stages are `Except`-valued, so
  -- `oM`, and `C AP_THM a` runs FIRST (ind_defs.ml 28).
  rev_itlistM (fun a => CONV_RULE (RAND_CONV BETA_CONV) oM Lib.C AP_THM a) args th

/- ======================================================================= -/
/- Part 1: The main part of the inductive definitions package.              -/
/- This proves that a certain definition yields the requires theorems.      -/
/- ======================================================================= -/

/-- `getconcl tm`: strip leading `!`s, then take the conclusion of the implication
    (or the whole body if not an implication). -/
def getconcl (tm : term) : term :=
  let bod := repeat' (fun t => (Basics.dest_forall t).map Prod.snd) tm
  match Basics.dest_imp bod with
  | .ok (_, c) => c
  | .error _ => bod

/-- `SIMPLE_DISJ_PAIR th`: `th` has a disjunctive first hypothesis `l \/ r`;
    return the two theorems got by assuming `l` resp. `r`. -/
def SIMPLE_DISJ_PAIR (B : BoolThms) (th : thm) : Except String (thm × thm) := do
  let (l, r) ← Basics.dest_disj (← headHyp th)
  let left ← PROVE_HYP (← B.DISJ1 (← ASSUME l) r) th
  let right ← PROVE_HYP (← B.DISJ2 l (← ASSUME r)) th
  return (left, right)
where
  headHyp (th : thm) : Except String term :=
    match hyp th with | h :: _ => .ok h | [] => .error "SIMPLE_DISJ_PAIR: no hyp"

/-- `HALF_BETA_EXPAND args th = GENL args (RIGHT_BETAS args th)`. -/
def HALF_BETA_EXPAND (B : BoolThms) (args : List term) (th : thm) : Except String thm := do
  B.GENL args (← RIGHT_BETAS args th)

/-- `AND_IMPS_CONV tm`: normalise a conjunction of implications into a single
    disjunction-antecedent implication (and back), returning the equivalence. -/
def AND_IMPS_CONV (B : BoolThms) (tm : term) : Except String thm := do
  let ths := B.CONJUNCTS (← ASSUME tm)
  let hd1 ← (match ths with | h :: _ => .ok h | [] => .error "AND_IMPS_CONV")
  let (avs, _) := strip_forall (concl hd1)
  -- thl = map (DISCH tm o UNDISCH o SPEC_ALL) ths   (ind_defs.ml 69).
  -- All three stages are `Except`-valued, so `oM` throughout; SPEC_ALL runs
  -- FIRST, then UNDISCH, then DISCH tm.
  let thl ← ths.mapM (B.DISCH tm oM B.UNDISCH oM B.SPEC_ALL)
  let th1 ← end_itlistM B.SIMPLE_DISJ_CASES thl
  let tm1 ← (match hyp th1 with | h :: _ => .ok h | [] => .error "AND_IMPS_CONV")
  let th2 ← B.GENL avs (← B.DISCH tm1 (← B.UNDISCH th1))
  let tm2 := concl th2
  let th3 ← B.DISCH tm2 (← B.UNDISCH (← B.SPEC_ALL (← ASSUME tm2)))
  let (thts, tht) ← nsplit (SIMPLE_DISJ_PAIR B) (ths.drop 1) th3
  let proc_fn (th : thm) : Except String thm := do
    let t ← (match hyp th with | h :: _ => .ok h | [] => .error "AND_IMPS_CONV")
    B.GENL avs (← B.DISCH t (← B.UNDISCH th))
  -- th4 = itlist (CONJ o proc_fn) thts (proc_fn tht)
  let base ← proc_fn tht
  let th4 ← itlistM (fun th acc => do B.CONJ (← proc_fn th) acc) thts base
  B.IMP_ANTISYM_RULE (← DISCH_ALL B.DISCH th2) (← DISCH_ALL B.DISCH th4)

/-- `calculate_simp_sequence avs plis`: split the pairs `plis = [(arg,xarg)]`
    into those whose second component is a distinct variable in `avs` (`oks`)
    and the rest. -/
private partial def getequs (avs : List term) (plis : List (term × term)) :
    List (term × term) :=
  match plis with
  | [] => []
  | h :: t =>
    let r := h.2
    if mem r avs then h :: getequs avs (t.filter (fun p => p.2 != r))
    else getequs avs t

def calculate_simp_sequence (avs : List term) (plis : List (term × term)) :
    (List (term × term)) × (List (term × term)) :=
  let oks := getequs avs plis
  (oks, subtract plis oks)

/-- `FORALL_IMPS_CONV tm`: push universal quantifiers through the antecedent of
    an implication, returning the equivalence. -/
def FORALL_IMPS_CONV (B : BoolThms) (tm : term) : Except String thm := do
  let (avs, bod) := strip_forall tm
  let th1 ← B.DISCH tm (← B.UNDISCH (← B.SPEC_ALL (← ASSUME tm)))
  let th2 ← itlistM B.SIMPLE_CHOOSE avs th1
  let tm2 ← (match hyp th2 with | h :: _ => .ok h | [] => .error "FORALL_IMPS_CONV")
  let th3 ← B.DISCH tm2 (← B.UNDISCH th2)
  let th4 ← ASSUME (concl th3)
  let ant ← lhand bod
  let th5 ← itlistM B.SIMPLE_EXISTS avs (← ASSUME ant)
  let th6 ← B.GENL avs (← B.DISCH ant (← B.MP th4 th5))
  B.IMP_ANTISYM_RULE (← DISCH_ALL B.DISCH th3) (← DISCH_ALL B.DISCH th6)

/-- `canonicalize_clause cls args`: rewrite a single inductive clause into a
    canonical form (arguments matched positionally against fresh variables),
    returning the equivalence theorem. -/
def canonicalize_clause (B : BoolThms) (t_tm : term) (cls : term) (args : List term) :
    ExceptT String IO thm := do
  let mkEq ← (mk_eq : IO (Except String ((term × term) → Except String term)))
  let (avs, bimp) := strip_forall cls
  let (ant, con) := match Basics.dest_imp bimp with
    | .ok (a, c) => (a, c)
    | .error _ => (t_tm, bimp)
  let (rel, xargs) := strip_comb con
  let plis ← liftExcept (zip args xargs)
  let (yes, no) := calculate_simp_sequence avs plis
  let nvs := avs.filter (fun a => !(mem a (yes.map Prod.snd)))
  -- helper: rev_itlist (C (curry MK_COMB)) thl (REFL rel)
  let mkCombChain (thl : List thm) : Except String thm :=
    rev_itlistM (fun th acc => MK_COMB acc th) thl (REFL rel)
  -- helper: find (fun th -> lhs(concl th) = t) ths
  let findByLhs (ths : List thm) (t : term) : Except String thm :=
    find (fun th => (lhs (concl th)).toOption == some t) ths
  let eth ←
    if Basics.is_imp bimp then liftExcept (do
      -- atm = itlist (curry mk_conj o mk_eq) (yes@no) ant
      let atm ← itlistM (fun p acc => do mk_conj (← mkEq p) acc) (yes ++ no) ant
      let (ths, tth) ← nsplit B.CONJ_PAIR plis (← ASSUME atm)
      let thl ← args.mapM (findByLhs ths)
      let th0 ← B.MP (← B.SPECL avs (← ASSUME cls)) tth
      let th1 ← mkCombChain thl
      let th2 ← EQ_MP (← SYM th1) th0
      let th3 ← INST yes (← B.DISCH atm th2)
      let tm4 ← funpowM (yes.length) rand (← lhand (concl th3))
      let th4 ← itlistM (fun p acc => do B.CONJ (REFL p.1) acc) yes (← ASSUME tm4)
      let th5 ← B.GENL args (← B.GENL nvs (← B.DISCH tm4 (← B.MP th3 th4)))
      let th6 ← B.SPECL nvs (← B.SPECL (plis.map Prod.snd) (← ASSUME (concl th5)))
      let th7 ← itlistM (fun p acc => do B.CONJ (REFL p.2) acc) no (← ASSUME ant)
      let th8 ← B.GENL avs (← B.DISCH ant (← B.MP th6 th7))
      B.IMP_ANTISYM_RULE (← DISCH_ALL B.DISCH th5) (← DISCH_ALL B.DISCH th8))
    else liftExcept (do
      let atm ← list_mk_conj (← (yes ++ no).mapM mkEq)
      let ths := B.CONJUNCTS (← ASSUME atm)
      let thl ← args.mapM (findByLhs ths)
      let th0 ← B.SPECL avs (← ASSUME cls)
      let th1 ← mkCombChain thl
      let th2 ← EQ_MP (← SYM th1) th0
      let th3 ← INST yes (← B.DISCH atm th2)
      let tm4 ← funpowM (yes.length) rand (← lhand (concl th3))
      let th4 ← itlistM (fun p acc => do B.CONJ (REFL p.1) acc) yes (← ASSUME tm4)
      let th5 ← B.GENL args (← B.GENL nvs (← B.DISCH tm4 (← B.MP th3 th4)))
      let th6 ← B.SPECL nvs (← B.SPECL (plis.map Prod.snd) (← ASSUME (concl th5)))
      let th7 ← end_itlistM B.CONJ (← no.mapM (fun p => pure (REFL p.2)))
      let th8 ← B.GENL avs (← B.MP th6 th7)
      B.IMP_ANTISYM_RULE (← DISCH_ALL B.DISCH th5) (← DISCH_ALL B.DISCH th8))
  -- ftm = funpow (length args) (body o rand) (rand(concl eth))   (ind_defs.ml 142).
  -- Both stages are `Except`-valued, so `oM`; `rand` runs FIRST.
  let ftm ← liftExcept (funpowM args.length (body oM rand) (← rand (concl eth)))
  let forallImps ← liftExcept (FORALL_IMPS_CONV B ftm)
  -- itlist MK_FORALL args forallImps   (MK_FORALL is IO)
  let rec mkForalls : List term → thm → IO (Except String thm)
    | [], t => return .ok t
    | v :: vs, t => do
        match ← (mkForalls vs t : IO (Except String thm)) with
        | .error e => return .error e
        | .ok t' => (MK_FORALL v t' : IO (Except String thm))
  let rhs ← (mkForalls args forallImps : IO (Except String thm))
  liftExcept (TRANS eth rhs)

/-- `canonicalize_clauses clauses`: canonicalise all clauses together, grouping
    by relation, returning the equivalence of the raw and canonical forms. -/
def canonicalize_clauses (B : BoolThms) (REFL_CLAUSE : thm) (CONJ_ACI : thm) (t_tm : term)
    (clauses : List term) : ExceptT String IO thm := do
  let CONJ_ACI_RULE (tm : term) : ExceptT String IO thm :=
    (Theorems.AC B REFL_CLAUSE CONJ_ACI tm : IO (Except String thm))
  let concls := clauses.map getconcl
  let uncs := concls.map strip_comb
  let rels := itlist (fun u acc => insert u.1 acc) uncs []
  let xargs ← liftExcept (rels.mapM (fun r => assoc r uncs))
  let closed ← liftExcept (list_mk_conj clauses)
  let avoids ← liftExcept (variables closed)
  let allx ← liftExcept (end_itlist (· ++ ·) xargs)
  let flargs ← liftExcept (make_args "a" avoids (allx.map type_of))
  let shared ← liftExcept (shareout xargs flargs)
  let zargs ← liftExcept (zip rels shared)
  let cargs ← liftExcept (uncs.mapM (fun u => assoc u.1 zargs))
  -- map2 canonicalize_clause clauses cargs  (IO)
  let cthms ← (← liftExcept (zip clauses cargs)).mapM
                (fun (cl, a) => (canonicalize_clause B t_tm cl a : IO (Except String thm)))
  let pclauses ← liftExcept (cthms.mapM (fun th => rand (concl th)))
  let unrels := uncs.map Prod.fst
  let relpcs ← liftExcept (zip unrels pclauses)
  let collectclauses (tm : term) : List term :=
    mapfilter (fun t => if t.1 == tm then .ok t.2 else fail) relpcs
  let clausell := rels.map collectclauses
  let cclausel ← liftExcept (clausell.mapM list_mk_conj)
  let cclauses ← liftExcept (list_mk_conj cclausel)
  let oclauses ← liftExcept (list_mk_conj pclauses)
  let mkEq ← (mk_eq : IO (Except String ((term × term) → Except String term)))
  let eth ← CONJ_ACI_RULE (← liftExcept (mkEq (oclauses, cclauses)))
  let pth ← liftExcept (do TRANS (← end_itlistM MK_CONJ cthms) eth)
  let andImps ← liftExcept (cclausel.mapM (AND_IMPS_CONV B))
  let rhsConv ← liftExcept (end_itlistM MK_CONJ andImps)
  liftExcept (TRANS pth rhsConv)

/-- `itlist MK_FORALL vs th`: universally quantify `th`'s equation over `vs`
    (outermost-first), using the IO-valued `MK_FORALL`. -/
partial def mkForallsList : List term → thm → IO (Except String thm)
  | [], t => return .ok t
  | v :: vs, t => do
      match ← (mkForallsList vs t : IO (Except String thm)) with
      | .error e => return .error e
      | .ok t' => (MK_FORALL v t' : IO (Except String thm))

/-- `derive_canon_inductive_relations clauses`: from canonical clauses derive
    the rule / induction / cases triple (conjoined). -/
def derive_canon_inductive_relations (B : BoolThms) (clausesIn : List term) :
    ExceptT String IO thm := do
  let closed ← liftExcept (list_mk_conj clausesIn)
  let clauses := conjuncts closed
  let (vargs, bodies) := unzip (clauses.map strip_forall)
  let antconc ← liftExcept (bodies.mapM Basics.dest_imp)
  let (ants, concs) := unzip antconc
  let rels := concs.map (repeat' rator)
  let avoids ← liftExcept (variables closed)
  let rels' ← liftExcept (variants avoids rels)
  let crels ← liftExcept (zip rels' rels)
  let primeFn ← (subst crels : IO (Except String (term → IO (Except String term))))
  let prime (t : term) : ExceptT String IO term := (primeFn t : IO (Except String term))
  let closed' ← prime closed
  let mkEq ← (mk_eq : IO (Except String ((term × term) → Except String term)))
  -- mk_def arg con
  let mk_def (arg : List term) (con : term) : ExceptT String IO term := do
    let pcon ← prime con
    let inner ← liftExcept (mk_imp closed' pcon)
    let body ← liftExcept (do list_mk_abs arg (← list_mk_forall rels' inner))
    liftExcept (mkEq (repeat' rator con, body))
  let deftms ← (← liftExcept (zip vargs concs)).mapM (fun (a, c) => mk_def a c)
  let defthms ← liftExcept (do
    let pairs ← zip vargs deftms
    pairs.mapM (fun (a, d) => do HALF_BETA_EXPAND B a (← ASSUME d)))
  -- mk_ind args th
  let mk_ind (args : List term) (th : thm) : Except String thm := do
    let th1 ← Prod.fst <$> (B.EQ_IMP_RULE (← B.SPEC_ALL th))
    let ant ← lhand (concl th1)
    let th2 ← B.SPECL rels' (← B.UNDISCH th1)
    B.GENL args (← B.DISCH ant (← B.UNDISCH th2))
  let indthms ← liftExcept (do
    let pairs ← zip vargs defthms
    pairs.mapM (fun (a, t) => mk_ind a t))
  let indthmr ← liftExcept (end_itlistM B.CONJ indthms)
  let indthm ← liftExcept (B.GENL rels' (← B.DISCH closed' indthmr))
  -- mconcs
  let mconcs ← (← liftExcept (zip vargs ants)).mapM (fun (a, t) => do
    let pt ← prime t
    let im ← liftExcept (mk_imp t pt)
    liftExcept (list_mk_forall a im))
  let mconcConj ← liftExcept (list_mk_conj mconcs)
  let monotm ← liftExcept (mk_imp (concl indthmr) mconcConj)
  let monoAll ← liftExcept (do list_mk_forall rels (← list_mk_forall rels' monotm))
  let monothm ← liftExcept (ASSUME monoAll)
  let closthm ← liftExcept (ASSUME closed')
  let monothms ← liftExcept (do
    let a ← B.MP (← B.SPECL rels' indthm) closthm
    pure (B.CONJUNCTS (← B.MP (← B.SPEC_ALL monothm) a)))
  let closthms := B.CONJUNCTS closthm
  -- prove_rule mth (cth,dth)
  let prove_rule (mth : thm) (cthdth : thm × thm) : Except String thm := do
    let (cth, dth) := cthdth
    let (avs, bod) := strip_forall (concl mth)
    let th1 ← B.IMP_TRANS (← B.SPECL avs mth) (← B.SPECL avs cth)
    let th2 ← B.GENL rels' (← B.DISCH closed' (← B.UNDISCH th1))
    let th3 ← EQ_MP (← SYM (← B.SPECL avs dth)) th2
    let ant ← lhand bod
    B.GENL avs (← B.DISCH ant th3)
  let rulethms ← liftExcept (do
    let cd ← zip closthms defthms
    let pairs ← zip monothms cd
    pairs.mapM (fun (m, cd) => prove_rule m cd))
  let rulethm ← liftExcept (end_itlistM B.CONJ rulethms)
  let dtms ← liftExcept (do
    let pairs ← zip vargs ants
    pairs.mapM (fun (a, t) => list_mk_abs a t))
  let dtmrels ← liftExcept (zip dtms rels)
  let doubleFn ← (subst dtmrels : IO (Except String (term → IO (Except String term))))
  let dbl (t : term) : ExceptT String IO term := (doubleFn t : IO (Except String term))
  -- mk_unbetas tm dtm
  let mk_unbetas (tm : term) (dtm : term) : ExceptT String IO (thm × (thm × thm)) := do
    let (avs, bod) := strip_forall tm
    let (il, r) ← liftExcept (dest_comb bod)
    let (i, l) ← liftExcept (dest_comb il)
    let bth ← liftExcept (RIGHT_BETAS avs (REFL dtm))
    let munb ← liftExcept (AP_THM (← AP_TERM i bth) r)
    let dl ← dbl l
    let iunb ← liftExcept (AP_TERM (← mk_comb i dl) bth)
    let junb ← liftExcept (AP_TERM (← mk_comb i r) bth)
    let quantify (t : thm) : IO (Except String thm) := mkForallsList avs t
    let m ← (quantify munb : IO (Except String thm))
    let iu ← (quantify iunb : IO (Except String thm))
    let ju ← (quantify junb : IO (Except String thm))
    pure (m, (iu, ju))
  let unths ← (← liftExcept (zip clauses dtms)).mapM (fun (c, d) => mk_unbetas c d)
  let irthm ← liftExcept (do EQ_MP (← SYM (← end_itlistM MK_CONJ (unths.map Prod.fst))) rulethm)
  let mrthm ← liftExcept (do B.MP (← B.SPECL rels (← B.SPECL dtms monothm)) irthm)
  let imrth ← liftExcept (do EQ_MP (← SYM (← end_itlistM MK_CONJ (unths.map (fun u => u.2.1)))) mrthm)
  let ifthm ← liftExcept (do B.MP (← B.SPECL dtms indthm) imrth)
  let fthm ← liftExcept (do EQ_MP (← end_itlistM MK_CONJ (unths.map (fun u => u.2.2))) ifthm)
  -- mk_case th1 th2
  let mk_case (th1 th2 : thm) : Except String thm := do
    let (avs, _) := strip_forall (concl th1)
    B.GENL avs (← B.IMP_ANTISYM_RULE (← B.SPEC_ALL th1) (← B.SPEC_ALL th2))
  let casethm ← liftExcept (do
    let pairs ← zip (B.CONJUNCTS fthm) (B.CONJUNCTS rulethm)
    end_itlistM B.CONJ (← pairs.mapM (fun (a, b) => mk_case a b)))
  liftExcept (do B.CONJ rulethm (← B.CONJ indthm casethm))

/-- `derive_nonschematic_inductive_relations tm`: the main entry — from a raw
    conjunction of clauses `tm`, derive the (rule ∧ induction ∧ cases) theorem.
    `REFL_CLAUSE`/`CONJ_ACI` are `TheoremThms` fields; `t_tm` is the term `T`. -/
def derive_nonschematic_inductive_relations (B : BoolThms) (REFL_CLAUSE CONJ_ACI : thm)
    (t_tm : term) (tm : term) : ExceptT String IO thm := do
  let clauses := conjuncts tm
  let canonthm ← (canonicalize_clauses B REFL_CLAUSE CONJ_ACI t_tm clauses
                    : IO (Except String thm))
  let canonthm' ← liftExcept (SYM canonthm)
  let pclosed ← liftExcept (rand (concl canonthm))
  let pclauses := conjuncts pclosed
  let rawthm ← (derive_canon_inductive_relations B pclauses : IO (Except String thm))
  let (rulethm, otherthms) ← liftExcept (B.CONJ_PAIR rawthm)
  let (indthm, casethm) ← liftExcept (B.CONJ_PAIR otherthms)
  let rulethm' ← liftExcept (EQ_MP canonthm' rulethm)
  let indthm' ← (Simp.convRuleIO (Simp.onceDepthConvIO (Simp.REWR_CONV B canonthm')) indthm
                  : IO (Except String thm))
  liftExcept (do B.CONJ rulethm' (← B.CONJ indthm' casethm))

/- ======================================================================= -/
/- Part 2: Tactic-integrated tools for proving monotonicity automatically.  -/
/- ======================================================================= -/

/- ---------------------------------------------------------------------- -/
/- Attempt to backchain through the monotonicity theorems.                -/
/- ---------------------------------------------------------------------- -/

/-- Backchain through a monotonicity theorem `th` (of the form
    `… ==> (R ⊑ R')`): match the conclusion against the goal, leaving the
    antecedent as the new subgoal. -/
def BACKCHAIN_TAC (B : BoolThms) (th : thm) : tactic := fun (asl, w) => do
  match ← (PART_MATCH B (fun t => do (Basics.dest_imp t).map Prod.snd) th w
            : IO (Except String thm)) with
  | .error e => return .error e
  | .ok th1 =>
    match Basics.dest_imp (concl th1) with
    | .error e => return .error e
    | .ok (ant, _) =>
      return .ok (null_meta, [(asl, ant)], fun i ths => do
        match ths with
        | [t] =>
          match INSTANTIATE i th1 with
          | .error e => return .error e
          | .ok ith => (MATCH_MP B ith t : IO (Except String thm))
        | _ => return .error "BACKCHAIN_TAC")

/-- Monotonicity for a lambda-abstraction application: beta-reduce both sides
    and rewrite the implication accordingly. -/
def MONO_ABS_TAC (B : BoolThms) (imp : term) : tactic := fun (asl, w) => do
  match Basics.dest_imp w with
  | .error e => return .error e
  | .ok (ant, con) =>
    let vars := (strip_comb con).2
    let rnum : Int := (vars.length : Int) - 1
    match (do
      let (hd1, args1) ← strip_ncomb rnum ant
      let (hd2, _args2) ← strip_ncomb rnum con
      let th1 ← rev_itlistM (fun a t => AP_THM t a) args1 (← BETA_CONV hd1)
      let th2 ← rev_itlistM (fun a t => AP_THM t a) args1 (← BETA_CONV hd2)
      let th3 ← MK_COMB (← AP_TERM imp th1) th2
      pure th3 : Except String thm) with
    | .error e => return .error e
    | .ok th3 => (Tactics.CONV_TAC B (Simp.REWR_CONV B th3) (asl, w) : IO (Except String goalstate))

/-- Try the monotonicity tactic keyed by the head constant of the goal's
    conclusion; reflexivity (`IMP_REFL`) if antecedent ≡ consequent. -/
def APPLY_MONOTAC (B : BoolThms) (IMP_REFL : thm) (tacs : List (String × tactic)) :
    tactic := fun (asl, w) => do
  match Basics.dest_imp w with
  | .error e => return .error e
  | .ok (a, c) =>
    if aconv a c then
      match B.SPEC a IMP_REFL with
      | .error e => return .error e
      | .ok sth => (Tactics.ACCEPT_TAC B sth (asl, w) : IO (Except String goalstate))
    else
      let cn := match dest_const (repeat' rator c) with
                | .ok (nm, _) => nm | .error _ => ""
      -- tryfind (fun (k,t) -> if k = cn then t (asl,w) else fail()) tacs
      -- (ind_defs.ml 277).  `tryfind` RETRIES: a same-key tactic that FAILS
      -- moves on to the next entry, so several theorems sharing a head
      -- constant are all tried, and the key-"" entries (a theorem whose head is
      -- not a constant, and the trailing `MONO_ABS_TAC`) back each other up.
      -- Exhaustion raises `tryfind`'s own message.
      let rec tryTacs : List (String × tactic) → IO (Except String goalstate)
        | [] => return .error "tryfind"
        | (k, t) :: rest =>
          if k == cn then do
            match ← t (asl, w) with
            | .ok r => return .ok r
            | .error _ => tryTacs rest
          else tryTacs rest
      tryTacs tacs

/-- Attempt to prove a monotonicity goal by repeated backchaining through the
    monotonicity theorems `mthms`. -/
def MONO_TAC (B : BoolThms) (mthms : List thm) (IMP_REFL : thm) : tactic := fun gl => do
  match ← (mk_const "==>" [] : IO (Except String term)) with
  | .error e => return .error e
  | .ok imp =>
    -- Build the keyed tactic table from the monotonicity theorems.
    let mkEntry (th : thm) : Except String (String × tactic) := do
      let ft := repeat' rator (← funpowM 2 rand (concl th))
      let c := match dest_const ft with | .ok (nm, _) => nm | .error _ => ""
      .ok (c, THEN B (BACKCHAIN_TAC B th) (REPEAT B (CONJ_TAC B)))
    match (mthms.mapM mkEntry : Except String (List (String × tactic))) with
    | .error e => return .error e
    | .ok entries =>
      let tacs := entries ++ [("", MONO_ABS_TAC B imp)]
      let MONO_STEP_TAC := THEN B (REPEAT B (GEN_TAC B)) (APPLY_MONOTAC B IMP_REFL tacs)
      (THEN B (REPEAT B MONO_STEP_TAC) (Simp.ASM_REWRITE_TAC B []) gl
        : IO (Except String goalstate))

/- ---------------------------------------------------------------------- -/
/- Attempt to dispose of the non-equational assumption(s) of a theorem.   -/
/- ---------------------------------------------------------------------- -/

/-- Prove (and discharge) the non-equational monotonicity hypotheses of `th`. -/
def prove_monotonicity_hyps (B : BoolThms) (mthms : List thm) (IMP_REFL : thm) (th : thm) :
    IO (Except String thm) := do
  let prove := Tactics.prove B
  let tac : tactic :=
    THEN B (REPEAT B (GEN_TAC B))
      (THEN B (DISCH_THEN B (REPEAT_TCL (CONJUNCTS_THEN B) (ASSUME_TAC B)))
        (THEN B (REPEAT B (CONJ_TAC B)) (MONO_TAC B mthms IMP_REFL)))
  -- mths = mapfilter (fun t => prove(t,tac)) (filter (not o is_eq) (hyp th))
  -- (ind_defs.ml 297).  `is_eq` and `not` are both total, so plain `o`.
  let cands := (hyp th).filter (not o is_eq)
  let rec collect : List term → List thm → IO (List thm)
    | [], acc => return acc.reverse
    | t :: ts, acc => do
        match ← (prove t tac : IO (Except String thm)) with
        | .ok mth => collect ts (mth :: acc)
        | .error _ => collect ts acc
  let mths ← collect cands []
  -- itlist PROVE_HYP mths th
  return (itlistM PROVE_HYP mths th)

/- ======================================================================= -/
/- Part 3: The final user wrapper, with schematic variables added.          -/
/- ======================================================================= -/

/-- `pare_comb qvs tm`: strip trailing arguments from `tm` until it shares no
    free variables with `qvs` and all its arguments are variables. -/
partial def pare_comb (qvs : List term) (tm : term) : Except String term :=
  if intersect (frees tm) qvs == [] && forall' is_var (strip_comb tm).2 then .ok tm
  -- ind_defs.ml 307-311: `rator`'s Failure must propagate (not fall back to tm).
  else do pare_comb qvs (← rator tm)

/-- Generalize schematic variables `vs` in the definition-hypotheses of `th`. -/
def generalize_schematic_variables (B : BoolThms) (gflag : Bool) (vs : List term) (th : thm) :
    IO (Except String thm) := do
  -- l' = mk_var(lname, itlist (mk_fun_ty o type_of) vs lty)   (ind_defs.ml 315).
  -- `type_of` is total and `mk_fun_ty` is IO-valued, so plain `o` types: the
  -- composite is `term → hol_type → IO (Except ...)`, which is what the fold
  -- below consumes.  `type_of` runs FIRST.
  let funTyOf := mk_fun_ty o type_of
  let mkTy (lty : hol_type) : IO (Except String hol_type) := do
    let rec go : List term → IO (Except String hol_type)
      | [] => return .ok lty
      | v :: vs' => do
          match ← (go vs' : IO (Except String hol_type)) with
          | .error e => return .error e
          | .ok acc => (funTyOf v acc : IO (Except String hol_type))
    go vs
  let generalize_def (tm : term) (th : thm) : IO (Except String thm) := do
    match dest_eq tm with
    | .error e => return .error e
    | .ok (l, r) =>
      match dest_var l with
      | .error e => return .error e
      | .ok (lname, lty) =>
        match ← (mkTy lty : IO (Except String hol_type)) with
        | .error e => return .error e
        | .ok lty' =>
          let l' := mk_var lname lty'
          return (do
            let r' ← list_mk_abs vs r
            let tm' := safe_mk_eq l' r'
            let th0 ← RIGHT_BETAS vs (← ASSUME tm')
            let th1 ← INST [((← lhs (concl th0)), l)] (← B.DISCH tm th)
            B.MP th1 th0)
  let (defs, others) := (hyp th).partition is_eq
  let rec genAll : List term → thm → IO (Except String thm)
    | [], t => return .ok t
    | d :: ds, t => do
        match ← (genAll ds t : IO (Except String thm)) with
        | .error e => return .error e
        | .ok t' => (generalize_def d t' : IO (Except String thm))
  match ← (genAll defs th : IO (Except String thm)) with
  | .error e => return .error e
  | .ok th1 =>
    if gflag then
      return (do
        let others' ← others.mapM (fun t => do
          let fvs := frees t
          B.SPECL fvs (← ASSUME (← list_mk_forall fvs t)))
        B.GENL vs (← itlistM PROVE_HYP others' th1))
    else return .ok th1

/-- `derive_existence th`: existentially close the definitional hypotheses. -/
def derive_existence (B : BoolThms) (pth : thm) (th : thm) : Except String thm := do
  let defs := (hyp th).filter is_eq
  itlistM (fun d acc => EXISTS_EQUATION B pth d acc) defs th

/-- `make_definitions th`: turn the definitional hypotheses into real constant
    definitions (via `new_definition`) and discharge them. -/
def make_definitions (B : BoolThms) (th : thm) : IO (Except String thm) := do
  let defs := (hyp th).filter is_eq
  let rec mkDefs : List term → IO (Except String (List thm))
    | [] => return .ok []
    | d :: ds => do
        match ← (new_definition B d : IO (Except String thm)) with
        | .error e => return .error e
        | .ok dth =>
          match ← (mkDefs ds : IO (Except String (List thm))) with
          | .error e => return .error e
          | .ok rest => return .ok (dth :: rest)
  match ← (mkDefs defs : IO (Except String (List thm))) with
  | .error e => return .error e
  | .ok dths =>
    return (do
      let lhsConcls ← dths.mapM (fun dth => lhs (concl dth))
      let lhsDefs ← defs.mapM lhs
      let insts ← zip lhsConcls lhsDefs
      let base ← INST insts (← itlistM B.DISCH defs th)
      rev_itlistM (fun dth acc => B.MP acc dth) dths base)

/-- `unschematize_clauses clauses`: detect and abstract schematic variables,
    returning `(clauses', schematic-args)`. -/
def unschematize_clauses (clausesIn : List term) : IO (Except String (List term × List term)) := do
  -- schem = map (fun cls -> pare_comb avs (snd(dest_imp bod) or bod)) clauses
  -- pare_comb now propagates `rator`'s failure (ind_defs.ml 307-311), so thread it.
  match (clausesIn.mapM (fun cls =>
    let (avs, bod) := strip_forall cls
    let target := match Basics.dest_imp bod with | .ok (_, c) => c | .error _ => bod
    pare_comb avs target) : Except String (List term)) with
  | .error e => return .error e
  | .ok schem =>
  let schems := setify schem
  match schem with
  | [] => return .ok (clausesIn, [])
  | hdSchem :: _ =>
    if is_var hdSchem then return .ok (clausesIn, [])
    else
      -- check schematic-args used consistently
      if (setify (schems.map (fun s => (strip_comb s).2))).length != 1 then
        return .error "Schematic variables not used consistently"
      else
        match (do
          let avoids ← variables (← list_mk_conj clausesIn)
          -- hack_fn tm = mk_var(fst(dest_var(repeat rator tm)), type_of tm)
          let hack_fn (tm : term) : Except String term := do
            let (nm, _) ← dest_var (repeat' rator tm)
            .ok (mk_var nm (type_of tm))
          let grels ← variants avoids (← schems.mapM hack_fn)
          let crels ← zip grels schems
          pure (crels, (strip_comb (schems.head!)).2) : Except String (List (term × term) × List term)) with
        | .error e => return .error e
        | .ok (crels, fvs) =>
          match ← (subst crels : IO (Except String (term → IO (Except String term)))) with
          | .error e => return .error e
          | .ok substFn =>
            let rec substAll : List term → IO (Except String (List term))
              | [] => return .ok []
              | c :: cs => do
                  match ← (substFn c : IO (Except String term)) with
                  | .error e => return .error e
                  | .ok c' =>
                    match ← (substAll cs : IO (Except String (List term))) with
                    | .error e => return .error e
                    | .ok rest => return .ok (c' :: rest)
            match ← (substAll clausesIn : IO (Except String (List term))) with
            | .error e => return .error e
            | .ok clauses' => return .ok (clauses', fvs)

/-- `prove_inductive_properties tm`: unschematize, derive the nonschematic
    relations, and prove the monotonicity hypotheses. Returns `(fvs, th)`. -/
def prove_inductive_properties (B : BoolThms) (REFL_CLAUSE CONJ_ACI : thm) (t_tm : term)
    (mthms : List thm) (IMP_REFL : thm) (tm : term) :
    IO (Except String (List term × thm)) := do
  let clauses := conjuncts tm
  match ← (unschematize_clauses clauses : IO (Except String (List term × List term))) with
  | .error e => return .error e
  | .ok (clauses', fvs) =>
    match list_mk_conj clauses' with
    | .error e => return .error e
    | .ok closed =>
      match ← (derive_nonschematic_inductive_relations B REFL_CLAUSE CONJ_ACI t_tm closed
                : IO (Except String thm)) with
      | .error e => return .error e
      | .ok th =>
        match ← (prove_monotonicity_hyps B mthms IMP_REFL th : IO (Except String thm)) with
        | .error e => return .error e
        | .ok th' => return .ok (fvs, th')

/-- `prove_inductive_relations_exist tm`: prove the existence of relations
    satisfying the inductive clauses (schematic version). -/
def prove_inductive_relations_exist (B : BoolThms) (pth REFL_CLAUSE CONJ_ACI : thm) (t_tm : term)
    (mthms : List thm) (IMP_REFL : thm) (tm : term) : IO (Except String thm) := do
  match ← (prove_inductive_properties B REFL_CLAUSE CONJ_ACI t_tm mthms IMP_REFL tm
            : IO (Except String (List term × thm))) with
  | .error e => return .error e
  | .ok (fvs, th1) =>
    match ← (generalize_schematic_variables B true fvs th1 : IO (Except String thm)) with
    | .error e => return .error e
    | .ok th2 => return (derive_existence B pth th2)

/-- `find_redefinition tm (rth,ith,cth)`: matches `tm` against the stored rule
    theorem `rth` (whole-conclusion `PART_MATCH I`); on success returns the
    stored triple paired with the matched theorem. Used to detect benign
    redefinitions. -/
def find_redefinition (B : BoolThms) (tm : term) (trip : thm × thm × thm) :
    IO (Except String ((thm × thm × thm) × thm)) := do
  let (rth, _, _) := trip
  match ← (PART_MATCH B (fun t => .ok t) rth tm : IO (Except String thm)) with
  | .error e => return .error e
  | .ok mth => return .ok (trip, mth)

/-- Core of `new_inductive_definition`: takes the current registry `existing`
    and returns the `(rule, induct, cases)` triple plus, when a *new* predicate
    was defined, the entry to prepend to the registry (`none` on benign
    redefinition). The `the_inductive_definitions` ref itself lives in Session. -/
def new_inductive_definition_core (B : BoolThms) (_pth REFL_CLAUSE CONJ_ACI : thm) (t_tm : term)
    (mthms : List thm) (IMP_REFL : thm) (existing : List (thm × thm × thm)) (tm : term) :
    IO (Except String ((thm × thm × thm) × Option (thm × thm × thm))) := do
  let tm' := (strip_forall tm).2
  -- tryfind (find_redefinition tm') (!the_inductive_definitions)
  let rec tryRedef : List (thm × thm × thm) → IO (Option (thm × thm × thm))
    | [] => return none
    | trip :: rest => do
        match ← (find_redefinition B tm' trip : IO (Except String ((thm × thm × thm) × thm))) with
        | .ok (foundTrip, _) => do
            -- ind_defs.ml 367, inside the same `try`.
            warn true "Benign redefinition of inductive predicate"
            return (some foundTrip)
        | .error _ => tryRedef rest
  match ← (tryRedef existing : IO (Option (thm × thm × thm))) with
  | some trip => return .ok (trip, none)
  | none =>
    match ← (prove_inductive_properties B REFL_CLAUSE CONJ_ACI t_tm mthms IMP_REFL tm
              : IO (Except String (List term × thm))) with
    | .error e => return .error e
    | .ok (fvs, th1) =>
      match ← (generalize_schematic_variables B true fvs th1 : IO (Except String thm)) with
      | .error e => return .error e
      | .ok th2 =>
        match ← (make_definitions B th2 : IO (Except String thm)) with
        | .error e => return .error e
        | .ok th3 =>
          let avs := (strip_forall (concl th3)).1
          match (do
            let spec ← B.SPECL avs th3
            let (r, ic) ← B.CONJ_PAIR spec
            let (i, c) ← B.CONJ_PAIR ic
            let gr ← B.GENL avs r
            let gi ← B.GENL avs i
            let gc ← B.GENL avs c
            pure (gr, gi, gc) : Except String (thm × thm × thm)) with
          | .error e => return .error e
          | .ok trip => return .ok (trip, some trip)

/- ---------------------------------------------------------------------- -/
/- Derivation of "strong induction".                                      -/
/- ---------------------------------------------------------------------- -/

/-- `dest_ibod tm`: from a clause `!avs. ant ==> con`, return `(n, (prator ant,
    prator con))` where `n = |avs|` and `prator = funpow n rator`. -/
def dest_ibod (tm : term) : Except String (Nat × (term × term)) := do
  let (avs, ibod) := strip_forall tm
  let n := avs.length
  let (ant, con) ← Basics.dest_imp ibod
  let pa ← funpowM n rator ant
  let pc ← funpowM n rator con
  return (n, (pa, pc))

/-- `prove_triv tm`: prove a trivial conjunctive-implication tautology. -/
partial def prove_triv (B : BoolThms) (tm : term) : Except String thm := do
  if Basics.is_conj tm then do
    let (l, r) ← Basics.dest_conj tm
    B.CONJ (← prove_triv B l) (← prove_triv B r)
  else
    let (avs, bod) := strip_forall tm
    let (a, c) ← Basics.dest_imp bod
    let ths := B.CONJUNCTS (← ASSUME a)
    let th ← find (fun t => aconv c (concl t)) ths
    B.GENL avs (← B.DISCH a th)

/-- `weaken_triv th`: weaken a trivial conjunctive theorem. -/
partial def weaken_triv (B : BoolThms) (th : thm) : Except String thm := do
  if Basics.is_conj (concl th) then do
    B.CONJ (← weaken_triv B (← B.CONJUNCT1 th)) (← weaken_triv B (← B.CONJUNCT2 th))
  else
    let (avs, _) := strip_forall (concl th)
    let th1 ← B.SPECL avs th
    let (a, _) ← Basics.dest_imp (concl th1)
    B.GENL avs (← B.DISCH a (← B.CONJUNCT2 (← B.UNDISCH th1)))

/-- `derive_strong_induction (rth, ith)`: derive the strong-induction theorem
    from the rule and (weak) induction theorems. -/
def derive_strong_induction (B : BoolThms) (MONO_AND : thm) (mthms : List thm) (IMP_REFL : thm)
    (rth ith : thm) : IO (Except String thm) := do
  let MATCH_IMPS (th : thm) : IO (Except String thm) := MATCH_MP B MONO_AND th
  let (ovs, ibod) := strip_forall (concl ith)
  match (do
    let (iant, icon) ← Basics.dest_imp ibod
    let ibods ← (conjuncts icon).mapM dest_ibod
    let (ns, prrs) := unzip ibods
    let (rs, ps) := unzip prrs
    let gs ← variants (← variables ibod) ps
    let (svs, _tvs) ← chop_list (ovs.length - ns.length) ovs
    let sth ← B.SPECL svs rth
    let jth ← B.SPECL svs ith
    pure (iant, icon, ns, prrs, rs, ps, gs, svs, sth, jth)
    : Except String _) with
  | .error e => return .error e
  | .ok (iant, icon, ns, prrs, rs, ps, gs, svs, sth, jth) =>
    -- gimps = subst (zip gs rs) icon
    match ← (do
      match zip gs rs with
      | .error e => return (.error e : Except String term)
      | .ok gr => match ← (subst gr : IO (Except String (term → IO (Except String term)))) with
                  | .error e => return .error e
                  | .ok f => (f icon : IO (Except String term))) with
    | .error e => return .error e
    | .ok gimps =>
      -- prs = map2 (fun n (r,p) -> ...) ns prrs   (uses genvar : IO)
      let mkPr (n : Nat) (rp : term × term) : IO (Except String term) := do
        let (r, p) := rp
        match (nsplit dest_fun_ty (List.range n) (type_of r) : Except String (List hol_type × hol_type)) with
        | .error e => return .error e
        | .ok (tys, _ty) =>
          let gvs ← tys.mapM genvar
          return (do list_mk_abs gvs (← mk_conj (← list_mk_comb r gvs) (← list_mk_comb p gvs)))
      let rec mkPrs : List Nat → List (term × term) → IO (Except String (List term))
        | n :: ns', rp :: rps => do
            match ← (mkPr n rp : IO (Except String term)) with
            | .error e => return .error e
            | .ok pr => match ← (mkPrs ns' rps : IO (Except String (List term))) with
                        | .error e => return .error e
                        | .ok rest => return .ok (pr :: rest)
        | _, _ => return .ok []
      match ← (mkPrs ns prrs : IO (Except String (List term))) with
      | .error e => return .error e
      | .ok prs =>
        -- modify_rule rcl itm
        let modify_rule (rcl : thm) (itm : term) : IO (Except String thm) := do
          let (avs, bod) := strip_forall itm
          if Basics.is_imp bod then
            match (do
              let (a, c) ← Basics.dest_imp bod
              let sub ← vsubst (← zip gs ps)
              let mgoal ← mk_imp gimps (← mk_imp (sub a) a)
              let mall ← list_mk_forall (gs ++ ps ++ avs) mgoal
              pure (a, c, mall) : Except String (term × term × term)) with
            | .error e => return .error e
            | .ok (_a, c, mall) =>
              match ← (do
                let mth ← liftExcept (ASSUME mall)
                let ith_r ← liftExcept (do BETA_RULE (← B.SPECL (prs ++ rs ++ avs) mth))
                let jth_r ← liftExcept (do B.MP ith_r (← prove_triv B (← lhand (concl ith_r))))
                let t ← liftExcept (lhand (concl jth_r))
                let kth_r ← liftExcept (B.UNDISCH jth_r)
                let ntm ← liftExcept (list_mk_forall avs (← mk_imp t c))
                let lth_r ← liftExcept (do B.MP (← B.SPECL avs rcl) kth_r)
                let lth_p ← liftExcept (do B.UNDISCH (← B.SPECL avs (← ASSUME ntm)))
                liftExcept (do B.DISCH ntm (← B.GENL avs (← B.DISCH t (← B.CONJ lth_r lth_p))))
                : ExceptT String IO thm).run with
              | x => return x
          else
            return (do
              B.DISCH itm (← B.GENL avs (← B.CONJ (← B.SPECL avs rcl) (← B.SPECL avs (← ASSUME itm)))))
        -- mimps = map2 modify_rule (CONJUNCTS sth) (conjuncts iant)
        let rec mkMimps : List thm → List term → IO (Except String (List thm))
          | rcl :: rcls, itm :: itms => do
              match ← (modify_rule rcl itm : IO (Except String thm)) with
              | .error e => return .error e
              | .ok m => match ← (mkMimps rcls itms : IO (Except String (List thm))) with
                         | .error e => return .error e
                         | .ok rest => return .ok (m :: rest)
          | _, _ => return .ok []
        match ← (mkMimps (B.CONJUNCTS sth) (conjuncts iant) : IO (Except String (List thm))) with
        | .error e => return .error e
        | .ok mimps =>
          -- th1 = end_itlist (fun th th' -> MATCH_IMPS(CONJ th th')) mimps
          let rec foldImps : List thm → IO (Except String thm)
            | [] => return .error "derive_strong_induction: no rules"
            | [x] => return .ok x
            | x :: xs => do
                match ← (foldImps xs : IO (Except String thm)) with
                | .error e => return .error e
                | .ok acc =>
                  match B.CONJ x acc with
                  | .error e => return .error e
                  | .ok cj => (MATCH_IMPS cj : IO (Except String thm))
          match ← (foldImps mimps : IO (Except String thm)) with
          | .error e => return .error e
          | .ok th1 =>
            match ← (do
              let th2 ← liftExcept (do BETA_RULE (← B.SPECL prs jth))
              let th3 ← liftExcept (B.IMP_TRANS th1 th2)
              let nasm ← liftExcept (lhand (concl th3))
              let wk ← liftExcept (weaken_triv B (← B.UNDISCH th3))
              let th4 ← liftExcept (B.GENL ps (← B.DISCH nasm wk))
              pure th4 : ExceptT String IO thm).run with
            | .error e => return .error e
            | .ok th4 =>
              match ← (prove_monotonicity_hyps B mthms IMP_REFL th4 : IO (Except String thm)) with
              | .error e => return .error e
              | .ok pmh => return (B.GENL svs pmh)

end HolCore.IndDefs
