/- File: Pair.lean
Syntax sugaring; theory of pairing, with a bit of support.
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Original (c) Copyright, Marco Maggesi 2015
Lean4 translation by Chris Walton 2026 -/

import HolCore.Bool
import HolCore.Equal
import HolCore.Drule
import HolCore.Tactics
import HolCore.Itab
import HolCore.Simp
import HolCore.Parser
import HolCore.Theorems
import HolCore.IndDefs
import HolCore.Classic
import HolCore.Trivia
import HolCore.Canon
import HolCore.Meson
import HolCore.ImpConv
import HolMath.Base

namespace HolMath.Pair

set_option maxRecDepth 4000

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/- ---------------------------------------------------------------------- -/
/- Constants implementing (or at least tagging) syntactic sugar.          -/
/- ---------------------------------------------------------------------- -/

/- ---------------------------------------------------------------------- -/
/- Pair type.                                                             -/
/- ---------------------------------------------------------------------- -/

/-- The definitions `pair.ml` declares.  These are made in `Session` (the
    `new_definition`/`new_type_definition` calls mutate the kernel's constant
    and type tables), and bundled here so downstream code can refer to them by
    name rather than by position. -/
structure PairDefs where
  /-- `|- LET f x = f x`. -/
  LET_DEF : thm
  /-- `|- LET_END t = t`. -/
  LET_END_DEF : thm
  /-- `|- GABS P = (@) P`. -/
  GABS_DEF : thm
  /-- `|- GEQ a b = (a = b)`. -/
  GEQ_DEF : thm
  /-- `|- _SEQPATTERN = \r s x. if ?y. r x y then r x else s x`. -/
  SEQPATTERN : thm
  /-- `|- _UNGUARDED_PATTERN = \p r. p /\ r`. -/
  UNGUARDED_PATTERN : thm
  /-- `|- _GUARDED_PATTERN = \p g r. p /\ g /\ r`. -/
  GUARDED_PATTERN : thm
  /-- `|- _MATCH = \e r. if (?!) (r e) then (@) (r e) else @z. F`. -/
  MATCH : thm
  /-- `|- _FUNCTION = \r x. if (?!) (r x) then (@) (r x) else @z. F`. -/
  FUNCTION : thm
  /-- `|- mk_pair x y = \a b. (a = x) /\ (b = y)`. -/
  mk_pair_def : thm
  /-- `PAIR_EXISTS_THM` (pair.ml 51), proved before the type definition. -/
  PAIR_EXISTS_THM : thm
  /-- The `prod` type bijection, from `new_type_definition`. -/
  prod_tybij : thm
  /-- `|- x,y = ABS_prod(mk_pair x y)`. -/
  COMMA_DEF : thm
  /-- `|- FST p = @x. ?y. p = x,y`. -/
  FST_DEF : thm
  /-- `|- SND p = @y. ?x. p = x,y`. -/
  SND_DEF : thm
  deriving Inhabited

/-- Theorems established by `pair.ml`. -/
structure PairThms where
  PAIR_EXISTS_THM : thm
  REP_ABS_PAIR    : thm
  PAIR_EQ         : thm
  PAIR_SURJECTIVE : thm
  FST             : thm
  SND             : thm
  PAIR            : thm
  pair_INDUCT     : thm
  pair_RECURSION  : thm
  FORALL_PAIR_THM : thm
  EXISTS_PAIR_THM : thm
  LAMBDA_PAIR_THM : thm
  LAMBDA_PAIR     : thm
  LAMBDA_TRIPLE_THM : thm
  LAMBDA_TRIPLE   : thm
  PAIRED_ETA_THM  : thm
  FORALL_UNCURRY  : thm
  EXISTS_UNCURRY  : thm
  EXISTS_CURRY    : thm
  FORALL_CURRY    : thm
  FORALL_UNPAIR_THM : thm
  EXISTS_UNPAIR_THM : thm
  FORALL_PAIR_FUN_THM : thm
  EXISTS_PAIR_FUN_THM : thm
  FORALL_UNPAIR_FUN_THM : thm
  EXISTS_UNPAIR_FUN_THM : thm
  EXISTS_SWAP_FUN_THM : thm
  FORALL_PAIRED_THM : thm
  EXISTS_PAIRED_THM : thm
  FORALL_TRIPLED_THM : thm
  EXISTS_TRIPLED_THM : thm
  CHOICE_UNPAIR_THM : thm
  CHOICE_PAIRED_THM : thm
  deriving Inhabited

/-- The theorems of `pair.ml`, in file order.  The definitions, the `prod`
    type definition and PAIR_EXISTS_THM (proved before it) are made by
    Session; `installGenBeta` is the stateful step pair.ml takes after
    pair_RECURSION (`extend_basic_rewrites`, `inductive_type_store`,
    `extend_basic_convs`). -/
@[nospecialize]
def setupPair [HolBase] (D : DSLThms)
    (ETA_AX : thm)
    (PAIR_EXISTS_THM prod_tybij mk_pair_def COMMA_DEF FST_DEF SND_DEF : thm)
    (o_DEF : thm)
    (MESON_TAC ASM_MESON_TAC : List thm → tactic)
    (MESON' : List thm → term → IO (Except String thm))
    (SELECT_ELIM_TAC : tactic)
    (installGenBeta : thm → thm → thm → thm → thm → IO (Except String Unit)) :
    ExceptT String IO PairThms := do
  let MESON (ths : List thm) (t : term) : ExceptT String IO thm := MESON' ths t
  let INTRO_TAC := D.INTRO_TAC
  let { FORALL_DEF, .. } := HolBase.B
  let { FUN_EQ_THM, SELECT_UNIQUE, NOT_EXISTS_THM, .. } := HolBase.C

  /- Pair type. -/

  let REP_ABS_PAIR ← prove
   r"!(x:A) (y:B). REP_prod (ABS_prod (mk_pair x y)) = mk_pair x y"
   (MESON_TAC [prod_tybij])

  let PAIR_EQ ← prove
   r"!(x:A) (y:B) a b. (x,y = a,b) <=> (x = a) /\ (y = b)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [REWRITE_TAC [COMMA_DEF] THEN
      DISCH_THEN (MP_TAC o AP_TERM (← q r"REP_prod:A#B->A->B->bool")) THEN
      REWRITE_TAC [REP_ABS_PAIR] THEN REWRITE_TAC [mk_pair_def, FUN_EQ_THM],
      ALL_TAC] THEN
    MESON_TAC [])

  let PAIR_SURJECTIVE ← prove
   r"!p:A#B. ?x y. p = x,y"
   (GEN_TAC THEN REWRITE_TAC [COMMA_DEF] THEN
    MP_TAC (← SPEC (← q r"REP_prod p :A->B->bool") (← CONJUNCT2 prod_tybij)) THEN
    REWRITE_TAC [← CONJUNCT1 prod_tybij] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") (X_CHOOSE_THEN (← q r"b:B") MP_TAC)) THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"ABS_prod:(A->B->bool)->A#B")) THEN
    REWRITE_TAC [← CONJUNCT1 prod_tybij] THEN DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXISTS_TAC [← q r"a:A", ← q r"b:B"] THEN REFL_TAC)

  let FST ← prove
   r"!(x:A) (y:B). FST(x,y) = x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [FST_DEF] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN GEN_TAC THEN BETA_TAC THEN
    REWRITE_TAC [PAIR_EQ] THEN EQ_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    EXISTS_TAC (← q r"y:B") THEN ASM_REWRITE_TAC [])

  let SND ← prove
   r"!(x:A) (y:B). SND(x,y) = y"
   (REPEAT GEN_TAC THEN REWRITE_TAC [SND_DEF] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN GEN_TAC THEN BETA_TAC THEN
    REWRITE_TAC [PAIR_EQ] THEN EQ_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    EXISTS_TAC (← q r"x:A") THEN ASM_REWRITE_TAC [])

  let PAIR ← prove
   r"!x:A#B. FST x,SND x = x"
   (GEN_TAC THEN
    (X_CHOOSE_THEN (← q r"a:A") (X_CHOOSE_THEN (← q r"b:B") SUBST1_TAC)
       (← SPEC (← q r"x:A#B") PAIR_SURJECTIVE)) THEN
    REWRITE_TAC [FST, SND])

  let pair_INDUCT ← prove
   r"!P:A#B->bool. (!x y. P (x,y)) ==> !p. P p"
   (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM PAIR] THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC)

  let pair_RECURSION ← prove
   r"!PAIR'. ?fn:A#B->C. !a0 a1. fn (a0,a1) = PAIR' a0 a1"
   (GEN_TAC THEN EXISTS_TAC (← q r"\p. (PAIR':A->B->C) (FST p) (SND p)") THEN
    REWRITE_TAC [FST, SND])

  -- extend_basic_rewrites [FST; SND; PAIR], the prod entry in
  -- inductive_type_store and extend_basic_convs GEN_BETA_CONV.
  ExceptT.mk (installGenBeta FST SND PAIR pair_INDUCT pair_RECURSION)

  /- Convenient rules to eliminate binders over pairs. -/

  let FORALL_PAIR_THM ← prove
   r"!P:A#B->bool. (!p. P p) <=> (!p1 p2. P(p1,p2))"
   (MESON_TAC [PAIR])

  let EXISTS_PAIR_THM ← prove
   r"!P:A#B->bool. (?p. P p) <=> ?p1 p2. P(p1,p2)"
   (MESON_TAC [PAIR])

  let LAMBDA_PAIR_THM ← prove
   r"!t:A#B->C. (\p. t p) = (\(x,y). t(x,y))"
   (REWRITE_TAC [FORALL_PAIR_THM, FUN_EQ_THM])

  let LAMBDA_PAIR ← prove
   r"!f:A->B->C. (\(x,y). f x y) = (\p. f (FST p) (SND p))"
   (REWRITE_TAC [LAMBDA_PAIR_THM])

  let LAMBDA_TRIPLE_THM ← prove
   r"!f:A#B#C->D. (\t. f t) = (\(x,y,z). f(x,y,z))"
   (REWRITE_TAC [FORALL_PAIR_THM, FUN_EQ_THM])

  let LAMBDA_TRIPLE ← prove
   r"!f:A->B->C->D.
   (\(x,y,z). f x y z) = (\t. f (FST t) (FST(SND t)) (SND(SND t)))"
   (REWRITE_TAC [LAMBDA_TRIPLE_THM])

  let PAIRED_ETA_THM ← prove
   r"(!f:A#B->C. (\(x,y). f (x,y)) = f) /\
   (!f:A#B#C->D. (\(x,y,z). f (x,y,z)) = f) /\
   (!f:A#B#C#D->E. (\(w,x,y,z). f (w,x,y,z)) = f)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM, FORALL_PAIR_THM])

  let FORALL_UNCURRY ← prove
   r"!P. (!f:A->B->C. P f) <=> (!f. P (\a b. f(a,b)))"
   (GEN_TAC THEN EQ_TAC THEN SIMP_TAC [] THEN DISCH_TAC THEN
    X_GEN_TAC (← q r"f:A->B->C") THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"\(a,b). (f:A->B->C) a b")) THEN SIMP_TAC [ETA_AX])

  let EXISTS_UNCURRY ← prove
   r"!P. (?f:A->B->C. P f) <=> (?f. P (\a b. f(a,b)))"
   (ONCE_REWRITE_TAC [← MESON [] (← q r"(?x. P x) <=> ~(!x. ~P x)")] THEN
    REWRITE_TAC [FORALL_UNCURRY])

  let EXISTS_CURRY ← prove
   r"!P:(A#B->C)->bool. (?f. P f) <=> (?f. P (\(a,b). f a b))"
   (REWRITE_TAC [EXISTS_UNCURRY, PAIRED_ETA_THM])

  let FORALL_CURRY ← prove
   r"!P:(A#B->C)->bool. (!f. P f) <=> (!f. P (\(a,b). f a b))"
   (REWRITE_TAC [FORALL_UNCURRY, PAIRED_ETA_THM])

  let FORALL_UNPAIR_THM ← prove
   r"!P:A->B->bool. (!x y. P x y) <=> !z. P (FST z) (SND z)"
   (REWRITE_TAC [FORALL_PAIR_THM, FST, SND] THEN MESON_TAC [])

  let EXISTS_UNPAIR_THM ← prove
   r"!P:A->B->bool. (?x y. P x y) <=> ?z. P (FST z) (SND z)"
   (REWRITE_TAC [EXISTS_PAIR_THM, FST, SND] THEN MESON_TAC [])

  let FORALL_PAIR_FUN_THM ← prove
   r"!P. (!f:A->B#C. P f) <=> (!g h. P(\a. g a,h a))"
   (GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [← GSYM ETA_AX] THEN
    GEN_REWRITE_TAC BINDER_CONV [← GSYM PAIR] THEN PURE_ASM_REWRITE_TAC [])

  let EXISTS_PAIR_FUN_THM ← prove
   r"!P. (?f:A->B#C. P f) <=> (?g h. P(\a. g a,h a))"
   (REWRITE_TAC [← MESON [] (← q r"(?x. P x) <=> ~(!x. ~P x)")] THEN
    REWRITE_TAC [FORALL_PAIR_FUN_THM])

  let FORALL_UNPAIR_FUN_THM ← prove
   r"!P:(A->B)->(A->C)->bool. (!f g. P f g) <=> (!h. P (FST o h) (SND o h))"
   (REWRITE_TAC [FORALL_PAIR_FUN_THM, o_DEF, ETA_AX])

  let EXISTS_UNPAIR_FUN_THM ← prove
   r"!P:(A->B)->(A->C)->bool. (?f g. P f g) <=> (?h. P (FST o h) (SND o h))"
   (REWRITE_TAC [EXISTS_PAIR_FUN_THM, o_DEF, ETA_AX])

  let EXISTS_SWAP_FUN_THM ← prove
   r"!P:(A->B->C)->bool. (?f. P f) <=> (?f. P (\a b. f b a))"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_TAC (← q r"f:A->B->C")) THEN
      EXISTS_TAC (← q r"\b a. (f:A->B->C) a b"),
      DISCH_THEN (X_CHOOSE_TAC (← q r"f:B->A->C")) THEN
      EXISTS_TAC (← q r"\b a. (f:B->A->C) a b")] THEN
    ASM_REWRITE_TAC [ETA_AX])

  /- Related theorems for explicitly paired quantifiers. -/

  let FORALL_PAIRED_THM ← prove
   r"!P:A->B->bool. (!(x,y). P x y) <=> (!x y. P x y)"
   (GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [FORALL_DEF] THEN
    REWRITE_TAC [FUN_EQ_THM, FORALL_PAIR_THM])

  let EXISTS_PAIRED_THM ← prove
   r"!P:A->B->bool. (?(x,y). P x y) <=> (?x y. P x y)"
   (GEN_TAC THEN MATCH_MP_TAC (← TAUT (← q r"(~p <=> ~q) ==> (p <=> q)")) THEN
    REWRITE_TAC [← REWRITE_RULE [ETA_AX] NOT_EXISTS_THM, FORALL_PAIR_THM])

  /- Likewise for tripled quantifiers (could continue with the same proof). -/

  let FORALL_TRIPLED_THM ← prove
   r"!P:A->B->C->bool. (!(x,y,z). P x y z) <=> (!x y z. P x y z)"
   (GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [FORALL_DEF] THEN
    REWRITE_TAC [FUN_EQ_THM, FORALL_PAIR_THM])

  let EXISTS_TRIPLED_THM ← prove
   r"!P:A->B->C->bool. (?(x,y,z). P x y z) <=> (?x y z. P x y z)"
   (GEN_TAC THEN MATCH_MP_TAC (← TAUT (← q r"(~p <=> ~q) ==> (p <=> q)")) THEN
    REWRITE_TAC [← REWRITE_RULE [ETA_AX] NOT_EXISTS_THM, FORALL_PAIR_THM])

  /- Similar theorems for the choice operator. -/

  let CHOICE_UNPAIR_THM ← prove
   r"!P. (@(x:A,y:B). P x y) = (@p. P (FST p) (SND p))"
   (REWRITE_TAC [LAMBDA_PAIR])

  let CHOICE_PAIRED_THM ← prove
   r"!P Q. (?x:A y:B. P x y) /\ (!x y. P x y ==> Q(x,y)) ==> Q (@(x,y). P x y)"
   (INTRO_TAC "!P Q; (@x0 y0. P0) PQ" THEN
    SUBGOAL_THEN (← q r"(\ (x:A,y:B). P x y:bool) = (\p. P (FST p) (SND p))")
      SUBST1_TAC THENL
    [REWRITE_TAC [LAMBDA_PAIR_THM], SELECT_ELIM_TAC] THEN
    INTRO_TAC "![c]; c" THEN ONCE_REWRITE_TAC [← GSYM PAIR] THEN
    REMOVE_THEN "PQ" MATCH_MP_TAC THEN REMOVE_THEN "c" MATCH_MP_TAC THEN
    REWRITE_TAC [EXISTS_PAIR_THM] THEN ASM_MESON_TAC [])

  return { PAIR_EXISTS_THM, REP_ABS_PAIR, PAIR_EQ, PAIR_SURJECTIVE,
           FST, SND, PAIR, pair_INDUCT, pair_RECURSION,
           FORALL_PAIR_THM, EXISTS_PAIR_THM, LAMBDA_PAIR_THM, LAMBDA_PAIR,
           LAMBDA_TRIPLE_THM, LAMBDA_TRIPLE, PAIRED_ETA_THM,
           FORALL_UNCURRY, EXISTS_UNCURRY, EXISTS_CURRY, FORALL_CURRY,
           FORALL_UNPAIR_THM, EXISTS_UNPAIR_THM,
           FORALL_PAIR_FUN_THM, EXISTS_PAIR_FUN_THM,
           FORALL_UNPAIR_FUN_THM, EXISTS_UNPAIR_FUN_THM, EXISTS_SWAP_FUN_THM,
           FORALL_PAIRED_THM, EXISTS_PAIRED_THM,
           FORALL_TRIPLED_THM, EXISTS_TRIPLED_THM,
           CHOICE_UNPAIR_THM, CHOICE_PAIRED_THM }

end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv conv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic goal)
open HolLight

/- ---------------------------------------------------------------------- -/
/- Syntax operations.                                                     -/
/- ---------------------------------------------------------------------- -/

/-- `is_pair = is_binary ","`. -/
def is_pair : term → Bool := is_binary ","

/-- `dest_pair = dest_binary ","`. -/
def dest_pair : term → Except String (term × term) := dest_binary ","

/-- `mk_pair` (pair.ml): `,` instantiated at the types of the two sides.
    `mk_const` reads the constant table, hence IO. -/
def mk_pair (lr : term × term) : IO (Except String term) := ExceptT.run do
  let (l, r) := lr
  let ptm ← ExceptT.mk (mk_const "," [])
  let ptm' := inst [(type_of l, aty), (type_of r, bty)] ptm
  liftExcept (do mk_comb (← mk_comb ptm' l) r)

/- ---------------------------------------------------------------------- -/
/- Analog of ABS_CONV for generalized abstraction.                        -/
/- ---------------------------------------------------------------------- -/

/-- `GABS_CONV` (pair.ml 48-53). -/
def GABS_CONV [HolBase] (conv : ioconv) : ioconv := fun tm => ExceptT.run do
  if is_abs tm then ExceptT.mk (ABS_CONV conv tm) else
  let (gabs, bod) ← liftExcept (dest_comb tm)
  let (f, qtm) ← liftExcept (dest_abs bod)
  let (xs, bod) := strip_forall qtm
  AP_TERM gabs (← liftExcept (ABS f (← xs.foldrM MK_FORALL (← ExceptT.mk (RAND_CONV conv bod)))))

/- ---------------------------------------------------------------------- -/
/- General beta-conversion over linear pattern of nested constructors.    -/
/- ---------------------------------------------------------------------- -/

/-- What `GEN_BETA_CONV` closes over: pair.ml's `projection_cache` ref, a
    reader for `inductive_type_store`, `GEQ_DEF`, and the `GABS_RULE`
    lemma `|- (?) P ==> P (GABS P)`. -/
structure GenBetaDeps where
  cache : IO.Ref (List (String × List thm))
  store : IO (List (String × (Int × thm × thm)))
  GEQ_DEF : thm
  gabsRulePth : thm

/-- `create_projections conname` (pair.ml 59-90), memoised in `G.cache`. -/
def createProjections [HolBase] (G : GenBetaDeps) (conname : String) :
    ExceptT String IO (List thm) := do
  match assoc conname (← G.cache.get) with
  | .ok ths => return ths
  | .error _ =>
  let genty ← ExceptT.mk (get_const_type conname)
  let (conty, _) ← liftExcept (dest_type (repeat' (Prod.snd oEm dest_fun_ty) genty))
  let (_, _, rth) ← liftExcept (assoc conty (← G.store))
  let sth ← SPEC_ALL rth
  let (evs, bod) := strip_exists (concl sth)
  let cjs := conjuncts bod
  let ourcj ← liftExcept (find (fun cj =>
    (do let (n, _) ← dest_const (strip_comb (← rand (← lhand (strip_forall cj).2))).1
        pure (n == conname) : Except String Bool).toOption.getD false) cjs)
  let n ← liftExcept (index ourcj cjs)
  let (avs, eqn) := strip_forall ourcj
  let (con', args) := strip_comb (← liftExcept (rand eqn))
  let (aargs, zargs) ← liftExcept (chop_list avs.length args)
  let gargs ← zargs.mapM (fun a => (genvar (type_of a) : IO term))
  let gcon ← (genvar (← avs.foldrM (fun a ty => ExceptT.mk (mk_fun_ty (type_of a) ty))
                         (type_of (← liftExcept (rand eqn)))) : IO term)
  let bth ← INST [(← liftExcept (do list_mk_abs (aargs ++ gargs) (← list_mk_comb gcon avs)),
                   con')] sth
  let cth ← liftExcept (el n (CONJUNCTS (← ASSUME (strip_exists (concl bth)).2)))
  let dth ← CONV_RULE (funpow avs.length BINDER_CONV (RAND_CONV BETAS_CONV)) cth
  let eth ← SIMPLE_EXISTS (← liftExcept (do rator (← lhand (strip_forall (concl dth)).2))) dth
  let fth ← PROVE_HYP bth (← evs.foldrM SIMPLE_CHOOSE eth)
  let zty := type_of (← liftExcept (rand (strip_forall (concl dth)).2))
  let mk_projector (a : term) : ExceptT String IO thm := do
    let ity := type_of a
    let th ← BETA_RULE (← PINST [(ity, zty)] [(← liftExcept (list_mk_abs avs a), gcon)] fth)
    SYM (← SPEC_ALL (← SELECT_RULE th))
  let ths ← avs.mapM mk_projector
  G.cache.modify ((conname, ths) :: ·)
  return ths

/-- `create_iterated_projections` (pair.ml 97-107). -/
partial def createIteratedProjections [HolBase] (G : GenBetaDeps) (tm : term) :
    ExceptT String IO (List thm) := do
  if frees tm == [] then return []
  if is_var tm then return [REFL tm]
  let (con, _args) := strip_comb tm
  let prjths ← createProjections G (← liftExcept (dest_const con)).1
  let atm ← liftExcept (do rand (← rand (concl (← hd prjths))))
  let instn ← term_match [] atm tm
  let arths ← prjths.mapM (INSTANTIATE instn)
  let ths ← arths.mapM (fun arth => do
    let sths ← createIteratedProjections G (← liftExcept (lhand (concl arth)))
    sths.mapM (CONV_RULE (RAND_CONV (SUBS_CONV [arth]))))
  return unions' equals_thm ths

/-- `GEN_BETA_CONV` (pair.ml 57-125).  `GEQ_CONV`, `DEGEQ_RULE` and
    `GABS_RULE` are built from `G` as in OCaml. -/
def GEN_BETA_CONV [HolBase] (G : GenBetaDeps) : ioconv := fun tm => ExceptT.run do
  match (HolCore.Equal.BETA_CONV tm : Except String thm) with
  | .ok th => return th
  | .error _ =>
  let GEQ_CONV : ioconv := fun t => ExceptT.run do ExceptT.mk (REWR_CONV (← GSYM G.GEQ_DEF) t)
  let DEGEQ_RULE := CONV_RULE (REWR_CONV G.GEQ_DEF)
  let GABS_RULE := MATCH_MP G.gabsRulePth
  let (l, r) ← liftExcept (dest_comb tm)
  let (vstr, bod) ← liftExcept (dest_gabs l)
  let instn ← term_match [] vstr r
  let prjs ← createIteratedProjections G vstr
  let th1 ← ExceptT.mk (SUBS_CONV prjs bod)
  let bod' ← liftExcept (rand (concl th1))
  let gv ← (genvar (type_of vstr) : IO term)
  let subst1 ← ExceptT.mk (subst [(gv, vstr)])
  let pat ← liftExcept (mk_abs gv (← ExceptT.mk (subst1 bod')))
  let th2 ← TRANS (← ExceptT.mk (BETA_CONV (← liftExcept (mk_comb pat vstr)))) (← SYM th1)
  let avs := (strip_forall (← liftExcept (body (← liftExcept (rand l))))).1
  let th3 ← GENL avs th2
  let efn ← (genvar (type_of pat) : IO term)
  let subst2 ← ExceptT.mk (subst [(efn, pat)])
  let th4 ← EXISTS (← liftExcept (HolCore.Bool.mk_exists efn (← ExceptT.mk (subst2 (concl th3)))), pat) th3
  let th5 ← CONV_RULE (funpow (avs.length + 1) BINDER_CONV GEQ_CONV) th4
  let th6 ← CONV_RULE BETA_CONV (← GABS_RULE th5)
  INSTANTIATE instn (← DEGEQ_RULE (← SPEC_ALL th6))

/- ---------------------------------------------------------------------- -/
/- Expansion of a let-term.                                               -/
/- ---------------------------------------------------------------------- -/

/-- What the `let` machinery closes over: `LET_DEF`, `LET_END_DEF`, and
    `LET_TAC`'s depairing lemma and two tautologies. -/
structure LetDeps where
  LET_DEF : thm
  LET_END_DEF : thm
  letTacPth : thm
  taut1 : thm
  taut2 : thm

/-- `let_CONV` (pair.ml 148-166). -/
partial def let_CONV [HolBase] (L : LetDeps) (GEN_BETA_CONV : ioconv) : ioconv :=
  let let1_CONV := thenc_ (REWR_CONV L.LET_DEF) GEN_BETA_CONV
  let lete_CONV := REWR_CONV L.LET_END_DEF
  let rec EXPAND_BETAS_CONV (tm : term) : IO (Except String thm) := ExceptT.run do
    let tm' ← liftExcept (rator tm)
    let r1 : Except String thm ← (let1_CONV tm : IO (Except String thm))
    match r1 with
    | Except.ok th => return th
    | Except.error _ =>
    let th1 ← AP_THM (← ExceptT.mk (EXPAND_BETAS_CONV tm')) (← liftExcept (rand tm))
    let th2 ← ExceptT.mk (GEN_BETA_CONV (← liftExcept (rand (concl th1))))
    TRANS th1 th2
  fun tm => ExceptT.run do
    let (ltm, pargs) := strip_comb tm
    if (← liftExcept (dest_const ltm)).1 != "LET" || pargs == [] then throw "let_CONV"
    let abstm ← liftExcept (hd pargs)
    let (vs, _bod) := strip_gabs abstm
    let es ← liftExcept (tl pargs)
    let n := es.length
    if vs.length != n then throw "let_CONV"
    ExceptT.mk (thenc_ EXPAND_BETAS_CONV lete_CONV tm)

/-- `PATH_CONV` (equal.ml) for an `ioconv`: `l` = RATOR, `r` = RAND, else ABS. -/
def pathConvIO (s : String) (cnv : ioconv) : ioconv :=
  let rec go : List String → ioconv
    | []       => cnv
    | "l" :: t => RATOR_CONV (go t)
    | "r" :: t => RAND_CONV (go t)
    | _ :: t   => ABS_CONV (go t)
  go (explode s)

/-- `LET_TAC` (pair.ml 168-207). -/
def LET_TAC [HolBase] (L : LetDeps) (GEN_BETA_CONV : ioconv) : tactic :=
  let is_trivlet (tm : term) : Bool :=
    match dest_let tm with
    | .ok (assigs, _) => assigs.all (fun (x, y) => x == y)
    | .error _ => false
  let PROVE_DEPAIRING_EXISTS (tm : term) : ExceptT String IO thm := do
    let rewr1_CONV ← GEN_REWRITE_CONV_NET TOP_DEPTH_CONV [L.letTacPth]
    let rewr2_RULE := GEN_REWRITE_RULE (LAND_CONV ∘ DEPTH_CONV) [L.taut1, L.taut2]
    let th1 ← ExceptT.mk (rewr1_CONV tm)
    let tm1 ← liftExcept (rand (concl th1))
    let cjs := conjuncts tm1
    let vars ← liftExcept (cjs.mapM lhand)
    let th2 ← EQ_MP (← SYM th1) (← ASSUME tm1)
    let th3 ← DISCH_ALL (← vars.foldrM SIMPLE_EXISTS th2)
    let th4 ← INST (← liftExcept (cjs.mapM (fun t => do pure (← rand t, ← lhand t)))) th3
    MP (← rewr2_RULE th4) HolBase.B.TRUTH
  fun (asl, w) => ExceptT.run do
    let path ← liftExcept (match find_path is_trivlet w with
      | .ok p => .ok p | .error _ => find_path is_let w)
    let tm ← liftExcept (follow_path path w)
    let (assigs, _bod) ← liftExcept (dest_let tm)
    let abbrevs := mapfilter (fun (xy : term × term) =>
      if xy.1 == xy.2 then (failwith "" : Except String term) else .ok (safe_mk_eq xy.1 xy.2)) assigs
    let lvars ← liftExcept (abbrevs.foldrM (fun eq acc => do pure (union (frees (← lhs eq)) acc)) [])
    let avoids := itlist (fun (p : String × thm) acc => union (thm_frees p.2) acc) asl (frees w)
    let rename ← liftExcept (do vsubst (← zip (← variants avoids lvars) lvars))
    let abbrevs' ← liftExcept (abbrevs.mapM (fun eq => do
      let (l, r) ← dest_eq eq
      pure (safe_mk_eq (rename l) r)))
    let deprths ← abbrevs'.mapM PROVE_DEPAIRING_EXISTS
    ExceptT.mk ((MAP_EVERY (REPEAT_TCL CHOOSE_THEN
        (fun th => tactic_of do
           let th' ← SYM th
           pure (then_ (SUBST_ALL_TAC th') (ASSUME_TAC th')))) deprths |>
      fun t => then_ t (fun (asl', w') => ExceptT.run do
        let tm' ← liftExcept (follow_path path w')
        ExceptT.mk (CONV_TAC (pathConvIO path (fun _ => let_CONV L GEN_BETA_CONV tm')) (asl', w'))))
      (asl, w))

/- ---------------------------------------------------------------------- -/
/- Apply conversion "conv" to RHS of toplevel let-term                    -/
/- ---------------------------------------------------------------------- -/

/-- `SUBLET_CONV conv` (pair.ml 213-219). -/
partial def SUBLET_CONV (conv : ioconv) : ioconv :=
  let rec largconv (tm : term) : IO (Except String thm) :=
    match tm with
    | .Comb (.Const "LET" _) _ => pure (.ok (REFL tm))
    | .Comb _ _ => COMB2_CONV largconv conv tm
    | _ => pure (failwith "SUBLET_CONV")
  fun tm => if is_let tm then largconv tm else pure (failwith "SUBLET_CONV")

end

end HolMath.Pair
