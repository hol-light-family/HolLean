/- File: HolTest/RQETest.lean
Runtime test suite: Rqe/rqe_tactics_ext.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/asym.ml, Rqe/rol.ml, Rqe/poly_ext.ml, Rqe/lift_qelim.ml, Rqe/defs.ml, Rqe/testform_thms.ml, Rqe/condense_thms.ml, Rqe/inferisign_thms.ml, Rqe/matinsert_thms.ml, Rqe/signs_thms.ml, Rqe/inferpsign_thms.ml, Rqe/dedmatrix_thms.ml, Rqe/pdivides_thms.ml, Rqe/main_thms.ml, Rqe/work_thms.ml
(HolRQE/, wired by SessionRQE/).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Rqe/<file>.ml"`, then `string_of_thm`, newlines joined).
tools/rq<file>diff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here.  The files are
in one test module so that each SessionRQE module replays once. -/

import HolTest.CommonTest
import SessionRQE.RqeTacticsExt
import SessionRQE.Basic
import SessionRQE.RqeNum
import SessionRQE.RqeReal
import SessionRQE.ListRewrites
import SessionRQE.RqeList
import SessionRQE.Asym
import SessionRQE.Rol
import SessionRQE.PolyExt
import SessionRQE.LiftQelim
import SessionRQE.Defs
import SessionRQE.TestformThms
import SessionRQE.CondenseThms
import SessionRQE.InferisignThms
import SessionRQE.MatinsertThms
import SessionRQE.SignsThms
import SessionRQE.InferpsignThms
import SessionRQE.DedmatrixThms
import SessionRQE.PdividesThms
import SessionRQE.MainThms
import SessionRQE.WorkThms
import SessionRQE.RqeMain

open HolCore.Kernel HolTest.CommonTest

#eval SessionRQE.RqeTacticsExt.ensureRqeTacticsExt
#eval SessionRQE.Basic.ensureBasic
#eval SessionRQE.RqeNum.ensureRqeNum
#eval SessionRQE.RqeReal.ensureRqeReal
#eval SessionRQE.ListRewrites.ensureListRewrites
#eval SessionRQE.RqeList.ensureRqeList
#eval SessionRQE.Asym.ensureAsym
#eval SessionRQE.Rol.ensureRol
#eval SessionRQE.PolyExt.ensurePolyExt
#eval SessionRQE.LiftQelim.ensureLiftQelim
#eval SessionRQE.Defs.ensureDefs
#eval SessionRQE.TestformThms.ensureTestformThms
#eval SessionRQE.CondenseThms.ensureCondenseThms
#eval SessionRQE.InferisignThms.ensureInferisignThms
#eval SessionRQE.MatinsertThms.ensureMatinsertThms
#eval SessionRQE.SignsThms.ensureSignsThms
#eval SessionRQE.InferpsignThms.ensureInferpsignThms
#eval SessionRQE.DedmatrixThms.ensureDedmatrixThms
#eval SessionRQE.PdividesThms.ensurePdividesThms
#eval SessionRQE.MainThms.ensureMainThms
#eval SessionRQE.WorkThms.ensureWorkThms

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def check (lbl : String) (r : IO (Except String thm)) (expected : String) :
    IO Unit := do
  let got ← match ← r with
    | .ok th => pure (squash (← HolCore.Printer.string_of_thm th))
    | .error e => pure s!"FAIL {e}"
  if got == squash expected || got == expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

private unsafe def thm' (lbl : String) (th : thm) (expected : String) : IO Unit :=
  check lbl (pure (.ok th)) expected

private unsafe def qe (fm : String) (expected : String) : IO Unit :=
  check s!"REAL_QELIM_CONV {fm}" (do
    match ← HolCore.Parser.parse_term fm with
    | .ok t => SessionRQE.RqeMain.REAL_QELIM_CONV t
    | .error e => pure (.error e)) expected

namespace T

-- RqeTacticsExt
#eval thm' "RqeTacticsExt.lem" SessionRQE.RqeTacticsExt.«lem»
  "|- (a <=> b) <=> (a ==> b) /\\ (b ==> a)"

-- Basic
#eval thm' "Basic.IMP_AND_THM" SessionRQE.Basic.«IMP_AND_THM»
  "|- p ==> q ==> r <=> p /\\ q ==> r"
#eval thm' "Basic.AND_IMP_THM" SessionRQE.Basic.«AND_IMP_THM»
  "|- p /\\ q ==> r <=> p ==> q ==> r"

-- RqeNum
#eval thm' "RqeNum.nmax" SessionRQE.RqeNum.«nmax»
  "|- forall m n. nmax n m = (if n <= m then m else n)"
#eval thm' "RqeNum.SUC_1" SessionRQE.RqeNum.«SUC_1»
  "|- 1 + x = SUC x"

-- RqeReal
#eval thm' "RqeReal.REAL_DENSE" SessionRQE.RqeReal.«REAL_DENSE»
  "|- forall x y. x < y ==> (exists z. x < z /\\ z < y)"
#eval thm' "RqeReal.REAL_DIV_ADD_DISTRIB" SessionRQE.RqeReal.«REAL_DIV_ADD_DISTRIB»
  "|- forall x y z. (x + y) / z = x / z + y / z"
#eval thm' "RqeReal.BINOMIAL_LEMMA_LT" SessionRQE.RqeReal.«BINOMIAL_LEMMA_LT»
  "|- forall x y.        &0 < x /\\ &0 < y        ==> (forall n. 0 < n ==> x pow n + y pow n <= (x + y) pow n)"
#eval thm' "RqeReal.REAL_DIV_DENOM_LT" SessionRQE.RqeReal.«REAL_DIV_DENOM_LT»
  "|- forall x y z. &0 < x /\\ &0 < y /\\ y < z ==> x / z < x / y"

-- ListRewrites
#eval thm' "ListRewrites.NOT_NIL" SessionRQE.ListRewrites.«NOT_NIL»
  "|- forall l. ~(l = []) <=> (exists h t. l = CONS h t)"

-- RqeList
#eval thm' "RqeList.NOT_CONS" SessionRQE.RqeList.«NOT_CONS»
  "|- forall l. ~(exists h t. l = CONS h t) ==> l = []"
#eval thm' "RqeList.REMOVE" SessionRQE.RqeList.«REMOVE»
  "|- REMOVE x [] = [] /\\    REMOVE x (CONS h t) =    (let rest = REMOVE x t in if x = h then rest else CONS h rest)"
#eval thm' "RqeList.LIST_TRI" SessionRQE.RqeList.«LIST_TRI»
  "|- forall p.        p = [] \\/ (exists x. p = [x]) \\/ (exists x y t. p = CONS x (CONS y t))"
#eval thm' "RqeList.LENGTH_PAIR" SessionRQE.RqeList.«LENGTH_PAIR»
  "|- forall p. LENGTH p = 2 <=> (exists h t. p = [h; t])"

-- Asym
#eval thm' "Asym.LIM_INV_1N" SessionRQE.Asym.«LIM_INV_1N»
  "|- (\\n. &1 / &n) --> &0"
#eval thm' "Asym.NORMAL_ID" SessionRQE.Asym.«NORMAL_ID»
  "|- forall p. normal p <=> 0 < LENGTH p /\\ ~(LAST p = &0)"
#eval thm' "Asym.lem" SessionRQE.Asym.«lem»
  "|- forall x y z. --(x / (y + z)) = x / (--y + --z)"
#eval thm' "Asym.PNEG_AUX_NORMALIZE_LENGTH" SessionRQE.Asym.«PNEG_AUX_NORMALIZE_LENGTH»
  "|- forall p n. LENGTH (normalize (pneg_aux n p)) = LENGTH (normalize p)"

-- Rol
#eval thm' "Rol.real_ordered_list" SessionRQE.Rol.«real_ordered_list»
  "|- (real_ordered_list [] <=> true) /\\    (real_ordered_list (CONS h t) <=>     real_ordered_list t /\\ (t = [] \\/ h < HD t))"
#eval thm' "Rol.NOT_ROL" SessionRQE.Rol.«NOT_ROL»
  "|- forall l. ~real_ordered_list l ==> (exists n. EL n l >= EL (SUC n) l)"
#eval thm' "Rol.ROL_INSERT_FRONT_THM" SessionRQE.Rol.«ROL_INSERT_FRONT_THM»
  "|- forall x l.        real_ordered_list l /\\ ~(l = []) /\\ x < HD l        ==> real_ordered_list (CONS x l)"
#eval thm' "Rol.lem1" SessionRQE.Rol.«lem1»
  "|- forall x y. x < y ==> real_ordered_list [x; y]"

-- PolyExt
#eval thm' "PolyExt.POLY" SessionRQE.PolyExt.«POLY»
  "|- poly [] x = &0 /\\    poly [__c__] x = __c__ /\\    poly (CONS __h__ __t__) x = __h__ + x * poly __t__ x"
#eval thm' "PolyExt.POLY_DIFF_LEMMA" SessionRQE.PolyExt.«POLY_DIFF_LEMMA»
  "|- forall l n x.        ((\\x. x pow SUC n * poly l x) diffl         x pow n * poly (poly_diff_aux (SUC n) l) x)        x"
#eval thm' "PolyExt.le_lem" SessionRQE.PolyExt.«le_lem»
  "|- forall x y. x <= y <=> x - y <= &0"
#eval thm' "PolyExt.lem1" SessionRQE.PolyExt.«lem1»
  "|- x * x = x pow 2"

-- LiftQelim
#eval thm' "LiftQelim.OR_ASSOC" SessionRQE.LiftQelim.«OR_ASSOC»
  "|- (a \\/ b) \\/ c <=> a \\/ b \\/ c"

-- Defs
#eval thm' "Defs.sign_INDUCT" SessionRQE.Defs.«sign_INDUCT»
  "|- forall P.        P Zero /\\ P Pos /\\ P Neg /\\ P Nonzero /\\ P Unknown ==> (forall x. P x)"
#eval thm' "Defs.interpsign" SessionRQE.Defs.«interpsign»
  "|- (interpsign set ply Zero <=> (forall x. set x ==> ply x = &0)) /\\    (interpsign set ply Pos <=> (forall x. set x ==> ply x > &0)) /\\    (interpsign set ply Neg <=> (forall x. set x ==> ply x < &0)) /\\    (interpsign set ply Nonzero <=> (forall x. set x ==> ply x <> &0)) /\\    (interpsign set ply Unknown <=> (forall x. set x ==> ply x = ply x))"
#eval thm' "Defs.interp_sing" SessionRQE.Defs.«interp_sing»
  "|- interpsign set p s <=> interpsigns [p] set [s]"
#eval thm' "Defs.interpmat" SessionRQE.Defs.«interpmat»
  "|- forall polyl ptl signll.        interpmat ptl polyl signll <=>        real_ordered_list ptl /\\        ALL2 (interpsigns polyl) (partition_line ptl) signll"

-- TestformThms
#eval thm' "TestformThms.t_thm" SessionRQE.TestformThms.«t_thm»
  "|- forall set x. set x ==> true"
#eval thm' "TestformThms.f_thm" SessionRQE.TestformThms.«f_thm»
  "|- forall set. ~(exists x. set x /\\ false)"

-- CondenseThms
#eval thm' "CondenseThms.real_cases" SessionRQE.CondenseThms.«real_cases»
  "|- forall x y. x < y \\/ x = y \\/ y < x"
#eval thm' "CondenseThms.gt_aux" SessionRQE.CondenseThms.«gt_aux»
  "|- forall x.        (x1 < x2 /\\ x2 < x3) /\\        (x1 < x /\\ x < x2 \\/ x = x2 \\/ x2 < x /\\ x < x3)        ==> x1 < x /\\ x < x3"
#eval thm' "CondenseThms.gen_thm_noleft" SessionRQE.CondenseThms.«gen_thm_noleft»
  "|- forall P x2 x3.        x2 < x3        ==> (forall x. x < x2 ==> P x)        ==> (forall x. x = x2 ==> P x)        ==> (forall x. x2 < x /\\ x < x3 ==> P x)        ==> (forall x. x < x3 ==> P x)"
#eval thm' "CondenseThms.gen_thm_noright" SessionRQE.CondenseThms.«gen_thm_noright»
  "|- forall P x1 x2.        x1 < x2        ==> (forall x. x1 < x /\\ x < x2 ==> P x)        ==> (forall x. x = x2 ==> P x)        ==> (forall x. x2 < x ==> P x)        ==> (forall x. x1 < x ==> P x)"

-- InferisignThms
#eval thm' "InferisignThms.inferisign_lem00" SessionRQE.InferisignThms.«inferisign_lem00»
  "|- x1 < x3    ==> x3 < x2    ==> (forall x. x1 < x /\\ x < x2 ==> P x)    ==> (forall x. x1 < x /\\ x < x3 ==> P x) /\\        (forall x. x = x3 ==> P x) /\\        (forall x. x3 < x /\\ x < x2 ==> P x)"
#eval thm' "InferisignThms.pos_pos_neq_thm2" SessionRQE.InferisignThms.«pos_pos_neq_thm2»
  "|- forall x y p.        x < y        ==> poly p x > &0        ==> poly p y > &0        ==> (forall z. x < z /\\ z < y ==> ~(poly (poly_diff p) z = &0))        ==> (forall z. x < z /\\ z < y ==> poly p z > &0)"
#eval thm' "InferisignThms.neg_pos_neq_thm2" SessionRQE.InferisignThms.«neg_pos_neq_thm2»
  "|- forall x y p.        x < y        ==> poly p x < &0        ==> poly p y > &0        ==> (forall z. x < z /\\ z < y ==> ~(poly (poly_diff p) z = &0))        ==> (exists X.                 x < X /\\                 X < y /\\                 (forall z. z = X ==> poly p z = &0) /\\                 (forall z. x < z /\\ z < X ==> poly p z < &0) /\\                 (forall z. X < z /\\ z < y ==> poly p z > &0))"
#eval thm' "InferisignThms.neg_zero_neg_thm" SessionRQE.InferisignThms.«neg_zero_neg_thm»
  "|- forall x y p.        x < y        ==> poly p x < &0        ==> poly p y = &0        ==> (forall z. x < z /\\ z < y ==> ~(poly (poly_diff p) z = &0))        ==> (forall z. x < z /\\ z < y ==> poly p z < &0)"

-- MatinsertThms

-- SignsThms
#eval thm' "SignsThms.pth_0g" SessionRQE.SignsThms.«pth_0g»
  "|- p = &0 ==> c > &0 ==> c * p = &0"
#eval thm' "SignsThms.pth_ll" SessionRQE.SignsThms.«pth_ll»
  "|- p < &0 ==> c < &0 ==> c * p > &0"
#eval thm' "SignsThms.signs_lem04" SessionRQE.SignsThms.«signs_lem04»
  "|- c > &0 ==> p > &0 ==> c * p = p' ==> p' > &0"
#eval thm' "SignsThms.signs_lem002" SessionRQE.SignsThms.«signs_lem002»
  "|- forall p. p = &0 \\/ p <> &0"

-- InferpsignThms
#eval thm' "InferpsignThms.EVEN_DIV_LEM" SessionRQE.InferpsignThms.«EVEN_DIV_LEM»
  "|- forall set p q c d a n.        (forall x. a pow n * p x = c x * q x + d x)        ==> a <> &0        ==> EVEN n        ==> (interpsign set q Zero             ==> interpsign set d Neg             ==> interpsign set p Neg) /\\            (interpsign set q Zero             ==> interpsign set d Pos             ==> interpsign set p Pos) /\\            (interpsign set q Zero             ==> interpsign set d Zero             ==> interpsign set p Zero)"
#eval thm' "InferpsignThms.GT_DIV_LEM" SessionRQE.InferpsignThms.«GT_DIV_LEM»
  "|- forall set p q c d a n.        (forall x. a pow n * p x = c x * q x + d x)        ==> a > &0        ==> (interpsign set q Zero             ==> interpsign set d Neg             ==> interpsign set p Neg) /\\            (interpsign set q Zero             ==> interpsign set d Pos             ==> interpsign set p Pos) /\\            (interpsign set q Zero             ==> interpsign set d Zero             ==> interpsign set p Zero)"
#eval thm' "InferpsignThms.NEQ_ODD_LEM" SessionRQE.InferpsignThms.«NEQ_ODD_LEM»
  "|- forall set p q c d a n.        (forall x. a pow n * p x = c x * q x + d x)        ==> a <> &0        ==> ODD n        ==> (interpsign set q Zero             ==> interpsign set (\\x. a * d x) Neg             ==> interpsign set p Neg) /\\            (interpsign set q Zero             ==> interpsign set (\\x. a * d x) Pos             ==> interpsign set p Pos) /\\            (interpsign set q Zero             ==> interpsign set (\\x. a * d x) Zero             ==> interpsign set p Zero)"
#eval thm' "InferpsignThms.ips_gt_nz_thm" SessionRQE.InferpsignThms.«ips_gt_nz_thm»
  "|- forall x. x > &0 ==> x <> &0"

-- DedmatrixThms
#eval thm' "DedmatrixThms.le_lem" SessionRQE.DedmatrixThms.«le_lem»
  "|- (forall y. y <= Y ==> P y)    ==> (forall y. y < Y ==> P y) /\\ (forall y. y = Y ==> P y)"
#eval thm' "DedmatrixThms.gt_int_lem" SessionRQE.DedmatrixThms.«gt_int_lem»
  "|- (forall y. Y < y ==> P y) ==> Y < X ==> (forall y. Y < y /\\ y < X ==> P y)"
#eval thm' "DedmatrixThms.rest_eq_lt_lem" SessionRQE.DedmatrixThms.«rest_eq_lt_lem»
  "|- Y < X ==> (forall x. x < X ==> P x) ==> (forall x. x = Y ==> P x)"
#eval thm' "DedmatrixThms.rest_int_gt_lem" SessionRQE.DedmatrixThms.«rest_int_gt_lem»
  "|- X < Y ==> (forall x. X < x ==> P x) ==> (forall x. X < x /\\ x < Y ==> P x)"

-- PdividesThms

-- MainThms
#eval thm' "MainThms.empty_mat" SessionRQE.MainThms.«empty_mat»
  "|- interpmat [] [] [[]]"
#eval thm' "MainThms.ltneg" SessionRQE.MainThms.«ltneg»
  "|- forall s c mp p.        (forall x. c * p x = mp x)        ==> c < &0        ==> interpsign s mp Neg        ==> interpsign s p Pos"
#eval thm' "MainThms.factor_pos_neg" SessionRQE.MainThms.«factor_pos_neg»
  "|- interpsign s (\\x. &0 + x * &1) Pos    ==> interpsign s p Neg    ==> (forall x. x pow k * p x = q x)    ==> interpsign s q Neg"
#eval thm' "MainThms.factor_neg_even_pos" SessionRQE.MainThms.«factor_neg_even_pos»
  "|- interpsign s (\\x. &0 + x * &1) Neg    ==> interpsign s p Pos    ==> EVEN k    ==> ~(k = 0)    ==> (forall x. x pow k * p x = q x)    ==> interpsign s q Pos"

-- WorkThms
#eval thm' "WorkThms.INTERPSIGNS_CONJ" SessionRQE.WorkThms.«INTERPSIGNS_CONJ»
  "|- forall P Q eqs l.        interpsigns eqs (\\x. P x) l /\\ interpsigns eqs (\\x. Q x) l        ==> interpsigns eqs (\\x. P x \\/ Q x) l"
#eval thm' "WorkThms.INFERISIGN_POS_POS_POS" SessionRQE.WorkThms.«INFERISIGN_POS_POS_POS»
  "|- forall y z p pts qts eqs sgns rgns r1 r2 r3.        interpmat (APPEND pts (CONS y (CONS z qts)))        (CONS (\\x. poly p x) (CONS (\\x. poly (poly_diff p) x) eqs))        (APPEND sgns        (CONS (CONS Pos r1)        (CONS (CONS Unknown (CONS Pos r2)) (CONS (CONS Pos r3) rgns))))        ==> LENGTH sgns = 2 * LENGTH pts + 1        ==> interpmat (APPEND pts (CONS y (CONS z qts)))            (CONS (\\x. poly p x) (CONS (\\x. poly (poly_diff p) x) eqs))            (APPEND sgns            (CONS (CONS Pos r1)            (CONS (CONS Pos (CONS Pos r2)) (CONS (CONS Pos r3) rgns))))"
#eval thm' "WorkThms.INFIN_POS_POS" SessionRQE.WorkThms.«INFIN_POS_POS»
  "|- forall pts p ps r1 sgns r2.        interpmat pts        (CONS (\\x. poly p x) (CONS (\\x. poly (poly_diff p) x) ps))        (APPEND (CONS (CONS Unknown (CONS Pos r1)) sgns)        [a; b; CONS Unknown (CONS Pos r2)])        ==> nonconstant p        ==> (exists xminf xinf.                 interpmat (APPEND (CONS xminf pts) [xinf])                 (CONS (\\x. poly p x) (CONS (\\x. poly (poly_diff p) x) ps))                 (APPEND                  (CONS (CONS Neg (CONS Pos r1))                  (CONS (CONS Neg (CONS Pos r1))                  (CONS (CONS Unknown (CONS Pos r1)) sgns)))                 [a; b; CONS Unknown (CONS Pos r2); CONS Pos (CONS Pos r2);                  CONS Pos (CONS Pos r2)]))"
#eval thm' "WorkThms.ALL2_UNKNOWN" SessionRQE.WorkThms.«ALL2_UNKNOWN»
  "|- forall p pts.        ALL2 (\\x y. interpsign x p y) (partition_line pts)        (REPLICATE (LENGTH (partition_line pts)) Unknown)"

-- REAL_QELIM_CONV (rqe_main.ml)
#eval qe "!x. --(&1) <= x /\\ x <= &1 ==> -- (&1) <= &2 * x pow 2 - &1 /\\ &2 * x pow 2 - &1 <= &1"
  "|- (forall x.         -- &1 <= x /\\ x <= &1         ==> -- &1 <= &2 * x pow 2 - &1 /\\ &2 * x pow 2 - &1 <= &1) <=>    true"
#eval qe "?x. x pow 4 + x pow 2 + &1 = &0"
  "|- (exists x. x pow 4 + x pow 2 + &1 = &0) <=> false"
#eval qe "?x. x pow 3 - x pow 2 + x - &1 = &0"
  "|- (exists x. x pow 3 - x pow 2 + x - &1 = &0) <=> true"
#eval qe "?x. x * x = &2"
  "|- (exists x. x * x = &2) <=> true"
#eval qe "!x. x * x >= &0"
  "|- (forall x. x * x >= &0) <=> true"
#eval qe "!a b. ?x. a * x = b"
  "|- (forall a b. exists x'. a * x' = b) <=> false"
#eval qe "?x. x pow 2 = &0 /\\ ~(x = &0)"
  "|- (exists x. x pow 2 = &0 /\\ ~(x = &0)) <=> false"
#eval qe "?x y. x * y = &1 /\\ x + y = &0"
  "|- (exists x y. x * y = &1 /\\ x + y = &0) <=> false"

end T
