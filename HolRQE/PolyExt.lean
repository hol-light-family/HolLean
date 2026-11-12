/- ========================================================================= -/
/- Rqe: canonical polynomials, their arithmetic, derivatives and pseudo-di -/
/- ========================================================================= -/
/- File: HolRQE/PolyExt.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/poly_ext.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/timers.ml, Rqe/num_calc_simp.ml, Rqe/asym.ml, Rqe/rol.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.PolyExt fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, INT_ARITH, TAUT, SET_RULE, ...) they are
  bound first, in OCaml's order.
-/

import HolLibrary.Analysis
import HolLibrary.Poly
import HolRQE.RqeLib
import HolRQE.RqeTacticsExt
import HolRQE.Util
import HolRQE.Rewrites
import HolRQE.Basic
import HolRQE.RqeNum
import HolRQE.RqeReal
import HolRQE.ListRewrites
import HolRQE.RqeList
import HolRQE.Timers
import HolRQE.NumCalcSimp
import HolRQE.Asym
import HolRQE.Rol

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolRQE.RqeLib
open HolRQE.RqeTacticsExt
open HolRQE.Util
open HolRQE.Rewrites
open HolRQE.Basic
open HolRQE.RqeNum
open HolRQE.RqeReal
open HolRQE.ListRewrites
open HolRQE.RqeList
open HolRQE.Timers
open HolRQE.NumCalcSimp
open HolRQE.Asym
open HolRQE.Rol

namespace HolRQE.PolyExt

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (DIFF_ADD DIFF_CMUL DIFF_CONST DIFF_POW HD NOT_CONS_NIL POW_1 REAL_ADD_LID
   REAL_LDISTRIB REAL_MUL_ASSOC REAL_MUL_LID REAL_MUL_RZERO REAL_MUL_SYM
   SUC_SUB1 SWAP_FORALL_THM TL lem poly poly_diff poly_diff_aux pow real_div
   real_ge real_gt real_pow real_sub : thm)
  deriving Inhabited

/-- What poly_ext.ml uses from Session besides theorems. -/
structure PolyExtDeps where
  new_definition : String → ExceptT String IO thm
  define : String → ExceptT String IO thm
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  new_recursive_definition : thm → String → ExceptT String IO thm
  LIST_INDUCT_TAC : tactic
  ASM_ARITH_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  METIS_TAC : List thm → tactic
  ASM_METIS_TAC : List thm → tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  TAUT : term → ExceptT String IO thm
  ITAUT : term → ExceptT String IO thm
  REAL_ARITH : term → ExceptT String IO thm
  REAL_FIELD : term → ExceptT String IO thm
  REAL_ARITH_TAC : tactic
  ASM_REAL_ARITH_TAC : tactic
  INDUCT_TAC : tactic
  INT_ARITH : term → ExceptT String IO thm
  INT_ARITH_TAC : tactic
  ASM_INT_ARITH_TAC : tactic
  INTEGER_RULE : term → ExceptT String IO thm  -- ints.ml's INTEGER_RULE
  INTEGER_TAC : tactic
  NUMBER_RULE : ioconv  -- ints.ml's NUMBER_RULE
  NUM_REDUCE_CONV : ioconv
  INT_REDUCE_CONV : ioconv
  INT_RED_CONV : ioconv
  INT_REM_DOWN_CONV : ioconv
  HAS_SIZE_CONV : ioconv  -- card.ml's HAS_SIZE_CONV
  let_CONV : ioconv
  num_CONV : ioconv
  mk_numeral : Rat → Except String term
  LET_TAC : tactic
  basic_ss : List thm → IO (Except String HolCore.Simp.simpset)
  NUM_SUB_CONV : ioconv
  REAL_RAT_REDUCE_CONV : ioconv
  NUM_EQ_CONV : ioconv
  NUM_DIV_CONV : ioconv
  EXP_MOD_CONV : ioconv
  EXPAND_CASES_CONV : ioconv
  REAL_RAT_NEG_CONV : ioconv
  REAL_RAT_GT_CONV : ioconv
  REAL_RAT_LT_CONV : ioconv
  REAL_RAT_MUL_CONV : ioconv
  REAL_RAT_EQ_CONV : ioconv
  ETA_CONV : ioconv
  mk_small_numeral : Int → Except String term
  term_of_rat : Rat → Except String term
  NUM_SUC_CONV : ioconv
  labels_flag : Option (IO.Ref Bool)
  prove_by_refinement : term × List tactic → ExceptT String IO thm
  exclude_list : Option (IO.Ref (List String))
  get_var_list : term → IO (List (String × hol_type))
  auto_type : term → term → IO term
  auto_type_list : term → List term → IO term
  auto_type_goal : term → HolCore.Tactics.goal → IO term
  TYPE_TAC : (term → tactic) → term → tactic
  TYPE_TACL : (List term → tactic) → List term → tactic
  CLAIM : term → tactic
  MATCH_EQ_MP : thm → thm → ExceptT String IO thm
  DISJ_LCASE : tactic
  DISJ_RCASE : tactic
  CASES_ON : term → tactic
  EXISTS_TAC : term → tactic
  MATCH_EQ_MPL : List thm → ExceptT String IO thm
  CCONTR_TAC : tactic
  pgoal : Unit → IO HolCore.Tactics.goalstack
  suppress : Option (IO.Ref (List String))
  get_type_list : term → IO (List (String × hol_type))
  set_types : term → IO (List (String × hol_type))
  print_term_types : term → IO Unit
  print_thm_types : thm → IO Unit
  goal_types : Unit → IO Unit
  assum : Int → ExceptT String IO term
  assum_types : Int → ExceptT String IO Unit
  get_type : String → thm → ExceptT String IO hol_type
  proof_stack : Option (IO.Ref (List HolCore.Tactics.goalstack))
  push_proof : term → IO HolCore.Tactics.goalstack
  pop_proof : Unit → ExceptT String IO HolCore.Tactics.goalstack
  NUM_REWRITES : Option (IO.Ref (List thm))
  NUM_SIMP_TAC : tactic
  extend_num_rewrites : List thm → IO Unit
  REAL_REWRITES : Option (IO.Ref (List thm))
  REAL_ELIM : Option (IO.Ref (List thm))
  REAL_SIMP_TAC : tactic
  REAL_SOLVE_TAC : tactic
  extend_real_rewrites : List thm → IO Unit
  BASIC_REWRITES : Option (IO.Ref (List thm))
  dest_beq : term → Except String (term × term)
  t_tm : term
  f_tm : term
  nqt : term
  mk_neq : term × term → Except String term
  neq : term
  nlt : term
  ngt : term
  nle : term
  nge : term
  nm : term
  np : term
  nzero : term
  even_tm : term
  odd_tm : term
  PARITY_CONV : term → ExceptT String IO thm
  real_ty : hol_type
  rx : term
  ry : term
  rz : term
  req : term
  rneq : term
  rlt : term
  rgt : term
  rle : term
  rge : term
  rm : term
  rs : term
  rn : term
  rd : term
  rp : term
  rzero : term
  rone : term
  rlast : term
  rappend : term
  mk_rlist : List term → IO (Except String term)
  diffl_tm : term
  dest_diffl : term → Except String (term × term)
  dest_mult : term → Except String (term × term)
  mk_mult : term → Except String (term → Except String term)
  pow_tm : term
  dest_pow : term → Except String (term × term)
  mk_plus : term → Except String (term → Except String term)
  mk_negative : term → Except String term
  dest_plus : term → Except String (term × term)
  LIST_REWRITES : Option (IO.Ref (List thm))
  LIST_SIMP_TAC : tactic
  extend_list_rewrites : List thm → IO Unit
  aacons_tm : term
  HD_CONV : ioconv → ioconv
  TL_CONV : ioconv → ioconv
  EL_CONV : ioconv → Int → ioconv
  testform_timer : Option (IO.Ref Float)
  combine_testforms_timer : Option (IO.Ref Float)
  condense_timer : Option (IO.Ref Float)
  inferisign_timer : Option (IO.Ref Float)
  matinsert_timer : Option (IO.Ref Float)
  inferpsign_timer : Option (IO.Ref Float)
  remove_column1_timer : Option (IO.Ref Float)
  add_infinities_timer : Option (IO.Ref Float)
  remove_infinities_timer : Option (IO.Ref Float)
  pdivides_timer : Option (IO.Ref Float)
  duplicate_columns_timer : Option (IO.Ref Float)
  unmonicize_mat_timer : Option (IO.Ref Float)
  swap_head_col_timer : Option (IO.Ref Float)
  replace_pol_timer : Option (IO.Ref Float)
  unfactor_mat_timer : Option (IO.Ref Float)
  reset_timers : Unit → IO Unit
  print_timers : Unit → IO Unit
  arith_ss : List thm → ExceptT String IO HolCore.Simp.simpset
  ARITH_SIMP_CONV : List thm → ioconv
  arith_net : Unit → ExceptT String IO (HolCore.Nets.net HolCore.Simp.gconv)
  ARITH_REWRITE_CONV : List thm → ioconv
  ARITH_SIMP_TAC : List thm → tactic
  CHOP_REAL_LIST : Int → term → ExceptT String IO thm
  ROL_CHOP_LT : Int → thm → ExceptT String IO thm
  ROL_CHOP_LIST : Int → thm → ExceptT String IO (thm × thm × thm)
  ROL_INSERT_MIDDLE : thm → thm → ExceptT String IO thm
  ROL_INSERT_FRONT : thm → thm → ExceptT String IO thm
  ROL_INSERT_BACK : thm → thm → ExceptT String IO thm
  ROL_INSERT : thm → thm → ExceptT String IO thm
  rol_thms : thm → ExceptT String IO (List thm)
  rol_nonempty_thms : thm → ExceptT String IO (List thm)
  mk_rol : List thm → ExceptT String IO thm
  real_nil : term
  ROL_REMOVE : term → thm → ExceptT String IO thm
  ROL_COVERS : thm → ExceptT String IO thm
  core1 : CoreThms1

/-- RingTheory's `wPart` (copied verbatim).  `W(MP_TAC o PART_MATCH f th o g
    o snd)`: match `th`'s part `f` against the part `g` of the goal, and
    MP_TAC the instance. -/
def wPart [HolBase] (g : term → Except String term) (f : term → Except String term)
    (th : thm) : tactic := fun gl =>
  ExceptT.run do
    let t ← liftExcept (g gl.2)
    ExceptT.mk (MP_TAC (← PART_MATCH f th t) gl)

/-- tactics.ml's NO_TAC. -/
def NO_TAC : tactic := HolCore.Tactics.NO_TAC

/- The recursive conversions and functions of poly_ext.ml (OCaml's local
   `let rec`s, and its top-level recursive functions over the polynomial
   syntax) are top-level `partial def`s here, taking the theorems,
   conversions and terms they close over; the bundle below builds those at
   load, as OCaml does, and binds the functions over them. -/

section
variable [HolBase]

/-- POLY_ENLIST_CONV's local `conv`. -/
partial def POLY_ENLIST_CONV.conv (polyvar : term → Except String term) (x zero_tm : term)
    (cnv_0 cnv_1 cnv_2 : ioconv) : ioconv := fun tm => ExceptT.run do
  if (← liftExcept (polyvar tm)) == x then
    ExceptT.mk ((RAND_CONV (RAND_CONV (POLY_ENLIST_CONV.conv polyvar x zero_tm cnv_0 cnv_1 cnv_2))
      THENC cnv_2) tm)
  else if tm == zero_tm then ExceptT.mk (cnv_0 tm)
  else ExceptT.mk (cnv_1 tm)

/-- POLY_DELIST_CONV's local `conv`. -/
partial def POLY_DELIST_CONV.conv (cnv_0 cnv_1 cnv_2 : ioconv) : ioconv := fun tm =>
  (cnv_0 ORELSEC cnv_1 ORELSEC
    (cnv_2 THENC RAND_CONV (RAND_CONV (POLY_DELIST_CONV.conv cnv_0 cnv_1 cnv_2)))) tm

/-- CANON_POLY_DIFF_CONV's local `POLY_DIFF_AUX_CONV`. -/
partial def CANON_POLY_DIFF_CONV.POLY_DIFF_AUX_CONV (aux_conv0 aux_conv1 NUM_SUC_CONV : ioconv) :
    ioconv := fun tm =>
  (aux_conv0 ORELSEC
   (aux_conv1 THENC
    RAND_CONV (LAND_CONV NUM_SUC_CONV THENC
      CANON_POLY_DIFF_CONV.POLY_DIFF_AUX_CONV aux_conv0 aux_conv1 NUM_SUC_CONV))) tm

end

/-- Whether the first of two items comes earlier in the list. -/
def earlier {α : Type} [BEq α] : List α → α → α → Bool
  | h :: t, x, y => if h == y then false else if h == x then true else earlier t x y
  | [], _, _ => false

section
variable [HolBase]

/-- POLY_ADD_CONV's local `POLY_ADD_CONV`. -/
partial def POLY_ADD_CONV.go (polyvar : term → Except String term)
    (dest_add : term → Except String (term × term)) (cnv_r cnv_l cnv_2 cnv_0 REAL_RAT_REDUCE_CONV : ioconv)
    (vars : List term) : ioconv := fun tm => ExceptT.run do
  let rec_ := POLY_ADD_CONV.go polyvar dest_add cnv_r cnv_l cnv_2 cnv_0 REAL_RAT_REDUCE_CONV vars
  let (pol1, pol2) ← liftExcept (dest_add tm)
  -- `let x = .. and y = ..`
  let x ← liftExcept (polyvar pol1)
  let y ← liftExcept (polyvar pol2)
  if !(is_var x) && !(is_var y) then ExceptT.mk (REAL_RAT_REDUCE_CONV tm) else
  if !(is_var y) || earlier vars x y then
    ExceptT.mk ((cnv_l THENC LAND_CONV rec_) tm)
  else if !(is_var x) || earlier vars y x then
    ExceptT.mk ((cnv_r THENC LAND_CONV rec_) tm)
  else
    ExceptT.mk ((cnv_2 THENC COMB_CONV (RAND_CONV rec_) THENC
     TRY_CONV cnv_0) tm)

/-- POLY_NEG_CONV's local `POLY_NEG_CONV`. -/
partial def POLY_NEG_CONV.go (cnv REAL_RAT_NEG_CONV : ioconv) : ioconv := fun tm => ExceptT.run do
  if HolMath.CalcInt.is_ratconst (← liftExcept (rand tm)) then ExceptT.mk (REAL_RAT_NEG_CONV tm) else
  ExceptT.mk ((cnv THENC COMB_CONV (RAND_CONV (POLY_NEG_CONV.go cnv REAL_RAT_NEG_CONV))) tm)

/-- POLY_MUL_CONV's local `POLY_MUL_CONV`. -/
partial def POLY_MUL_CONV.go (polyvar : term → Except String term)
    (dest_mul : term → Except String (term × term)) (zero_tm : term)
    (cnv_l1 cnv_r1 cnv_2 cnv_l0 cnv_r0 REAL_RAT_MUL_CONV : ioconv)
    (POLY_ADD_CONV : List term → ioconv) (vars : List term) : ioconv := fun tm => ExceptT.run do
  let rec_ := POLY_MUL_CONV.go polyvar dest_mul zero_tm cnv_l1 cnv_r1 cnv_2 cnv_l0 cnv_r0
    REAL_RAT_MUL_CONV POLY_ADD_CONV vars
  let (pol1, pol2) ← liftExcept (dest_mul tm)
  if pol1 == zero_tm then ExceptT.mk (cnv_l0 tm)
  else if pol2 == zero_tm then ExceptT.mk (cnv_r0 tm)
  else if HolMath.CalcInt.is_ratconst pol1 && HolMath.CalcInt.is_ratconst pol2 then
    ExceptT.mk (REAL_RAT_MUL_CONV tm) else
  let x ← liftExcept (polyvar pol1)
  let y ← liftExcept (polyvar pol2)
  if !(is_var y) || earlier vars x y then
    ExceptT.mk ((cnv_r1 THENC COMB_CONV (RAND_CONV rec_)) tm)
  else if !(is_var x) || earlier vars y x then
    ExceptT.mk ((cnv_l1 THENC COMB_CONV (RAND_CONV rec_)) tm)
  else
    ExceptT.mk ((cnv_2 THENC COMB2_CONV (RAND_CONV rec_)
                            (RAND_CONV (RAND_CONV rec_)) THENC
     POLY_ADD_CONV vars) tm)

/-- POLY_POW_CONV's local `POLY_POW_CONV`. -/
partial def POLY_POW_CONV.go (zero_tm : term) (cnv_0 cnv_1 num_CONV : ioconv)
    (POLY_MUL_CONV : List term → ioconv) (vars : List term) : ioconv := fun tm => ExceptT.run do
  if (← liftExcept (rand tm)) == zero_tm then ExceptT.mk (cnv_0 tm) else
  ExceptT.mk ((RAND_CONV num_CONV THENC cnv_1 THENC
   RAND_CONV (POLY_POW_CONV.go zero_tm cnv_0 cnv_1 num_CONV POLY_MUL_CONV vars) THENC
   POLY_MUL_CONV vars) tm)

/-- POLYNATE_CONV's local `POLYNATE_CONV`. -/
partial def POLYNATE_CONV.go (cnv_var cnv_div : ioconv) (neg_tm add_tm sub_tm mul_tm pow_tm div_tm : term)
    (POLY_NEG_CONV REAL_RAT_REDUCE_CONV : ioconv)
    (POLY_ADD_CONV POLY_SUB_CONV POLY_MUL_CONV POLY_POW_CONV : List term → ioconv)
    (vars : List term) : ioconv := fun tm => ExceptT.run do
  let rec_ := POLYNATE_CONV.go cnv_var cnv_div neg_tm add_tm sub_tm mul_tm pow_tm div_tm
    POLY_NEG_CONV REAL_RAT_REDUCE_CONV POLY_ADD_CONV POLY_SUB_CONV POLY_MUL_CONV POLY_POW_CONV vars
  if is_var tm then ExceptT.mk (cnv_var tm)
  else if HolMath.CalcInt.is_ratconst tm then pure (REFL tm) else
  let (lop, _r) ← liftExcept (dest_comb tm)
  if lop == neg_tm
  then ExceptT.mk ((RAND_CONV rec_ THENC POLY_NEG_CONV) tm) else
  let (op, _l) ← liftExcept (dest_comb lop)
  if op == pow_tm then
    ExceptT.mk ((LAND_CONV rec_ THENC POLY_POW_CONV vars) tm)
  else if op == div_tm then
    ExceptT.mk ((cnv_div THENC
     COMB2_CONV (RAND_CONV rec_) REAL_RAT_REDUCE_CONV THENC
     POLY_MUL_CONV vars) tm) else
  let cnv ← if op == add_tm then pure POLY_ADD_CONV
            else if op == sub_tm then pure POLY_SUB_CONV
            else if op == mul_tm then pure POLY_MUL_CONV
            else throw "POLYNATE_CONV: unknown operation"
  ExceptT.mk ((BINOP_CONV rec_ THENC cnv vars) tm)

end

/-- poly_ext.ml's `degree_`, given `polyvar`. -/
partial def degree_.go (polyvar : term → Except String term) (vars : List term) (tm : term) :
    Except String Int := do
  if (← polyvar tm) == (← hd vars) then
    return 1 + (← degree_.go polyvar vars (← rand (← rand tm)))
  else return 0

/-- poly_ext.ml's `coefficients`, given `polyvar`. -/
partial def coefficients.go (polyvar : term → Except String term) (vars : List term) (tm : term) :
    Except String (List term) := do
  if (← polyvar tm) == (← hd vars) then
    -- `(lhand tm)::coefficients ..`, right to left
    let rest ← coefficients.go polyvar vars (← rand (← rand tm))
    return (← lhand tm) :: rest
  else return [tm]

/-- poly_ext.ml's `behead`, given rqe_real.ml's syntax functions. -/
partial def behead.go (dest_plus dest_mult : term → Except String (term × term))
    (mk_plus mk_mult : term → Except String (term → Except String term)) (rzero : term)
    (vars : List term) (tm : term) : Except String term :=
  match (do
      let (c, r) ← dest_plus tm
      let (x, p) ← dest_mult r
      if !(x == (← hd vars)) then throw "" else
      let p' ← behead.go dest_plus dest_mult mk_plus mk_mult rzero vars p
      if p' == rzero then pure c
      else (← mk_plus c) (← (← mk_mult x) p') : Except String term) with
  | .ok v => .ok v
  | .error _ => .ok rzero

/-- poly_ext.ml's `headconst`. -/
partial def headconst (p : term) : Except String Rat :=
  match HolMath.CalcInt.rat_of_term p with
  | .ok v => .ok v
  | .error _ => do headconst (← rand (← rand p))

/-- weakfactor's local `weakfactor`, given rqe_real.ml's syntax functions. -/
partial def weakfactor.go (dest_plus dest_mult : term → Except String (term × term)) (rzero : term)
    (k : Int) (x pol : term) : Int × term :=
  match (do
      let (ls, rs) ← dest_plus pol
      if !(ls == rzero) then throw "" else
      let (lm, rm) ← dest_mult rs
      if !(lm == x) then throw "" else
      pure (weakfactor.go dest_plus dest_mult rzero (k + 1) x rm) : Except String (Int × term)) with
  | .ok v => v
  | .error _ => (k, pol)

/-- PDIVIDE's local `pdivide_aux`, given its `mk_varpow`, `zero_tm` and the
    polynomial functions of the bundle. -/
partial def PDIVIDE.pdivide_aux (zero_tm : term)
    (mk_varpow : List term → Int → Except String term)
    (head : List term → term → Except String term)
    (degree_ : List term → term → Except String Int)
    (poly_add_ poly_sub_ poly_mul_ : List term → term → term → ExceptT String IO term)
    (poly_pow_ : List term → term → Int → ExceptT String IO term)
    (vars : List term) (a : term) (n : Int) (p s : term) : ExceptT String IO (Int × term × term) := do
  let go := PDIVIDE.pdivide_aux zero_tm mk_varpow head degree_ poly_add_ poly_sub_ poly_mul_ poly_pow_ vars a n p
  if s == zero_tm then return (0, zero_tm, s) else
  -- `let b = .. and m = ..`
  let b ← liftExcept (head vars s)
  let m ← liftExcept (degree_ vars s)
  if m < n then return (0, zero_tm, s) else
  let xp ← liftExcept (mk_varpow vars (m - n))
  let p' ← poly_mul_ vars xp p
  if a == b then
    let (k, q, r) ← go (← poly_sub_ vars s p')
    -- the triple right to left
    let q' ← poly_add_ vars q (← poly_mul_ vars xp (← poly_pow_ vars a k))
    return (k, q', r)
  else
    let (k, q, r) ← go
      (← poly_sub_ vars (← poly_mul_ vars a s) (← poly_mul_ vars b p'))
    let q' ← poly_add_ vars q (← poly_mul_ vars b
              (← poly_mul_ vars (← poly_pow_ vars a k) xp))
    return (k + 1, q', r)



/- ---------------------------------------------------------------------- -/
/-  Canonical polynomials (poly_ext.ml 1-772)                             -/
/- ---------------------------------------------------------------------- -/

structure PolyExtFns where
  -- @@FIELDS
  poly_tm : term
  dest_poly : term → Except String (term × term)
  is_poly : term → ExceptT String IO Bool
  polyvar : term → Except String term
  is_constant : List term → term → Except String Bool
  POLY : thm
  POLY_ENLIST_CONV : List term → ExceptT String IO ioconv
  POLY_DELIST_CONV : ioconv
  POLY_DIFF_CLAUSES : thm
  POLY_DIFF_LEMMA : thm
  POLY_DIFF : thm
  CANON_POLY_DIFF_CONV : ioconv
  POLY_ADD_CONV : List term → ioconv
  POLY_NEG_CONV : ioconv
  POLY_SUB_CONV : List term → ioconv
  POLY_MUL_CONV : List term → ioconv
  POLY_POW_CONV : List term → ioconv
  POLYNATE_CONV : List term → ioconv
  poly_add_ : List term → term → term → ExceptT String IO term
  poly_sub_ : List term → term → term → ExceptT String IO term
  poly_mul_ : List term → term → term → ExceptT String IO term
  poly_neg_ : term → ExceptT String IO term
  poly_pow_ : List term → term → Int → ExceptT String IO term
  degree_ : List term → term → Except String Int
  coefficients : List term → term → Except String (List term)
  head : List term → term → Except String term
  behead : List term → term → Except String term
  BEHEAD3 : List term → thm → term → ExceptT String IO thm
  BEHEAD : List term → thm → term → ExceptT String IO thm
  is_const_poly : List term → term → Except String Bool
  MONIC_CONV : List term → ioconv
  PDIVIDE : List term → term → term → ExceptT String IO thm
  SIGN_CONST : term → ExceptT String IO thm
  POLY_DERIV_CONV : List term → term → ExceptT String IO thm
  lt_lem : thm
  le_lem : thm
  eq_lem : thm
  POLYATOM_CONV : List term → term → ExceptT String IO thm
  weakfactor : term → term → Int × term
  poly_var : term → Except String term
  POW_PROD_SUM : thm
  lem1 : thm
  lem2 : thm
  lem3 : thm
  SIMP_POW_CONV : term → ExceptT String IO thm
  WEAKFACTOR_CONV : term → term → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupPolyExtFns [HolBase] (D : PolyExtDeps) :
    ExceptT String IO PolyExtFns := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_SIMP_CONV, ETA_CONV, INDUCT_TAC, LIST_INDUCT_TAC,
        NUM_SIMP_TAC, NUM_SUC_CONV, REAL_ARITH, REAL_ARITH_TAC, REAL_RAT_EQ_CONV,
        REAL_RAT_GT_CONV, REAL_RAT_LT_CONV, REAL_RAT_MUL_CONV, REAL_RAT_NEG_CONV,
        REAL_RAT_REDUCE_CONV, REAL_SIMP_TAC, dest_mult, dest_plus, dest_pow, mk_mult,
        mk_plus, mk_small_numeral, num_CONV, prove_by_refinement, rm, rone, rp, rx,
        rzero, term_of_rat, .. } := D
  let { DIFF_ADD, DIFF_CMUL, DIFF_CONST, DIFF_POW, HD, NOT_CONS_NIL, POW_1,
        REAL_ADD_LID, REAL_LDISTRIB, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_RZERO,
        REAL_MUL_SYM, SUC_SUB1, SWAP_FORALL_THM, TL, poly, poly_diff, poly_diff_aux,
        pow, real_div, real_ge, real_gt, real_pow, real_sub, .. } := D.core1
  -- @@SCOPE END

  let poly_tm : term ← q r"poly"

  let dest_poly : term → Except String (term × term) ← pure (fun tm => do
    -- (OCaml's local `poly` is `poly0` here, so that it does not hide the
    -- theorem `poly` from the bundle's scope)
    let (poly0, args) ← HolCore.IndDefs.strip_ncomb 2 tm
    let (l, var) ← match args with
      | [l, var] => pure (l, var)
      | _ => throw "Match_failure"
    if !(poly0 == poly_tm) then throw "dest_poly: not a poly"
    else pure (l, var))

  -- the quotation is in the function body, so it is parsed on each call
  let is_poly : term → ExceptT String IO Bool ← pure (fun tm => do
    return (strip_comb tm).1 == (← q r"poly"))

  /- ------------------------------------------------------------------------- -/
  /- Get the lead variable in polynomial; &1 if a constant.                    -/
  /- ------------------------------------------------------------------------- -/

  let polyvar : term → Except String term ← do
    let dummy_tm ← q r"&1"
    pure (fun tm => if HolMath.CalcInt.is_ratconst tm then .ok dummy_tm else do lhand (← rand tm))


  /-
  let k00 = `&3 * x * y pow 2 + &2 * x pow 2 * y * z + z * x + &3 * y * z`
  let k0 = `(&0 + y * (&0 + z * &3)) + x * (((&0 + z * &1) + y * (&0 + y * &3)) +  x * (&0 + y * (&0 + z * &2)))`;;
  # polyvar k0;;
  val it : Term.term = `x`
  -/

  /- ---------------------------------------------------------------------- -/
  /-  Is a constant polynomial (wrt variable ordering)                      -/
  /- ---------------------------------------------------------------------- -/

  -- `assert` fails with OCaml's Assert_failure; the `try .. with _` catches
  -- every failure of its body
  let is_constant : List term → term → Except String Bool ← pure (fun vars p => do
    if vars == [] then throw "Assert_failure" else
    match (do
        let (_l, r) ← dest_plus p
        let (x, _r2) ← dest_mult r
        pure (if x == (← hd vars) then false else true) : Except String Bool) with
    | .ok v => pure v
    | .error _ => pure (if p == (← hd vars) then false else true))

  /- ------------------------------------------------------------------------- -/
  /- We only use this as a handy way to do derivatives.                        -/
  /- ------------------------------------------------------------------------- -/

  let POLY ← prove
   r"(poly [] x = &0) /\
     (poly [__c__] x = __c__) /\
     (poly (CONS __h__ __t__) x = __h__ + x * poly __t__ x)"
     (REWRITE_TAC [poly] THEN REAL_ARITH_TAC)

  /- ------------------------------------------------------------------------- -/
  /- Convert in and out of list representations.                              -/
  /- ------------------------------------------------------------------------- -/

  /- THIS IS BAD CODE!!!  It depends on the names of the variables in POLY -/
  let POLY_ENLIST_CONV : List term → ExceptT String IO ioconv ← pure (fun vars => do
    let lem ← GEN rx POLY
    let (cnv_0, cnv_1, cnv_2) ← do
      let cs ← (CONJUNCTS (← ISPEC (← liftExcept (hd vars)) lem)).mapM
        (fun th => do GEN_REWRITE_CONV_NET id [← GSYM th])
      match cs with
      | [cnv_0, cnv_1, cnv_2] => pure (cnv_0, cnv_1, cnv_2)
      | _ => throw "Match_failure"
    let zero_tm := rzero
    pure (POLY_ENLIST_CONV.conv polyvar (← liftExcept (hd vars)) zero_tm cnv_0 cnv_1 cnv_2))


  /-
  map GSYM (CONJUNCTS (ISPEC (hd vars) lem))

  POLY_ENLIST_CONV vars p in

  let tm = `&0 + c * &1`



  POLY_ENLIST_CONV vars tm

  #trace conv
  POLY_ENLIST_CONV vars tm
  let vars = [ry;rx]
  let tm =  `&0 + y * (&0 + x * &1)`


  let k1 = rhs(concl (POLY_ENLIST_CONV [`x:real`;`y:real`;`z:real`] k0));;
  POLY_ENLIST_CONV [`x:real`;`y:real`;`z:real`] k0;;
  val it : Hol.thm =
    |- k0 =
       poly [&0 + y * (&0 + z * &3);
             &0 * z * &1 + y * (&0 + y * &3);
             &0 + y * (&0 + z * &2)] x
  -/

  let POLY_DELIST_CONV : ioconv ← do
    let (cnv_0, cnv_1, cnv_2) ← do
      let cs ← (CONJUNCTS POLY).mapM (fun th => GEN_REWRITE_CONV_NET id [th])
      match cs with
      | [cnv_0, cnv_1, cnv_2] => pure (cnv_0, cnv_1, cnv_2)
      | _ => throw "Match_failure"
    pure (POLY_DELIST_CONV.conv cnv_0 cnv_1 cnv_2)

  /-
  # POLY_DELIST_CONV `poly [&5; &6; &7] x`;;
  val it : Hol.thm = |- poly [&5; &6; &7] x = &5 + x * (&6 + x * &7)
  -/

  /- ------------------------------------------------------------------------- -/
  /- Differentiation within list representation.                               -/
  /- ------------------------------------------------------------------------- -/

  /- let poly_diff_aux = new_recursive_definition list_RECURSION -/
  /-   `(poly_diff_aux n [] = []) /\ -/
  /-    (poly_diff_aux n (CONS h t) = CONS (&n * h) (poly_diff_aux (SUC n) t))`;; -/

  /- let poly_diff = new_definition -/
  /-   `poly_diff l = if l = [] then [] else poly_diff_aux 1 (TL l)`;; -/

  let POLY_DIFF_CLAUSES ← prove
   r"(poly_diff [] = []) /\
     (poly_diff [c] = []) /\
     (poly_diff (CONS h t) = poly_diff_aux 1 t)"
    (REWRITE_TAC [poly_diff, NOT_CONS_NIL, HD, TL, poly_diff_aux])

  let POLY_DIFF_LEMMA ← prove
   r"!l n x. ((\x. (x pow (SUC n)) * poly l x) diffl
                     ((x pow n) * poly (poly_diff_aux (SUC n) l) x))(x)"
  /- {{{ Proof -/

    (LIST_INDUCT_TAC THEN
    REWRITE_TAC [poly, poly_diff_aux, REAL_MUL_RZERO, DIFF_CONST] THEN
    MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"x:real"] THEN
    REWRITE_TAC [REAL_LDISTRIB, REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC [← GSYM (← ONCE_REWRITE_RULE [REAL_MUL_SYM] (← CONJUNCT2 pow))] THEN
    POP_ASSUM (MP_TAC o SPECL [← q r"SUC n", ← q r"x:real"]) THEN
    SUBGOAL_THEN (← q r"(((\x. (x pow (SUC n)) * h)) diffl
                          ((x pow n) * &(SUC n) * h))(x)")
    (fun th => DISCH_THEN (MP_TAC o CONJ th)) THENL
     [REWRITE_TAC [REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      MP_TAC (← SPEC (← q r"\x. x pow (SUC n)") DIFF_CMUL) THEN BETA_TAC THEN
      DISCH_THEN MATCH_MP_TAC THEN
      MP_TAC (← SPEC (← q r"SUC n") DIFF_POW) THEN REWRITE_TAC [SUC_SUB1] THEN
      DISCH_THEN (MATCH_ACCEPT_TAC o ONCE_REWRITE_RULE [REAL_MUL_SYM]),
      DISCH_THEN (MP_TAC o MATCH_MP DIFF_ADD) THEN BETA_TAC THEN
      REWRITE_TAC [REAL_MUL_ASSOC]])

  /- }}} -/

  let POLY_DIFF ← prove
   r"!l x. ((\x. poly l x) diffl (poly (poly_diff l) x))(x)"
  /- {{{ Proof -/

    (LIST_INDUCT_TAC THEN REWRITE_TAC [POLY_DIFF_CLAUSES] THEN
    ONCE_REWRITE_TAC [← SYM (← ExceptT.mk (ETA_CONV (← q r"\x. poly l x")))] THEN
    REWRITE_TAC [poly, DIFF_CONST] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:real"] THEN
    MP_TAC (← SPECL [← q r"t:(real)list", ← q r"0", ← q r"x:real"] POLY_DIFF_LEMMA) THEN
    REWRITE_TAC [← SYM (← ExceptT.mk (num_CONV (← q r"1")))] THEN REWRITE_TAC [pow, REAL_MUL_LID] THEN
    REWRITE_TAC [POW_1] THEN
    DISCH_THEN (MP_TAC o CONJ (← SPECL [← q r"h:real", ← q r"x:real"] DIFF_CONST)) THEN
    DISCH_THEN (MP_TAC o MATCH_MP DIFF_ADD) THEN BETA_TAC THEN
    REWRITE_TAC [REAL_ADD_LID])

  /- }}} -/

  let CANON_POLY_DIFF_CONV : ioconv ← do
    let aux_conv0 ← GEN_REWRITE_CONV_NET id [← CONJUNCT1 poly_diff_aux]
    let aux_conv1 ← GEN_REWRITE_CONV_NET id [← CONJUNCT2 poly_diff_aux]
    let diff_conv0 ← GEN_REWRITE_CONV_NET id (← liftExcept (butlast (CONJUNCTS POLY_DIFF_CLAUSES)))
    let diff_conv1 ← GEN_REWRITE_CONV_NET id [← liftExcept (last (CONJUNCTS POLY_DIFF_CLAUSES))]
    let POLY_DIFF_AUX_CONV := CANON_POLY_DIFF_CONV.POLY_DIFF_AUX_CONV aux_conv0 aux_conv1 NUM_SUC_CONV
    pure (diff_conv0 ORELSEC
      (diff_conv1 THENC POLY_DIFF_AUX_CONV))

  /-

  # POLY_DIFF_CONV (mk_comb(`poly_diff`,k2));;
  val it : Hol.thm =
    |- poly_diff k2 =
       [&1 * (&0 * z * &1 + y * (&0 + y * &3)); &2 * (&0 + y * (&0 + z * &2))]
  -/

  /- ------------------------------------------------------------------------- -/
  /- Add polynomials.                                                          -/
  /- ------------------------------------------------------------------------- -/

  let POLY_ADD_CONV : List term → ioconv ← do
    let (cnv_r, cnv_l, cnv_2, cnv_0) ← do
      let cs := (CONJUNCTS (← REAL_ARITH (← q r"(pol1 + (d + y * q) = (pol1 + d) + y * q) /\
       ((c + x * p) + pol2 = (c + pol2) + x * p) /\
       ((c + x * p) + (d + x * q) = (c + d) + x * (p + q)) /\
       (c + x * &0 = c)"))).map REWR_CONV
      match cs with
      | [cnv_r, cnv_l, cnv_2, cnv_0] => pure (cnv_r, cnv_l, cnv_2, cnv_0)
      | _ => throw "Match_failure"
    let dest_add := dest_binop (← q r"(+)")
    pure (POLY_ADD_CONV.go polyvar dest_add cnv_r cnv_l cnv_2 cnv_0 REAL_RAT_REDUCE_CONV)

  /-
  # POLY_ADD_CONV [`x:real`;`y:real`;`z:real`] (mk_binop `(+)` k0 k0) ;;
  val it : Hol.thm =
    |- ((&0 + y * (&0 + z * &3)) +
        x *
        (((&0 + z * &1) + y * (&0 + y * &3)) + x * (&0 + y * (&0 + z * &2)))) +
       (&0 + y * (&0 + z * &3)) +
       x * (((&0 + z * &1) + y * (&0 + y * &3)) + x * (&0 + y * (&0 + z * &2))) =
       (&0 + y * (&0 + z * &6)) +
       x * (((&0 + z * &2) + y * (&0 + y * &6)) + x * (&0 + y * (&0 + z * &4)))
  -/

  /- ------------------------------------------------------------------------- -/
  /- Negate polynomials.                                                       -/
  /- ------------------------------------------------------------------------- -/

  let POLY_NEG_CONV : ioconv ← do
    let cnv := REWR_CONV (← REAL_ARITH (← q r"--(c + x * p) = --c + x * --p"))
    pure (POLY_NEG_CONV.go cnv REAL_RAT_NEG_CONV)

  /- ------------------------------------------------------------------------- -/
  /- Subtract polynomials.                                                     -/
  /- ------------------------------------------------------------------------- -/

  let POLY_SUB_CONV : List term → ioconv ← do
    let cnv := REWR_CONV real_sub
    pure (fun vars => cnv THENC RAND_CONV POLY_NEG_CONV THENC POLY_ADD_CONV vars)

  /- ------------------------------------------------------------------------- -/
  /- Multiply polynomials.                                                     -/
  /- ------------------------------------------------------------------------- -/

  let POLY_MUL_CONV : List term → ioconv ← do
    let (cnv_l1, cnv_r1, cnv_2, cnv_l0, cnv_r0) ← do
      let cs := (CONJUNCTS (← REAL_ARITH (← q r"(pol1 * (d + y * q) = (pol1 * d) + y * (pol1 * q)) /\
       ((c + x * p) * pol2 = (c * pol2) + x * (p * pol2)) /\
       (pol1 * (d + x * q) = pol1 * d + (&0 + x * pol1 * q)) /\
       (&0 * pol2 = &0) /\
       (pol1 * &0 = &0)"))).map REWR_CONV
      match cs with
      | [cnv_l1, cnv_r1, cnv_2, cnv_l0, cnv_r0] => pure (cnv_l1, cnv_r1, cnv_2, cnv_l0, cnv_r0)
      | _ => throw "Match_failure"
    let dest_mul := dest_binop (← q r"( * )")
    let zero_tm ← q r"&0"
    pure (POLY_MUL_CONV.go polyvar dest_mul zero_tm cnv_l1 cnv_r1 cnv_2 cnv_l0 cnv_r0
      REAL_RAT_MUL_CONV POLY_ADD_CONV)

  /-

  # POLY_MUL_CONV [`x:real`;`y:real`;`z:real`] (mk_binop `( * )` k0 k0) ;;
  (the result is in poly_ext.ml)
  -/


  /- ------------------------------------------------------------------------- -/
  /- Exponentiate polynomials.                                                 -/
  /- ------------------------------------------------------------------------- -/

  let POLY_POW_CONV : List term → ioconv ← do
    let (cnv_0, cnv_1) ← match (CONJUNCTS real_pow).map REWR_CONV with
      | [cnv_0, cnv_1] => pure (cnv_0, cnv_1)
      | _ => throw "Match_failure"
    let zero_tm ← q r"0"
    pure (POLY_POW_CONV.go zero_tm cnv_0 cnv_1 num_CONV POLY_MUL_CONV)

  /-
  # POLY_POW_CONV [`x:real`;`y:real`;`z:real`] (mk_binop `(pow)` k0 `2`) ;;
  (the result is in poly_ext.ml)
  -/

  /- ------------------------------------------------------------------------- -/
  /- Convert expression to canonical polynomials.                              -/
  /- ------------------------------------------------------------------------- -/

  let POLYNATE_CONV : List term → ioconv ← do
    let cnv_var := REWR_CONV (← REAL_ARITH (← q r"x = &0 + x * &1"))
    let cnv_div := REWR_CONV real_div
    let neg_tm ← q r"(--)"
    let add_tm ← q r"(+)"
    let sub_tm ← q r"(-)"
    let mul_tm ← q r"( * )"
    let pow_tm ← q r"(pow)"
    let div_tm ← q r"(/)"
    pure (POLYNATE_CONV.go cnv_var cnv_div neg_tm add_tm sub_tm mul_tm pow_tm div_tm
      POLY_NEG_CONV REAL_RAT_REDUCE_CONV POLY_ADD_CONV POLY_SUB_CONV POLY_MUL_CONV POLY_POW_CONV)

  /-
  POLYNATE_CONV [`x:real`;`y:real`] `x + y`;;
  POLYNATE_CONV [`x:real`;`y:real`] `x * y + &2 * y`;;
  -/

  /- ------------------------------------------------------------------------- -/
  /- Pure term manipulation versions; will optimize eventually.                -/
  /- ------------------------------------------------------------------------- -/

  let poly_add_ : List term → term → term → ExceptT String IO term ← do
    let add_tm ← q r"(+)"
    pure (fun vars p1 p2 => do
      liftExcept (rand (concl (← ExceptT.mk (POLY_ADD_CONV vars
        (← liftExcept (do mk_comb (← mk_comb add_tm p1) p2)))))))

  let poly_sub_ : List term → term → term → ExceptT String IO term ← do
    let sub_tm ← q r"(-)"
    pure (fun vars p1 p2 => do
      liftExcept (rand (concl (← ExceptT.mk (POLY_SUB_CONV vars
        (← liftExcept (do mk_comb (← mk_comb sub_tm p1) p2)))))))

  let poly_mul_ : List term → term → term → ExceptT String IO term ← do
    let mul_tm ← q r"( * )"
    pure (fun vars p1 p2 => do
      liftExcept (rand (concl (← ExceptT.mk (POLY_MUL_CONV vars
        (← liftExcept (do mk_comb (← mk_comb mul_tm p1) p2)))))))

  let poly_neg_ : term → ExceptT String IO term ← do
    let neg_tm ← q r"(--)"
    pure (fun p => do
      liftExcept (rand (concl (← ExceptT.mk (POLY_NEG_CONV (← liftExcept (mk_comb neg_tm p)))))))

  let poly_pow_ : List term → term → Int → ExceptT String IO term ← do
    let pow_tm ← q r"(pow)"
    pure (fun vars p k => do
      liftExcept (rand (concl (← ExceptT.mk (POLY_POW_CONV vars
        (← liftExcept (do mk_comb (← mk_comb pow_tm p) (← mk_small_numeral k))))))))

  /- ------------------------------------------------------------------------- -/
  /- Get the degree of a polynomial.                                           -/
  /- ------------------------------------------------------------------------- -/

  let degree_ : List term → term → Except String Int ← pure (degree_.go polyvar)

  /- ------------------------------------------------------------------------- -/
  /- Get the list of coefficients.                                             -/
  /- ------------------------------------------------------------------------- -/

  let coefficients : List term → term → Except String (List term) ← pure (coefficients.go polyvar)

  /- ------------------------------------------------------------------------- -/
  /- Get the head constant.                                                    -/
  /- ------------------------------------------------------------------------- -/

  let head : List term → term → Except String term ← pure (fun vars p => do
    last (← coefficients vars p))

  /- ---------------------------------------------------------------------- -/
  /-  Remove the head coefficient                                           -/
  /- ---------------------------------------------------------------------- -/

  let behead : List term → term → Except String term ← pure
    (behead.go dest_plus dest_mult mk_plus mk_mult rzero)

  /-
  behead [`x:real`] `&1 + x * (&1 + x * (&0 + y * &1))`
  -/


  -- poly_ext.ml binds BEHEAD, then BEHEAD3, then `BEHEAD = BEHEAD3`; this
  -- first BEHEAD is built (its ARITH_RULE runs) but never used
  discard <| (show ExceptT String IO (List term → thm → term → ExceptT String IO thm) from do
    let lem ← ARITH_RULE (← q r"a + b * &0 = a")
    pure (fun vars zthm tm => do
      let _tm' ← liftExcept (behead vars tm)
        /- note: pure rewrite is ok here, as tm is in canonical form -/
      let thm1 ← ExceptT.mk (PURE_REWRITE_CONV [zthm] tm)
      let thm2 ← ExceptT.mk (PURE_REWRITE_CONV [lem] (← liftExcept (rhs (concl thm1))))
      let thm3 ← TRANS thm1 thm2
      pure thm3))

  let BEHEAD3 : List term → thm → term → ExceptT String IO thm ← do
    let lem ← ARITH_RULE (← q r"a + b * &0 = a")
    pure (fun vars zthm tm => do
      let _tm' ← liftExcept (behead vars tm)
      /- note slight hack here:
         BEHEAD was working fine if
         p = a + x * b where a <> b.  But
         when they were equal, dropping multiple levels
         broke the reconstruction.  Thus, we only do conversion
         on the right except when the head variable has been fully eliminated -/
      let conv ← do
        let (_l, r) ← liftExcept (dest_binop rp tm)
        let (l1, _r1) ← liftExcept (dest_binop rm r)
        if l1 == (← liftExcept (hd vars)) then
          pure (RAND_CONV (HolCore.Simp.PURE_ONCE_REWRITE_CONV' HolBase.B [zthm]))
        else pure (HolCore.Simp.PURE_ONCE_REWRITE_CONV' HolBase.B [zthm])
      let thm1 ← ExceptT.mk (conv tm)
      let thm2 ← ExceptT.mk (PURE_REWRITE_CONV [lem] (← liftExcept (rhs (concl thm1))))
      let thm3 ← TRANS thm1 thm2
      pure thm3)

  let BEHEAD : List term → thm → term → ExceptT String IO thm ← pure BEHEAD3


  /-
  let vars = [`z:real`;`x:real`]
  let zthm = (ASSUME `&0 + x * &1 = &0`)
  let tm = `(&0 + x * &1) + z * (&0 + x * &1)`
  behead vars tm
  BEHEAD vars zthm tm
  BEHEAD2 vars zthm tm
  BEHEAD3 vars zthm tm

  let tm = `(&0 + x * &1)`
  BEHEAD3 vars zthm tm



  let vars = [`x:real`]
  let tm = `&1 + x * (&1 + x * (&0 + y * &1))`
  let zthm = (ASSUME `&0 + y * &1 = &0`)
  BEHEAD vars zthm tm
  BEHEAD2 vars zthm tm



  -/

  /- ------------------------------------------------------------------------- -/
  /- Test whether a polynomial is a constant w.r.t. the head variable.         -/
  /- ------------------------------------------------------------------------- -/

  let is_const_poly : List term → term → Except String Bool ← pure (fun vars tm => do
    return (← polyvar tm) != (← hd vars))

  /- ------------------------------------------------------------------------- -/
  /- Monicize; return |- const * pol = monic-pol                               -/
  /- ------------------------------------------------------------------------- -/

  -- `num 1 // headconst p`: OCaml's Num division by zero raises
  -- Division_by_zero; Lean's Rat division by zero is 0
  let MONIC_CONV : List term → ioconv ← do
    let mul_tm ← q r"( * ):real->real->real"
    pure (fun vars p => ExceptT.run do
      let h ← liftExcept (headconst p)
      if h == 0 then throw "Division_by_zero" else
      let c := 1 / h
      ExceptT.mk (POLY_MUL_CONV vars
        (← liftExcept (do mk_comb (← mk_comb mul_tm (← term_of_rat c)) p))))

  /- ------------------------------------------------------------------------- -/
  /- Pseudo-division of s by p; head coefficient of p assumed nonzero.         -/
  /- Returns |- a^k s = p q + r for some q and r with deg(r) < deg(p).         -/
  /- Optimized only for the trivial case of equal head coefficients; no GCDs.  -/
  /- ------------------------------------------------------------------------- -/

  let PDIVIDE : List term → term → term → ExceptT String IO thm ← do
    let zero_tm ← q r"&0"
    let add0_tm ← q r"(+) (&0)"
    let add_tm ← q r"(+)"
    let mul_tm ← q r"( * )"
    let pow_tm ← q r"(pow)"
    let one_tm ← q r"&1"
    let mk_varpow (vars : List term) (k : Int) : Except String term := do
      let mulx_tm ← mk_comb mul_tm (← hd vars)
      (List.range k.toNat).foldlM (fun t _ => do mk_comb add0_tm (← mk_comb mulx_tm t)) one_tm
    let pdivide_aux := PDIVIDE.pdivide_aux zero_tm mk_varpow head degree_ poly_add_ poly_sub_
      poly_mul_ poly_pow_
    pure (fun vars s p => do
      let a ← liftExcept (head vars p)
      let (k, q, r) ← pdivide_aux vars a (← liftExcept (degree_ vars p)) p s
      let th1 ← ExceptT.mk (POLY_MUL_CONV vars (← liftExcept (do mk_comb (← mk_comb mul_tm q) p)))
      let th2 ← AP_THM (← AP_TERM add_tm th1) r
      let th3 ← CONV_RULE (RAND_CONV (POLY_ADD_CONV vars)) th2
      let th4 ← ExceptT.mk (POLY_POW_CONV vars
       (← liftExcept (do mk_comb (← mk_comb pow_tm a) (← mk_small_numeral k))))
      let th5 ← AP_THM (← AP_TERM mul_tm th4) s
      let th6 ← CONV_RULE (RAND_CONV (POLY_MUL_CONV vars)) th5
      TRANS th6 (← GSYM th3))

  /- ------------------------------------------------------------------------- -/
  /- Produce sign theorem for rational constant.                               -/
  /- ------------------------------------------------------------------------- -/

  let SIGN_CONST : term → ExceptT String IO thm ← do
    let zero : Rat := 0
    let zero_tm ← q r"&0"
    let eq_tm ← q r"(=):real->real->bool"
    let gt_tm ← q r"(>):real->real->bool"
    let lt_tm ← q r"(<):real->real->bool"
    pure (fun tm => do
      let x ← liftExcept (HolMath.CalcInt.rat_of_term tm)
      if x == zero then
        EQT_ELIM (← ExceptT.mk (REAL_RAT_EQ_CONV (← liftExcept (do mk_comb (← mk_comb eq_tm tm) zero_tm))))
      else if x > zero then
        EQT_ELIM (← ExceptT.mk (REAL_RAT_GT_CONV (← liftExcept (do mk_comb (← mk_comb gt_tm tm) zero_tm))))
      else
        EQT_ELIM (← ExceptT.mk (REAL_RAT_LT_CONV (← liftExcept (do mk_comb (← mk_comb lt_tm tm) zero_tm)))))

  /-
  SIGN_CONST `-- &5`;;
  val it : Hol.thm = |- &5 > &0
  -/


  /- ------------------------------------------------------------------------- -/
  /- Differentiation conversion in main representation.                        -/
  /- ------------------------------------------------------------------------- -/

  let POLY_DERIV_CONV : List term → term → ExceptT String IO thm ← do
    let _poly_diff_tm ← q r"poly_diff"
    let pth ← GEN_REWRITE_RULE id [SWAP_FORALL_THM] POLY_DIFF
    pure (fun vars tm => do
      let th1 ← ExceptT.mk ((← POLY_ENLIST_CONV vars) tm)
      let th2 ← SPECL [← liftExcept (hd vars), ← liftExcept (do lhand (← rand (concl th1)))] pth
      CONV_RULE (RATOR_CONV
        (COMB2_CONV (RAND_CONV (ABS_CONV (POLY_DELIST_CONV)))
                    (LAND_CONV (CANON_POLY_DIFF_CONV THENC
                               HolMath.Lists.LIST_CONV_IO (POLY_MUL_CONV vars)) THENC
                     POLY_DELIST_CONV))) th2)

  /-
  (examples in poly_ext.ml)
  -/

  /- ---------------------------------------------------------------------- -/
  /-  POLYATOM_CONV                                                         -/
  /- ---------------------------------------------------------------------- -/

  /-
    This is the AFN_CONV argument to the lifting function LIFT_QELIM_CONV
  -/

  let lt_lem ← prove_by_refinement (
    (← q r"!x y. x < y <=> x - y < &0"),
  /- {{{ Proof -/
  [
    REAL_ARITH_TAC
  ])
  /- }}} -/

  let le_lem ← prove_by_refinement (
    (← q r"!x y. x <= y <=> x - y <= &0"),
  /- {{{ Proof -/
  [
    REAL_ARITH_TAC
  ])
  /- }}} -/

  let eq_lem ← prove_by_refinement (
    (← q r"!x y. (x = y) <=> (x - y = &0)"),
  /- {{{ Proof -/
  [
    REAL_ARITH_TAC
  ])
  /- }}} -/

  let POLYATOM_CONV : List term → term → ExceptT String IO thm ← pure (fun vars tm => do
    let thm1 ← ExceptT.mk (ONCE_REWRITE_CONV [real_gt, real_ge, eq_lem] tm)
    let (_l, r) ← liftExcept (dest_eq (concl thm1))
    let thm2 ← ExceptT.mk (ONCE_REWRITE_CONV [lt_lem, le_lem] r)
    let (op, l', _r') ← liftExcept (get_binop (← liftExcept (rhs (concl thm2))))
    let thm3a ← ExceptT.mk (POLYNATE_CONV vars l')
    let thm3b ← AP_TERM op thm3a
    let thm3 ← AP_THM thm3b rzero
    HolLight.end_itlist TRANS [thm1, thm2, thm3])

  /-
  (examples in poly_ext.ml)
  -/

  /- ---------------------------------------------------------------------- -/
  /-  Factoring                                                             -/
  /- ---------------------------------------------------------------------- -/

  let weakfactor : term → term → Int × term ← pure (fun x pol =>
    weakfactor.go dest_plus dest_mult rzero 0 x pol)

  let poly_var : term → Except String term ← pure (fun x => do
    (← mk_plus rzero) (← (← mk_mult x) rone))
  /-
     poly_var rx
  -/

  let POW_PROD_SUM ← do
    let a1 ← ARITH_RULE (← q r"n + SUC m = SUC (n + m)")
    prove_by_refinement (
    (← q r"!x n m. (x pow n) * x pow m = x pow (n + m)"),
  /- {{{ Proof -/
  [
    STRIP_TAC THEN STRIP_TAC THEN INDUCT_TAC,
    REWRITE_TAC [real_pow],
    NUM_SIMP_TAC,
    REAL_SIMP_TAC,
    REWRITE_TAC [real_pow],
    REWRITE_TAC [a1],
    REWRITE_TAC [real_pow],
    POP_ASSUM (SUBST1_TAC o GSYM),
    REAL_ARITH_TAC
  ])
  /- }}} -/

  let lem1 ← REAL_ARITH (← q r"x * x = x pow 2")
  let lem2 ← GSYM (← CONJUNCT2 real_pow)
  let lem3 ← REAL_ARITH (← q r"!x. x = x pow 1")

  let SIMP_POW_CONV : term → ExceptT String IO thm ← pure (fun tm => do
    let thm1 ← ExceptT.mk (((REWRITE_CONV [← GSYM REAL_MUL_ASSOC, lem1, lem2, POW_PROD_SUM]) THENC
      (ARITH_SIMP_CONV [])) tm)
    let (_, r) ← liftExcept (dest_eq (concl thm1))
    if can dest_pow r then pure thm1 else
    let thm2 ← ISPEC r lem3
    pure thm2)

  /-
    SIMP_POW_CONV `x * x * x * x * x`
    SIMP_POW_CONV `x * x * (x * x) * x`
    SIMP_POW_CONV `x * (x * (x * x)) *(x * x)`
    SIMP_POW_CONV `x:real`

  -/


  let WEAKFACTOR_CONV : term → term → ExceptT String IO thm ← pure (fun x pol => do
    let (k, _pol') := weakfactor x pol
    let c ← GEN_REWRITE_CONV_NET id [REAL_ADD_LID]
    -- `itlist2 (fun x y z -> funpow y RAND_CONV x THENC z) (replicate c k) (0--(k-1)) ALL_CONV`
    let cs := replicate c k.toNat
    let ns := List.range k.toNat
    let conv := (cs.zip ns).foldr (fun (x, y) z => (Nat.repeat RAND_CONV y x) THENC z) ALL_CONV
    let thm1 ← ExceptT.mk ((conv THENC
               (PURE_REWRITE_CONV [REAL_MUL_ASSOC])) pol)
    let thm2 ← (CONV_RULE (RAND_CONV (LAND_CONV (fun t => (SIMP_POW_CONV t).run)))) thm1
    pure thm2)



  /-
    (examples in poly_ext.ml)
  -/

  -- @@RETURN BEGIN
  return { poly_tm, dest_poly, is_poly, polyvar, is_constant, POLY, POLY_ENLIST_CONV,
           POLY_DELIST_CONV, POLY_DIFF_CLAUSES, POLY_DIFF_LEMMA, POLY_DIFF,
           CANON_POLY_DIFF_CONV, POLY_ADD_CONV, POLY_NEG_CONV, POLY_SUB_CONV,
           POLY_MUL_CONV, POLY_POW_CONV, POLYNATE_CONV, poly_add_, poly_sub_, poly_mul_,
           poly_neg_, poly_pow_, degree_, coefficients, head, behead, BEHEAD3, BEHEAD,
           is_const_poly, MONIC_CONV, PDIVIDE, SIGN_CONST, POLY_DERIV_CONV, lt_lem,
           le_lem, eq_lem, POLYATOM_CONV, weakfactor, poly_var, POW_PROD_SUM, lem1, lem2,
           lem3, SIMP_POW_CONV, WEAKFACTOR_CONV }
  -- @@RETURN END

end HolRQE.PolyExt
