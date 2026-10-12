/- File: Nums.lean
The axiom of infinity; construction of the natural numbers.
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
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
import HolMath.Pair
import HolMath.Base

namespace HolMath.Nums

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
/- The theorems established by this layer.                                -/
/- ---------------------------------------------------------------------- -/

/-- The four constants `mk_numeral` closes over in the OCaml
    (`mk_const("_0",[])`, `BIT0`, `BIT1`, `NUMERAL`).  They are looked up once
    and passed in, matching OCaml's load-time closure. -/
structure NumeralConsts where
  zero_tm    : term
  BIT0_tm    : term
  BIT1_tm    : term
  NUMERAL_tm : term
  deriving Inhabited

/-- Build the `NumeralConsts` by consulting the constant table (run once, after
    `setupNums` has defined `_0`, `BIT0`, `BIT1` and `NUMERAL`). -/
def numeralConsts : IO (Except String NumeralConsts) := ExceptT.run do
  let zero_tm ← (mk_const "_0" [] : IO (Except String term))
  let BIT0_tm ← (mk_const "BIT0" [] : IO (Except String term))
  let BIT1_tm ← (mk_const "BIT1" [] : IO (Except String term))
  let NUMERAL_tm ← (mk_const "NUMERAL" [] : IO (Except String term))
  return { zero_tm, BIT0_tm, BIT1_tm, NUMERAL_tm }

/-- Everything `nums.ml` proves, bundled for downstream layers.  `NOT_SUC`,
    `num_INDUCTION` and `num_Axiom` are the versions AFTER the `_0 = 0`
    rewriting, as in the OCaml. -/
structure NumsThms where
  ONE_ONE         : thm
  ONTO            : thm
  INFINITY_AX     : thm
  IND_SUC_0_EXISTS : thm
  IND_SUC_SPEC    : thm
  IND_SUC_INJ     : thm
  IND_SUC_0       : thm
  NUM_REP_RULES   : thm
  NUM_REP_INDUCT  : thm
  NUM_REP_CASES   : thm
  num_tydef       : thm × thm
  ZERO_DEF        : thm
  SUC_DEF         : thm
  NOT_SUC         : thm
  SUC_INJ         : thm
  num_INDUCTION   : thm
  num_Axiom       : thm
  NUMERAL         : thm
  num_RECURSION   : thm
  num_CASES       : thm
  BIT0_DEF        : thm
  BIT1_DEF        : thm
  /-- The `_0`/`BIT0`/`BIT1`/`NUMERAL` constants, looked up at the end of
      `setupNums` where they provably exist. -/
  numK            : NumeralConsts
  deriving Inhabited

/-- Run the `nums.ml` script: declare the type `ind`, assert the axiom of
    infinity, carve the natural numbers out of `ind` inductively, and prove
    induction, recursion and the cases theorem.  `SELECT_RULE`,
    `new_inductive_definition` and `prove_inductive_relations_exist` depend on
    session state, so Session passes them in. -/
@[nospecialize]
def setupNums [HolBase]
    (new_definition' : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic)
    (SELECT_RULE' : thm → Except String thm)
    (new_inductive_definition' : term → IO (Except String (thm × thm × thm)))
    (prove_inductive_relations_exist' : term → IO (Except String thm)) :
    ExceptT String IO NumsThms := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let new_definition_tm (t : term) : ExceptT String IO thm := new_definition' t
  let SELECT_RULE (th : thm) : ExceptT String IO thm := liftExcept (SELECT_RULE' th)
  let new_inductive_definition (s : String) :
      ExceptT String IO (thm × thm × thm) := do
    new_inductive_definition' (← q s)
  let prove_inductive_relations_exist (t : term) : ExceptT String IO thm :=
    prove_inductive_relations_exist' t
  let mk_eq (l r : term) : ExceptT String IO term := do
    let f ← ExceptT.mk _root_.mk_eq
    liftExcept (f (l, r))
  let { FUN_EQ_THM, UNIQUE_SKOLEM_ALT, .. } := HolBase.C
  let { EXISTS_UNIQUE_THM, EXISTS_UNIQUE_REFL, UNWIND_THM1, .. } := HolBase.T

  /- Declare a new type "ind" of individuals. -/

  ExceptT.mk (new_type "ind" 0)

  /- We assert the axiom of infinity as in HOL88, but then we can forget it! -/

  let ONE_ONE ← new_definition
   r"ONE_ONE(f:A->B) = !x1 x2. (f x1 = f x2) ==> (x1 = x2)"

  let ONTO ← new_definition
   r"ONTO(f:A->B) = !y. ?x. y = f x"

  let INFINITY_AX ← ExceptT.mk (new_axiom (← q r"?f:ind->ind. ONE_ONE f /\ ~(ONTO f)"))

  /- Actually introduce constants. -/

  let IND_SUC_0_EXISTS ← prove
   r"?(f:ind->ind) z. (!x1 x2. (f x1 = f x2) = (x1 = x2)) /\ (!x. ~(f x = z))"
   (X_CHOOSE_TAC (← q r"f:ind->ind") INFINITY_AX THEN EXISTS_TAC (← q r"f:ind->ind") THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [ONE_ONE, ONTO] THEN MESON_TAC [])

  let IND_SUC_SPEC ← do
    let th1 ← new_definition
     r"IND_SUC = @f:ind->ind. ?z. (!x1 x2. (f x1 = f x2) = (x1 = x2)) /\
                                (!x. ~(f x = z))"
    let th2 ← REWRITE_RULE [← GSYM th1] (← SELECT_RULE IND_SUC_0_EXISTS)
    let th3 ← new_definition
     r"IND_0 = @z:ind. (!x1 x2. IND_SUC x1 = IND_SUC x2 <=> x1 = x2) /\
                    (!x. ~(IND_SUC x = z))"
    REWRITE_RULE [← GSYM th3] (← SELECT_RULE th2)

  let (IND_SUC_INJ, IND_SUC_0) ← CONJ_PAIR IND_SUC_SPEC

  /- Carve out the natural numbers inductively. -/

  let (NUM_REP_RULES, NUM_REP_INDUCT, NUM_REP_CASES) ←
    new_inductive_definition
     r"NUM_REP IND_0 /\
    (!i. NUM_REP i ==> NUM_REP (IND_SUC i))"

  let num_tydef ← ExceptT.mk (new_basic_type_definition
    "num" "mk_num" "dest_num"
      (← CONJUNCT1 NUM_REP_RULES))

  let ZERO_DEF ← new_definition
   r"_0 = mk_num IND_0"

  let SUC_DEF ← new_definition
   r"SUC n = mk_num(IND_SUC(dest_num n))"

  /- Distinctness and injectivity of constructors. -/

  let NOT_SUC ← prove
   r"!n. ~(SUC n = _0)"
   (REWRITE_TAC [SUC_DEF, ZERO_DEF] THEN
    MESON_TAC [NUM_REP_RULES, num_tydef.1, num_tydef.2, IND_SUC_0])

  let SUC_INJ ← prove
   r"!m n. SUC m = SUC n <=> m = n"
   (REPEAT GEN_TAC THEN REWRITE_TAC [SUC_DEF] THEN
    EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    POP_ASSUM (MP_TAC o AP_TERM (← q r"dest_num")) THEN
    SUBGOAL_THEN (← q r"!p. NUM_REP (IND_SUC (dest_num p))") MP_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC (← CONJUNCT2 NUM_REP_RULES), ALL_TAC] THEN
    REWRITE_TAC [num_tydef.1, num_tydef.2] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC [IND_SUC_INJ] THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"mk_num")) THEN
    REWRITE_TAC [num_tydef.1])

  /- Induction. -/

  let num_INDUCTION ← prove
   r"!P. P(_0) /\ (!n. P(n) ==> P(SUC n)) ==> !n. P n"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPEC (← q r"\i. NUM_REP i /\ P(mk_num i):bool") NUM_REP_INDUCT) THEN
    ASM_REWRITE_TAC [← GSYM ZERO_DEF, NUM_REP_RULES] THEN
    W (fun g => tactic_of do pure (C SUBGOAL_THEN (fun t => REWRITE_TAC [t])
         (← funpowM 2 lhand (snd g)))) THENL
     [REPEAT STRIP_TAC THENL
       [MATCH_MP_TAC (← CONJUNCT2 NUM_REP_RULES) THEN ASM_REWRITE_TAC [],
        SUBGOAL_THEN (← q r"mk_num(IND_SUC i) = SUC(mk_num i)") SUBST1_TAC THENL
         [REWRITE_TAC [SUC_DEF] THEN REPEAT AP_TERM_TAC THEN
          CONV_TAC SYM_CONV THEN REWRITE_TAC [← GSYM num_tydef.2] THEN
          FIRST_ASSUM MATCH_ACCEPT_TAC,
          FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]],
      DISCH_THEN (MP_TAC o SPEC (← q r"dest_num n")) THEN
      REWRITE_TAC [num_tydef.1, num_tydef.2]])

  /- Recursion. -/

  let num_Axiom ← prove
   r"!(e:A) f. ?!fn. (fn _0 = e) /\
                   (!n. fn (SUC n) = f (fn n) n)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
     [MP_TAC (← prove_inductive_relations_exist
        (← q r"PRG _0 e /\ (!b:A n:num. PRG n b ==> PRG (SUC n) (f b n))")) THEN
      DISCH_THEN (CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o GSYM)) THEN
      SUBGOAL_THEN (← q r"!n:num. ?!y:A. PRG n y") MP_TAC THENL
       [MATCH_MP_TAC num_INDUCTION THEN REPEAT STRIP_TAC THEN
        FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC BINDER_CONV [← GSYM th])) THEN
        REWRITE_TAC [← GSYM NOT_SUC, NOT_SUC, SUC_INJ, EXISTS_UNIQUE_REFL] THEN
        REWRITE_TAC [UNWIND_THM1] THEN
        UNDISCH_TAC (← q r"?!y. PRG (n:num) (y:A)") THEN
        REWRITE_TAC [EXISTS_UNIQUE_THM] THEN
        DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"y:A")) ASSUME_TAC) THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
         [MAP_EVERY EXISTS_TAC [← q r"(f:A->num->A) y n", ← q r"y:A"],
          AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC] THEN
        ASM_REWRITE_TAC [],
        REWRITE_TAC [UNIQUE_SKOLEM_ALT] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"fn:num->A") (ASSUME_TAC o GSYM)) THEN
        EXISTS_TAC (← q r"fn:num->A") THEN ASM_REWRITE_TAC [] THEN
        GEN_TAC THEN FIRST_ASSUM (MATCH_MP_TAC o CONJUNCT2) THEN
        FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC I [← GSYM th])) THEN
        REFL_TAC],
      REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
      MATCH_MP_TAC num_INDUCTION THEN ASM_REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []])

  /- The basic numeral tag; rewrite existing instances of "_0". -/

  let NUMERAL ← do
    let num_ty := type_of (← lhand (concl ZERO_DEF))
    let funn_ty ← ExceptT.mk (mk_fun_ty num_ty num_ty)
    let numeral_tm := mk_var "NUMERAL" funn_ty
    let n_tm := mk_var "n" num_ty
    new_definition_tm (← mk_eq (← mk_comb numeral_tm n_tm) n_tm)

  let (NOT_SUC, num_INDUCTION, num_Axiom) ← do
    let th ← prove r"_0 = 0" (REWRITE_TAC [NUMERAL])
    let r := GEN_REWRITE_RULE DEPTH_CONV [th]
    pure (← r NOT_SUC, ← r num_INDUCTION, ← r num_Axiom)

  /- Induction tactic. -/

  let INDUCT_TAC : tactic :=
    MATCH_MP_TAC num_INDUCTION THEN
    CONJ_TAC THENL [ALL_TAC, GEN_TAC THEN DISCH_TAC]

  let num_RECURSION ← do
    let avs := (strip_forall (concl num_Axiom)).1
    GENL avs (← EXISTENCE (← SPECL avs num_Axiom))

  /- Cases theorem. -/

  let num_CASES ← prove
   r"!m. (m = 0) \/ (?n. m = SUC n)"
   (INDUCT_TAC THEN MESON_TAC [])

  /- Augmenting inductive type store: done by Session. -/

  /- "Bitwise" binary representation of numerals. -/

  let BIT0_DEF ← do
    let funn_ty := type_of (← rator (← lhand (← dest_forall (concl NUMERAL)).2))
    let bit0_tm := mk_var "BIT0" funn_ty
    let def_ ← new_definition_tm (← mk_eq bit0_tm
      (← q r"@fn. fn 0 = 0 /\ (!n. fn (SUC n) = SUC (SUC(fn n)))"))
    let th ← BETA_RULE (← ISPECL [← q r"0", ← q r"\m n:num. SUC(SUC m)"] num_RECURSION)
    REWRITE_RULE [← GSYM def_] (← SELECT_RULE th)

  let BIT1_DEF ← do
    let funn_ty := type_of (← rator (← lhand (← lhand (concl BIT0_DEF))))
    let num_ty := (← dest_fun_ty funn_ty).2
    let n_tm := mk_var "n" num_ty
    let bit1_tm := mk_var "BIT1" funn_ty
    new_definition_tm (← mk_eq (← mk_comb bit1_tm n_tm) (← q r"SUC (BIT0 n)"))

  let numK ← ExceptT.mk numeralConsts

  return { ONE_ONE, ONTO, INFINITY_AX, IND_SUC_0_EXISTS, IND_SUC_SPEC,
           IND_SUC_INJ, IND_SUC_0,
           NUM_REP_RULES, NUM_REP_INDUCT, NUM_REP_CASES, num_tydef,
           ZERO_DEF, SUC_DEF,
           NOT_SUC, SUC_INJ, num_INDUCTION, num_Axiom, NUMERAL,
           num_RECURSION, num_CASES, BIT0_DEF, BIT1_DEF, numK }

end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic)
open HolLight HolLight.Syntax

/- ---------------------------------------------------------------------- -/
/- Induction tactic.                                                      -/
/- ---------------------------------------------------------------------- -/

/-- `INDUCT_TAC` (nums.ml 165-167). -/
def INDUCT_TAC [HolBase] (num_INDUCTION : thm) : tactic :=
  MATCH_MP_TAC num_INDUCTION THEN
  CONJ_TAC THENL [ALL_TAC, GEN_TAC THEN DISCH_TAC]

end

section Numerals

open HolCore HolCore.Kernel HolCore.Basics HolCore.Lib

/- ---------------------------------------------------------------------- -/
/- Syntax operations on numerals.                                         -/
/- ---------------------------------------------------------------------- -/

/-- `stripzeros`: drop leading `false`s (the most significant zero bits). -/
private def stripzeros : List Bool → List Bool
  | false :: t => stripzeros t
  | l => l

/-- The 24 bits of one chunk, most significant first, exactly as the OCaml
    spells them out. -/
private def chunkBits (h : Nat) : List Bool :=
  [h &&& 8388608 != 0, h &&& 4194304 != 0, h &&& 2097152 != 0,
   h &&& 1048576 != 0, h &&& 524288 != 0,  h &&& 262144 != 0,
   h &&& 131072 != 0,  h &&& 65536 != 0,   h &&& 32768 != 0,
   h &&& 16384 != 0,   h &&& 8192 != 0,    h &&& 4096 != 0,
   h &&& 2048 != 0,    h &&& 1024 != 0,    h &&& 512 != 0,
   h &&& 256 != 0,     h &&& 128 != 0,     h &&& 64 != 0,
   h &&& 32 != 0,      h &&& 16 != 0,      h &&& 8 != 0,   h &&& 4 != 0,
   h &&& 2 != 0,       h &&& 1 != 0]

/-- `raw_list_of_num`: the bits of `n`, most significant first, taken 24 at a
    time (`pow2 24`) as in the OCaml. -/
private partial def raw_list_of_num (l : List Bool) (n : Rat) : List Bool :=
  if n == num_0 then stripzeros l
  else
    let h := (truncate_num (mod_num n (pow2 24))).toNat
    raw_list_of_num (chunkBits h ++ l) (quo_num n (pow2 24))

/-- `numeral_of_list`: wrap `t` in `BIT0`/`BIT1` for each bit, so the LAST
    element of the list ends up outermost (least significant). -/
private def numeral_of_list (K : NumeralConsts) : term → List Bool →
    Except String term
  | t, [] => .ok t
  | t, b :: r => do
    numeral_of_list K (← mk_comb (if b then K.BIT1_tm else K.BIT0_tm) t) r

/-- `mk_numeral`: the term `NUMERAL n` for a non-negative integer `n`. -/
def mk_numeral (K : NumeralConsts) (n : Rat) : Except String term :=
  if n < num_0 then failwith "mk_numeral: negative argument"
  else do
    let raw ← numeral_of_list K K.zero_tm (raw_list_of_num [] n)
    mk_comb K.NUMERAL_tm raw

/-- `mk_small_numeral`. -/
def mk_small_numeral (K : NumeralConsts) (n : Int) : Except String term :=
  mk_numeral K (Rat.ofInt n)

/-- `dest_small_numeral`. -/
def dest_small_numeral (t : term) : Except String Int := do
  return truncate_num (← dest_numeral t)

/-- `is_numeral`. -/
def is_numeral (t : term) : Bool := (dest_numeral t).toOption.isSome

/-- One entry of `the_specifications`: the `(names, th)` request and the
    resulting theorem. -/
abbrev specification := (List String × thm) × thm

/-- `check_distinct`: are all the names distinct? -/
private def check_distinct (l : List String) : Bool :=
  let rec go : List String → List String → Bool
    | [], _ => true
    | h :: t, res => if mem h res then false else go t (h :: res)
  -- OCaml folds right (`itlist`), but distinctness is order-independent.
  go l []

end Numerals

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolLight

/-- `new_specification names th` (nums.ml 256-299).  The mutable
    `the_specifications` list lives in Session, so the current list is passed
    in and the entry to store (if the specification is new) is returned with
    the theorem. -/
def new_specification_core [HolBase] (K : NumeralConsts)
    (new_definition : term → IO (Except String thm))
    (existing : List specification) (names : List String) (th : thm) :
    ExceptT String IO (thm × Option specification) := do
  let code (c : String) : Except String term :=
    match c.toList with
    | ch :: _ => mk_small_numeral K (Int.ofNat ch.toNat)
    | [] => failwith "new_specification: empty character"
  -- `end_itlist (curry mk_pair) (map code (explode name))`
  let mk_code (name : String) : ExceptT String IO term := do
    let cs ← liftExcept ((explode name).mapM code)
    let mk_pair (x y : term) : ExceptT String IO term := ExceptT.mk (HolMath.Pair.mk_pair (x, y))
    end_itlist mk_pair cs
  let check_distinct (l : List String) : Bool :=
    (l.foldrM (fun t res => if mem t res then none else some (t :: res)) []).isSome
  let specify (name : String) (th : thm) : ExceptT String IO thm := do
    let ntm ← mk_code name
    let gv ← (genvar (type_of ntm) : IO term)
    let th0 ← CONV_RULE (REWR_CONV HolBase.C.SKOLEM_THM) (← GEN gv th)
    let th1 ← CONV_RULE (thenc_ (RATOR_CONV (REWR_CONV HolBase.C.EXISTS_THM))
                           BETA_CONV) th0
    let (_l, r) ← liftExcept (dest_comb (concl th1))
    let rn ← liftExcept (mk_comb r ntm)
    let ty := type_of rn
    let mkeq ← ExceptT.mk (_root_.mk_eq : IO (Except String ((term × term) → Except String term)))
    let th2 ← ExceptT.mk (new_definition (← liftExcept (mkeq (mk_var name ty, rn))))
    GEN_REWRITE_RULE ONCE_DEPTH_CONV [← GSYM th2]
      (← SPEC ntm (← CONV_RULE BETA_CONV th1))
  let rec specifies : List String → thm → ExceptT String IO thm
    | [], th => pure th
    | name :: onames, th => do specifies onames (← specify name th)
  let (asl, c) := dest_thm th
  if !(asl == []) then
    throw "new_specification: Assumptions not allowed in theorem"
  if !(frees c == []) then
    let varName (t : term) : String :=
      match dest_var t with | .ok (n, _) => n | .error _ => ""
    throw ("new_specification: Free variables in predicate: " ++
      String.intercalate ", " ((frees c).map varName))
  let avs := (strip_exists c).1
  if names.length == 0 || names.length > avs.length then
    throw "new_specification: Unsuitable number of constant names"
  if !(check_distinct names) then
    throw "new_specification: Constant names not distinct"
  match existing.find? (fun e => e.1.1 == names && aconv (concl e.1.2) (concl th)) with
  | some e =>
      (warn true "Benign respecification" : IO Unit)
      return (e.2, none)
  | none =>
      let sth ← specifies names th
      return (sth, some ((names, th), sth))

end

end HolMath.Nums
