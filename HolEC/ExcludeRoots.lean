/- ========================================================================= -/
/- Prove that a congruence x^3 + a * x + b == 0 (mod p) has no solution.   -/
/- ========================================================================= -/
/- File: HolEC/ExcludeRoots.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/excluderoots.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.ExcludeRoots fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, INT_ARITH, TAUT, SET_RULE, ...) they are
  bound first, in OCaml's order.
-/

import HolLibrary.Iter
import HolLibrary.Prime
import HolLibrary.Pocklington

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolEC.ExcludeRoots

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CONG COPRIME_SYM DIVIDES_LE EXP FERMAT_LITTLE_PRIME IMP_CONJ INT_CONG_RREM
   INT_FORALL_POS INT_LT_REM_EQ INT_OF_NUM_EQ INT_OF_NUM_LT INT_OF_NUM_POW
   INT_OF_NUM_REM INT_POW_ADD INT_POW_REM INT_REM_EQ INT_REM_MOD_SELF
   INT_REM_POS_EQ LE_1 MOD_LT MULT_2 PRIME_COPRIME_EQ PRIME_IMP_NZ num_coprime : thm)
  deriving Inhabited

/-- What excluderoots.ml uses from Session besides theorems. -/
structure ExcludeRootsDeps where
  new_definition : String → ExceptT String IO thm
  define : String → ExceptT String IO thm
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  METIS_TAC : List thm → tactic
  ASM_METIS_TAC : List thm → tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  TAUT : term → ExceptT String IO thm
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
  PRIME_CONV : term → ExceptT String IO thm  -- pocklington.ml's PRIME_CONV
  PRIME_RULE : List String → term → ExceptT String IO thm  -- pocklington.ml's PRIME_RULE
  LET_TAC : tactic
  basic_ss : List thm → IO (Except String HolCore.Simp.simpset)
  mk_intconst : Rat → Except String term  -- int.ml's mk_intconst
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

/-- excluderoots.ml's `gcdex`, local to `num_modinv`: Bezout coefficients
    `(x,y)` with `x * m + y * n = gcd(m,n)`, for `m, n >= 0`. -/
partial def gcdex (m n : Int) : Int × Int :=
  if n < m then
    let (x, y) := gcdex n m
    (y, x)
  else if m = 0 then (0, 1) else
  let q := n / m
  let r := n - q * m
  let (x, y) := gcdex r m
  (y - q * x, x)

/-- excluderoots.ml's `num_modinv p n`: the inverse of `n` modulo `p`, or
    failure "num_modinv".  (`mod_num` and Lean's `%` on `Int` are both the
    Euclidean remainder.) -/
def num_modinv (p n : Int) : Except String Int :=
  let (x, _) := gcdex n p
  if (x * n) % p = 1 then .ok (x % p) else .error "num_modinv"

/-- The local `power_rule` of excluderoots.ml's EXCLUDE_MODULAR_CUBIC_ROOTS:
    `th0` for 0; otherwise the result for `n / 2`, squared (`sq`), and then
    multiplied by x (`mx`) when `n` is odd. -/
partial def powerRule (th0 : thm) (sq mx : thm → ExceptT String IO thm) (n : Nat) :
    ExceptT String IO thm := do
  if n = 0 then pure th0 else
  let m := n / 2
  let th1 ← powerRule th0 sq mx m
  let th2 ← sq th1
  if n % 2 = 0 then pure th2 else mx th2



/- ------------------------------------------------------------------------- -/
/- Prove that a congruence x^3 + a * x + b == 0 (mod p) has no solution      -/
/- (fails with an exception if it does). This is essentually done via a      -/
/- computation of gcd(x^p - x,x^3 + a * x + b) over F_p[x].                  -/
/-                                                                           -/
/- This can be used to show that a Weierstrass curve y^2 = x^3 + a * x + b   -/
/- has no 2-torsion points, since such points would necessarily have y = 0   -/
/- because the negation in the curve group of (x,y) is (x,-y).               -/
/- (excluderoots.ml 1-167; `num_modinv` and `power_rule` are above.)         -/
/- ------------------------------------------------------------------------- -/

structure ExcludeRootsRules where
  -- @@FIELDS
  EXCLUDE_MODULAR_CUBIC_ROOTS : term → thm → ExceptT String IO thm
  EXCLUDE_MODULAR_CUBIC_ROOTS_TAC : thm → List thm → ExceptT String IO tactic
  deriving Inhabited

@[nospecialize]
def setupExcludeRootsRules [HolBase] (D : ExcludeRootsDeps) :
    ExceptT String IO ExcludeRootsRules := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, INTEGER_RULE, INTEGER_TAC, INT_ARITH,
        INT_REDUCE_CONV, NUMBER_RULE, NUM_REDUCE_CONV, mk_intconst, .. } := D
  let { CONG, COPRIME_SYM, DIVIDES_LE, EXP, FERMAT_LITTLE_PRIME, IMP_CONJ,
        INT_CONG_RREM, INT_FORALL_POS, INT_LT_REM_EQ, INT_OF_NUM_EQ, INT_OF_NUM_LT,
        INT_OF_NUM_POW, INT_OF_NUM_REM, INT_POW_ADD, INT_POW_REM, INT_REM_EQ,
        INT_REM_MOD_SELF, INT_REM_POS_EQ, LE_1, MOD_LT, MULT_2, PRIME_COPRIME_EQ,
        PRIME_IMP_NZ, num_coprime, .. } := D.core1
  -- @@SCOPE END

  -- `let lemma_flt = .. and lemma_tolin = .. and .. and pth0 = .. in`, left
  -- to right
  let EXCLUDE_MODULAR_CUBIC_ROOTS : term → thm → ExceptT String IO thm ← do
    let lemma_flt ← prove
     r"((x pow 3 + a * x + b:int == &0) (mod &p)
        ==> (x pow p == c2 * x pow 2 + c1 * x + c0) (mod &p))
       ==> prime p
           ==> ~(b rem &p = &0)
               ==> ((x pow 3 + a * x + b == &0) (mod &p)
                   ==> (&0 == c2 * x pow 2 + (c1 - &1) * x + c0) (mod &p))"
     (← do
      -- right to left: the ARITH_RULE, the NUMBER_RULE, then the
      -- INTEGER_RULEs from the last backwards
      let a6 ← ARITH_RULE (← q r"~(p = 0) ==> SUC(p - 1) = p")
      let n5 ← ExceptT.mk (NUMBER_RULE
        (← q r"(x EXP a == 1) (mod p) ==> (x * x EXP a == x) (mod p)"))
      let i4 ← INTEGER_RULE
        (← q r"coprime(b,p) ==> (b rem p == b) (mod p) ==> coprime(b rem p,p)")
      let i3 ← INTEGER_RULE
        (← q r"(b rem p == b) (mod p) /\ coprime(b rem p,p) ==> coprime(b,p)")
      let i2 ← INTEGER_RULE
        (← q r"(x pow 3 + a * x + b:int == &0) (mod p)
          ==> coprime(b,p) ==> coprime(x,p)")
      let i1 ← INTEGER_RULE
        (← q r"(xp == x) (mod p)
          ==> (xp:int == c2 * x pow 2 + c1 * x + c0) (mod p)
               ==> (&0 == c2 * x pow 2 + (c1 - &1) * x + c0) (mod p)")
      pure (DISCH_THEN (fun th => REPEAT DISCH_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC i1 THEN
      FIRST_X_ASSUM (MP_TAC o MATCH_MP i2) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC i3 THEN
        REWRITE_TAC [INT_REM_MOD_SELF] THEN UNDISCH_TAC (← q r"~(b rem &p = &0)") THEN
        SUBGOAL_THEN (← q r"&0 <= b rem &p /\ b rem &p < &p") MP_TAC THENL
         [ASM_REWRITE_TAC [INT_REM_POS_EQ, INT_LT_REM_EQ] THEN
          ASM_SIMP_TAC [INT_OF_NUM_EQ, PRIME_IMP_NZ, INT_OF_NUM_LT, LE_1],
          SPEC_TAC (← q r"b rem &p", ← q r"x:int")] THEN
        REWRITE_TAC [← GSYM INT_FORALL_POS, IMP_CONJ] THEN
        X_GEN_TAC (← q r"n:num") THEN REWRITE_TAC [INT_OF_NUM_EQ, INT_OF_NUM_LT] THEN
        REPEAT DISCH_TAC THEN REWRITE_TAC [← GSYM num_coprime] THEN
        ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_SIMP_TAC [PRIME_COPRIME_EQ] THEN
        DISCH_THEN (MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC,
        DISCH_THEN (MP_TAC o MATCH_MP i4) THEN
        REWRITE_TAC [INT_REM_MOD_SELF]] THEN
      REWRITE_TAC [← GSYM INT_REM_EQ] THEN ONCE_REWRITE_TAC [← GSYM INT_POW_REM] THEN
      SUBGOAL_THEN (← q r"&0 <= x rem &p /\ x rem &p < &p") MP_TAC THENL
       [ASM_REWRITE_TAC [INT_REM_POS_EQ, INT_LT_REM_EQ] THEN
        ASM_SIMP_TAC [INT_OF_NUM_EQ, PRIME_IMP_NZ, INT_OF_NUM_LT, LE_1],
        SPEC_TAC (← q r"x rem &p", ← q r"x:int")] THEN
      REWRITE_TAC [← GSYM INT_FORALL_POS, IMP_CONJ] THEN
      REWRITE_TAC [INT_POW_REM, ← GSYM num_coprime, INT_OF_NUM_LT] THEN
      X_GEN_TAC (← q r"n:num") THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC [INT_OF_NUM_POW, INT_OF_NUM_REM, INT_OF_NUM_EQ] THEN
      MP_TAC (← SPECL [← q r"n:num", ← q r"p:num"] FERMAT_LITTLE_PRIME) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o MATCH_MP n5) THEN
      ASM_SIMP_TAC [← GSYM (← CONJUNCT2 EXP), CONG, MOD_LT] THEN
      ASM_SIMP_TAC [PRIME_IMP_NZ, a6]))
    let lemma_tolin ← prove
     r"(x pow 3 + a * x + b == &0) (mod p) /\
       (&0 == &1 * x pow 2 + c1 * x + c0) (mod p)
       ==> (&0:int == &0 * x pow 2 +
                      (a + c1 pow 2 - c0) * x + (b + c0 * c1)) (mod p)"
     (← do
      pure INTEGER_TAC)
    let lemma_toconst ← prove
     r"(x pow 3 + a * x + b == &0) (mod p) /\
       (&0:int == &0 * x pow 2 + &1 * x + c0) (mod p)
       ==> (&0:int == --c0 pow 3 - a * c0 + b) (mod p)"
     (← do
      pure INTEGER_TAC)
    let lemma_3_2 ← prove
     r"(x pow 3 + a * x + b:int == &0) (mod p)
       ==> (y == c3 * x pow 3 + c2 * x pow 2 + c1 * x + c0) (mod p)
           ==> (y == c2 * x pow 2 + (c1 - a * c3) * x + (c0 - b * c3)) (mod p)"
     (← do
      pure INTEGER_TAC)
    let lemma_4_3 ← prove
     r"(x pow 3 + a * x + b:int == &0) (mod p)
       ==> (y == c4 * x pow 4 + c3 * x pow 3 + c2 * x pow 2 + c1 * x + c0) (mod p)
           ==> (y == c3 * x pow 3 + (c2 - a * c4) * x pow 2 +
                     (c1 - b * c4) * x + c0) (mod p)"
     (← do
      pure INTEGER_TAC)
    let lemma_rem ← prove
     r"(y:int == c2 * x pow 2 + c1 * x + c0) (mod p)
       ==> (y == c2 rem p * x pow 2 + c1 rem p * x + c0 rem p) (mod p)"
     (← do
      let i1 ← INTEGER_RULE
       (← q r"(c2:int == c2') (mod p) /\ (c1 == c1') (mod p) /\ (c0 == c0') (mod p)
        ==> (y:int == c2 * x pow 2 + c1 * x + c0) (mod p)
            ==> (y:int == c2' * x pow 2 + c1' * x + c0') (mod p)")
      pure (MATCH_MP_TAC i1 THEN
      REWRITE_TAC [INT_CONG_RREM] THEN CONV_TAC (fun t => (INTEGER_RULE t).run)))
    let lemma_mulx ← prove
     r"((x:int) pow n == c2 * x pow 2 + c1 * x + c0) (mod p)
       ==> (x pow (n + 1) == c2 * x pow 3 + c1 * x pow 2 + c0 * x + &0) (mod p)"
     (← do
      pure (REWRITE_TAC [INT_POW_ADD] THEN INTEGER_TAC))
    let lemma_sqr ← prove
     r"((x:int) pow n == c2 * x pow 2 + c1 * x + c0) (mod p)
       ==> (x pow (2 * n) ==
            (c2 pow 2) * x pow 4 + (&2 * c1 * c2) * x pow 3 +
            (c1 pow 2 + &2 * c0 * c2) * x pow 2 +
            (&2 * c0 * c1) * x +
            c0 pow 2) (mod p)"
     (← do
      pure (REWRITE_TAC [MULT_2, INT_POW_ADD] THEN
      INTEGER_TAC))
    let lemma_mulc ← prove
     r"(y:int == c2 * x pow 2 + c1 * x + c0) (mod p)
       ==> !c. (c * y == (c * c2) * x pow 2 + (c * c1) * x + c * c0) (mod p)"
     (← do
      pure INTEGER_TAC)
    let pth0 ← INTEGER_RULE (← q r"!p. ((x:int) pow 0 == &0 * x pow 2 + &0 * x + &1)
                                 (mod &p)")
    pure (fun tm primeth => do
      let th ← ASSUME tm
      -- `let rule_3_2 = .. and .. and rule_rem = .. in`, left to right
      let m32 ← MATCH_MP lemma_3_2 th
      let rule_3_2 := MATCH_MP m32
      let m43 ← MATCH_MP lemma_4_3 th
      let rule_4_3 := MATCH_MP m43
      let rule_mulx := MATCH_MP lemma_mulx
      let rule_mulc := MATCH_MP lemma_mulc
      let rule_sqr := MATCH_MP lemma_sqr
      let rule_rem := MATCH_MP lemma_rem
      let qtm ← liftExcept (rand (concl primeth))
      let qn ← liftExcept (dest_numeral qtm)
      let th0 ← SPEC qtm pth0
      let power_rule := powerRule th0
        (fun th1 => do
          CONV_RULE INT_REDUCE_CONV (← CONV_RULE NUM_REDUCE_CONV
            (← rule_rem (← rule_3_2 (← rule_4_3 (← rule_sqr th1))))))
        (fun th2 => do
          CONV_RULE INT_REDUCE_CONV (← CONV_RULE NUM_REDUCE_CONV
            (← rule_rem (← rule_3_2 (← rule_mulx th2)))))
      let th1 ← DISCH tm (← power_rule qn.num.toNat)
      let th2 ← MP (← MATCH_MP lemma_flt th1) primeth
      let th3 ← MP th2 (← EQT_ELIM (← ExceptT.mk
        (INT_REDUCE_CONV (← liftExcept (lhand (concl th2))))))
      let th4 ← CONV_RULE INT_REDUCE_CONV (← rule_rem (← UNDISCH th3))
      let hc ← liftExcept (do
        HolMath.Int.dest_intconst (← lhand (← lhand (← rand (← rator (concl th4))))))
      let th8 ← if hc = 0 then pure th4 else do
        let th5 ← SPEC (← liftExcept (mk_intconst
          (← liftExcept (num_modinv qn.num hc.num)))) (← rule_mulc th4)
        let th6 ← CONV_RULE INT_REDUCE_CONV (← rule_rem th5)
        let th7 ← MATCH_MP lemma_tolin (← CONJ (← ASSUME tm) th6)
        CONV_RULE INT_REDUCE_CONV (← rule_rem th7)
      let lc ← liftExcept (do
        HolMath.Int.dest_intconst
          (← lhand (← lhand (← rand (← rand (← rator (concl th8)))))))
      let th9 ← SPEC (← liftExcept (mk_intconst
        (← liftExcept (num_modinv qn.num lc.num)))) (← rule_mulc th8)
      let tha ← CONV_RULE INT_REDUCE_CONV (← rule_rem th9)
      let thb ← MATCH_MP lemma_toconst (← CONJ (← ASSUME tm) tha)
      let thc ← CONV_RULE INT_REDUCE_CONV (← REWRITE_RULE [← GSYM INT_REM_EQ] thb)
      NOT_INTRO (← DISCH tm thc))

  -- `EXCLUDE_MODULAR_CUBIC_ROOTS_TAC primeth defths`; applying it builds the
  -- tactic (its INT_ARITH runs then, as in OCaml)
  let EXCLUDE_MODULAR_CUBIC_ROOTS_TAC : thm → List thm → ExceptT String IO tactic ← do
    pure (fun primeth defths => do
      let ia ← INT_ARITH
        (← q r"x pow 3 - &3 * x + b:int = x pow 3 + (-- &3) * x + b /\
               x pow 3 + &c = x pow 3 + &0 * x + &c")
      pure (X_GEN_TAC (← q r"x:int") THEN
      GEN_REWRITE_TAC ONCE_DEPTH_CONV [ia] THEN
      REWRITE_TAC defths THEN
      W (fun (_asl, w) => tactic_of do
        pure (ACCEPT_TAC (← EXCLUDE_MODULAR_CUBIC_ROOTS (← liftExcept (rand w))
          (← ONCE_REWRITE_RULE defths primeth))))))

  -- @@RETURN BEGIN
  return { EXCLUDE_MODULAR_CUBIC_ROOTS, EXCLUDE_MODULAR_CUBIC_ROOTS_TAC }
  -- @@RETURN END

end HolEC.ExcludeRoots
