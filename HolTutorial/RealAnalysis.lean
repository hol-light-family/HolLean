/- File: HolTutorial/RealAnalysis.lean
Translation of HOL Light's Tutorial/Real_analysis.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolTutorial.Common
open HolCore.Kernel Session HolLight.Syntax HolTutorial
open HolCore.Tactics (tactic thm_tactic)
open HolCore.Lib (funpow)
open HolCore.Basics (dest_numeral)
open HolCore.Equal (ioconv SYM)
open SessionLibrary.Transc (COS_0 COS_ADD COS_DOUBLE SIN_DOUBLE SIN_CIRCLE
  ACS_COS COS_BOUNDS)
open SessionLibrary.Analysis (IVT IVT2 CONT_SUB CONT_X)
open HolCore.Simp (thencIO orelsecIO landConvIO randConvIO)

namespace HolTutorial.RealAnalysis

/-- Print `<fun>`, as the OCaml toplevel prints a function value. -/
def fn : IO Unit := IO.println "<fun>"

#eval phrase 1
-- needs "Library/analysis.ml";;  (loads the real-analysis library; not compared)
#eval SessionLibrary.Analysis.ensureAnalysis

#eval phrase 2
-- needs "Library/transc.ml";;  (loads the transcendental library; not compared)
#eval SessionLibrary.Transc.ensureTransc

#eval phrase 3
unsafe def cheb : thm := keep "cheb" fun _ => define
 [[(!x. cheb 0 x = &1) /\
  (!x. cheb 1 x = x) /\
  (!n x. cheb (n + 2) x = &2 * x * cheb (n + 1) x - cheb n x)]]
#eval cheb

#eval phrase 4
unsafe def CHEB_INDUCT : thm := keep "CHEB_INDUCT" fun _ => prove
 ([[!P. P 0 /\ P 1 /\ (!n. P n /\ P(n + 1) ==> P(n + 2)) ==> !n. P n]])
  (HolLight.tactic_of do
   let aa ← ExceptT.mk (HolLight.GSYM ADD_ASSOC)
   pure
    (GEN_TAC THEN STRIP_TAC THEN
     SUBGOAL_THEN ([[!n. P n /\ P(n + 1)]]) (fun th => MESON_TAC [th]) THEN
     INDUCT_TAC THEN ASM_SIMP_TAC [ADD1, aa] THEN
     ASM_SIMP_TAC [ARITH]))
#eval CHEB_INDUCT

#eval phrase 5
unsafe def CHEB_COS : thm := keep "CHEB_COS" fun _ => prove
 ([[!n x. cheb n (cos x) = cos(&n * x)]])
  (HolLight.tactic_of do
   let g1 ← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_ADD)
   pure
    (MATCH_MP_TAC CHEB_INDUCT THEN
     REWRITE_TAC [cheb, REAL_MUL_LZERO, REAL_MUL_LID, COS_0] THEN
     REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC [g1, REAL_MUL_LID, REAL_ADD_RDISTRIB] THEN
     REWRITE_TAC [COS_ADD, COS_DOUBLE, SIN_DOUBLE] THEN
     MP_TAC (SPEC ([[x:real]]) SIN_CIRCLE) THEN CONV_TAC REAL_RING))
#eval CHEB_COS

#eval phrase 6
unsafe def CHEB_RIPPLE : thm := keep "CHEB_RIPPLE" fun _ => prove
 ([[!x. abs(x) <= &1 ==> abs(cheb n x) <= &1]])
  (HolLight.tactic_of do
   let g1 ← ExceptT.mk (HolLight.GSYM REAL_BOUNDS_LE)
   pure
    (REWRITE_TAC [g1] THEN
     MESON_TAC [CHEB_COS, ACS_COS, COS_BOUNDS]))
#eval CHEB_RIPPLE

#eval phrase 7
/- let NUM_ADD2_CONV = let add_tm = `(+):num->num->num` and two_tm = `2` in
   fun tm -> let m = mk_numeral(dest_numeral tm less num 2) in
             let tm' = mk_comb(mk_comb(add_tm,m),two_tm) in
             SYM(NUM_ADD_CONV tm') -/
unsafe def NUM_ADD2_CONV : ioconv := fun tm => do
  let add_tm ← (HolLight.q "(+):num->num->num" : IO (Except String term))
  let two_tm ← (HolLight.q "2" : IO (Except String term))
  match (do
    let add_tm ← add_tm
    let two_tm ← two_tm
    let d ← dest_numeral tm
    let m ← mk_numeral (d - 2)
    let tm' ← mk_comb (← mk_comb add_tm m) two_tm
    pure tm' : Except String term) with
  | .error e => return .error e
  | .ok tm' =>
    match ← NUM_ADD_CONV tm' with
    | .error e => return .error e
    | .ok th => return SYM th
#eval fn

#eval phrase 8
/- let CHEB_CONV = let [pth0;pth1;pth2] = CONJUNCTS cheb in
     let rec conv tm =
      (GEN_REWRITE_CONV I [pth0; pth1] ORELSEC
       (LAND_CONV NUM_ADD2_CONV THENC
        GEN_REWRITE_CONV I [pth2] THENC
        COMB2_CONV
         (funpow 3 RAND_CONV ((LAND_CONV NUM_ADD_CONV) THENC conv))
         conv THENC
        REAL_POLY_CONV)) tm in
     conv -/
/-- `COMB2_CONV` for IO conversions (as `Equal.COMB2_CONV`, OCaml evaluating the
    arguments of `MK_COMB` right to left). -/
unsafe def comb2ConvIO (lconv rconv : ioconv) : ioconv := fun tm => do
  match tm with
  | .Comb l r => do
    match ← rconv r with
    | .error e => return .error e
    | .ok rth =>
      match ← lconv l with
      | .error e => return .error e
      | .ok lth => return MK_COMB lth rth
  | _ => return (.error "COMB2_CONV: Not a combination" : Except String thm)
unsafe def CHEB_CONV : ioconv :=
  let cs := CONJUNCTS cheb
  let pth0 := cs[0]!
  let pth1 := cs[1]!
  let pth2 := cs[2]!
  let rec conv : ioconv := fun tm =>
   orelsecIO (GEN_REWRITE_CONV id [pth0, pth1])
    (thencIO (landConvIO NUM_ADD2_CONV)
     (thencIO (GEN_REWRITE_CONV id [pth2])
      (thencIO
       (comb2ConvIO
        (funpow 3 randConvIO (thencIO (landConvIO NUM_ADD_CONV) conv))
        conv)
       REAL_POLY_CONV))) tm
  conv
#eval fn

#eval phrase 9
#eval do
  let tt : Except String term ← HolLight.q "cheb 8 x"
  match tt with
  | .error e => failure e
  | .ok t =>
    match ← CHEB_CONV t with
    | .ok th => IO.println th
    | .error e => failure e

#eval phrase 10
unsafe def CHEB_2N1 : thm := keep "CHEB_2N1" fun _ => prove
 ([[!n x. ((x - &1) * (cheb (2 * n + 1) x - &1) =
          (cheb (n + 1) x - cheb n x) pow 2) /\
         (&2 * (x pow 2 - &1) * (cheb (2 * n + 2) x - &1) =
          (cheb (n + 2) x - cheb n x) pow 2)]])
  (HolLight.tactic_of do
   let cheb2 ← ExceptT.mk (CHEB_CONV (← HolLight.q "cheb 2 x"))
   let cheb3 ← ExceptT.mk (CHEB_CONV (← HolLight.q "cheb 3 x"))
   let aa ← ExceptT.mk (HolLight.GSYM ADD_ASSOC)
   let a1 ← ARITH_RULE (← HolLight.q "n + 5 = (n + 3) + 2")
   let a2 ← ARITH_RULE (← HolLight.q "n + 4 = (n + 2) + 2")
   let a3 ← ARITH_RULE (← HolLight.q "n + 3 = (n + 1) + 2")
   pure
    (ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN GEN_TAC THEN
     MATCH_MP_TAC CHEB_INDUCT THEN
     REWRITE_TAC [ARITH, cheb, cheb2, cheb3] THEN
     REPEAT (CHANGED_TAC
      (REWRITE_TAC [aa, LEFT_ADD_DISTRIB, ARITH] THEN
       REWRITE_TAC [a1, a2, a3, cheb])) THEN
     CONV_TAC REAL_RING))
#eval CHEB_2N1

#eval phrase 11
unsafe def IVT_LEMMA1 : thm := keep "IVT_LEMMA1" fun _ => prove
 ([[!f. (!x. f contl x)
       ==> !x y. f(x) <= &0 /\ &0 <= f(y) ==> ?x. f(x) = &0]])
  (ASM_MESON_TAC [IVT, IVT2, REAL_LE_TOTAL])
#eval IVT_LEMMA1

#eval phrase 12
unsafe def IVT_LEMMA2 : thm := keep "IVT_LEMMA2" fun _ => prove
 ([[!f. (!x. f contl x) /\ (?x. f(x) <= x) /\ (?y. y <= f(y)) ==> ?x. f(x) = x]])
  (HolLight.tactic_of do
   let lam ← HolLight.q r"\x. f x - x"
   pure
    (REPEAT STRIP_TAC THEN MP_TAC (SPEC lam IVT_LEMMA1) THEN
     ASM_SIMP_TAC [CONT_SUB, CONT_X] THEN
     SIMP_TAC [REAL_LE_SUB_LADD, REAL_LE_SUB_RADD, REAL_SUB_0, REAL_ADD_LID] THEN
     ASM_MESON_TAC []))
#eval IVT_LEMMA2

#eval phrase 13
/-- `FIRST_ASSUM(UNDISCH_TAC o check is_eq o concl)`: undischarge the first
    assumption whose conclusion is an equation (a failure of `check` elsewhere). -/
unsafe def undischIsEq : thm_tactic := fun th =>
  if is_eq (concl th) then UNDISCH_TAC (concl th) else NO_TAC
unsafe def SARKOVSKII_TRIVIAL : thm := keep "SARKOVSKII_TRIVIAL" fun _ => prove
 ([[!f:real->real. (!x. f contl x) /\ (?x. f(f(f(x))) = x) ==> ?x. f(x) = x]])
  (HolLight.tactic_of do
   let lem ← MESON [] (← HolLight.q r"P x \/ P (f x) \/ P (f(f x)) ==> ?x:real. P x")
   pure
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC IVT_LEMMA2 THEN ASM_REWRITE_TAC [] THEN
     CONJ_TAC THEN MATCH_MP_TAC lem THEN
     FIRST_ASSUM undischIsEq THEN REAL_ARITH_TAC))
#eval SARKOVSKII_TRIVIAL

end HolTutorial.RealAnalysis
