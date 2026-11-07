/- File: Hol100/EIsTranscendental.lean
Translation of HOL Light's 100/e_is_transcendental.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Binomial
import SessionLibrary.Analysis
import SessionLibrary.Transc
import SessionLibrary.Prime
import SessionLibrary.Iter
import SessionLibrary.Integer
import SessionLibrary.Floor
import Hol100.Liouville
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Binomial SessionLibrary.Analysis SessionLibrary.Prime SessionLibrary.Iter SessionLibrary.Integer SessionLibrary.Floor SessionLibrary.Transc SessionLibrary.Poly Hol100.Liouville
namespace Hol100.EIsTranscendental

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
/- The file's own `PROVE` (the original `prove`, phrase 2): TAC_PROOF, then
   ALPHA to the goal; assumptions left by the proof stay in the result. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm := do
  let th ← ExceptT.mk (Session.TAC_PROOF ([], g) tac)
  let t' := concl th
  if t' == g then pure th
  else match (do HolCore.Kernel.EQ_MP (← HolCore.Equal.ALPHA t' g) th : Except String thm) with
    | .ok r => pure r
    | .error _ => throw "PROVE: justification generated wrong theorem"
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def ir (tm : term) : ExceptT String IO thm := ExceptT.mk (INTEGER_RULE tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/-
 *  HOL Light proof that e is transcendental.
 *
 *  This HOL Light proof and its relationship to the informal proof is
 *  described in :
 *
 *  "Formalizing a Proof that e is Transcendental", Journal of Formal
 *  Reasoning, Vol 4, No 1. 2011.
 *
 *  It follows the informal proof provided by the good folks at the
 *  planetmath website:
 *
 *  http://planetmath.org/encyclopedia/EIsTranscendental2.html
 *
 *  Note: the original proof script linked to in the above paper
 *  partitioned the proofs amongst several files, each encapsulated
 *  in an Ocaml module.  This file has simply concatenated those files
 *  and hence the module structure persists.
 *
 *  Jesse Bingham, Jan 2012
 *  jesse.d.bingham@intel.com
 *  jesse.bingham@gmail.com
 -/
/- Added 2022-07-29: use the original version of the prove function,
 * which did not complain about additional assumptions in the result,
 * though or clarity, give it a different name PROVE (uppercase).
 * Theorems with extra assumptions are used in a few places here so
 * it seemed easier to do this rather than modify the proofs.
 -/

#eval phrase 1
-- let PROVE(t,tac) = ... TAC_PROOF ...;;  (PROVE(t,tac) is translated as prove)
#eval IO.println "<fun>"

/- this is needed since the sum from the HOL core (iter.ml, i think)
 * which is used below, gets overwritten when Library/analysis.ml is loaded.
 -/

#eval phrase 2
-- let OLD_SUM = sum;;
def OLD_SUM : thm := Session.sum
#eval OLD_SUM

/- required stuff from HOL Light library... -/

#eval phrase 3
-- needs "Library/binomial.ml";;
#eval SessionLibrary.Binomial.ensureBinomial

#eval phrase 4
-- needs "Library/analysis.ml";;
#eval SessionLibrary.Analysis.ensureAnalysis

#eval phrase 5
-- needs "Library/transc.ml";;
#eval SessionLibrary.Transc.ensureTransc

#eval phrase 6
-- needs "Library/prime.ml";;
#eval SessionLibrary.Prime.ensurePrime

#eval phrase 7
-- needs "Library/iter.ml";;
#eval SessionLibrary.Iter.ensureIter

#eval phrase 8
-- needs "Library/integer.ml";;
#eval SessionLibrary.Integer.ensureInteger

#eval phrase 9
-- needs "Library/floor.ml";;
#eval SessionLibrary.Floor.ensureFloor

/- get def of transcendental from Harrison's Liouville proof  -/

#eval phrase 10
-- needs "100/liouville.ml";;
#eval Hol100.Liouville.ensure

#eval phrase 11
#eval Session.prioritize_real

/-
 *  A few misculaneous proof utility functions
 -/
/- A listified version of ADD_ASSUM -/

#eval phrase 12
-- let ADD_ASSUMS lst thm = ...;;
def ADD_ASSUMS (lst : List term) (th : thm) : ExceptT String IO thm :=
  lst.foldlM (fun x y => HolLight.ADD_ASSUM y x) th
#eval IO.println "<fun>"

/- A tactic that takes a goal with an assumption A /\ B and replaces
 * it with a goal with the two assumptions A and B
 -/

#eval phrase 13
-- let SPLIT_CONJOINED_ASSUMPT_TAC = ...;;
def SPLIT_CONJOINED_ASSUMPT_TAC (t : term) : HolCore.Tactics.tactic :=
  HolLight.tactic_of do
  let h1 ← tt (← ExceptT.mk [[(X /\ Y ==> Z) <=> (X ==> Y ==> Z)]])
  pure ((UNDISCH_TAC t) THEN
      (ONCE_REWRITE_TAC [h1]) THEN
      (DISCH_TAC THEN DISCH_TAC))
#eval IO.println "<fun>"

/- Adds an assumption and discharges it in one fell swoop -/

#eval phrase 14
-- let ADD_ASSUM_DISCH ass thm = DISCH ass (ADD_ASSUM ass thm);;
def ADD_ASSUM_DISCH (ass : term) (th : thm) : ExceptT String IO thm := do
  HolLight.DISCH ass (← HolLight.ADD_ASSUM ass th)
#eval IO.println "<fun>"

/- BRW = Bolean ReWrite -/

#eval phrase 15
-- let BRW t f = ONCE_REWRITE_RULE [TAUT t] f;;
def BRW (t : term) (f : thm) : ExceptT String IO thm := do
  HolLight.ONCE_REWRITE_RULE [← HolLight.TAUT t] f
#eval IO.println "<fun>"

/- Those two boolean rewrites come in handy -/

#eval phrase 16
-- let BRW0 f = BRW `(X ==> Y ==> Z) <=> (X /\ Y ==> Z)` f;;
def BRW0 (f : thm) : ExceptT String IO thm := do
  BRW (← ExceptT.mk [[(X ==> Y ==> Z) <=> (X /\ Y ==> Z)]]) f
#eval IO.println "<fun>"

#eval phrase 17
-- let BRW1 f = BRW `(X /\ Y ==> Z) <=> (X ==> Y ==> Z)` f;;
def BRW1 (f : thm) : ExceptT String IO thm := do
  BRW (← ExceptT.mk [[(X /\ Y ==> Z) <=> (X ==> Y ==> Z)]]) f
#eval IO.println "<fun>"

/- a bunch of trivial real theorems that are useful for
 * rewriting/simplifying/mesoning
 -/

#eval phrase 18
def rewrites0 : List thm := keep "rewrites0" fun _ => runList (do
  mapR rr [([[&0 + (y:real) = y]]), ([[(x:real) * &0 = &0]]), ([[(&1:real) + &0 = &1]]), ([[(x:real) * &1 = x]])]
)
#eval printThms rewrites0

#eval phrase 19
namespace Pm_lemma1
def PDI_DEF : thm := keep "PDI_DEF" fun _ => (do
  ExceptT.mk (Session.new_recursive_definition num_RECURSION ([[    (poly_diff_iter p 0 = p)
      /\ (poly_diff_iter p (SUC n) = poly_diff (poly_diff_iter p n))
    ]]))
  : ExceptT String IO thm).run
#eval replay PDI_DEF

def PDI_POLY_DIFF_COMM : thm := keep "PDI_POLY_DIFF_COMM" fun _ => (do
  prove ([[! p n.(poly_diff_iter (poly_diff p) n) = (poly_diff (poly_diff_iter p n))]])
   (STRIP_TAC THEN INDUCT_TAC THEN (ASM_SIMP_TAC [PDI_DEF]))
  : ExceptT String IO thm).run
#eval replay PDI_POLY_DIFF_COMM

def SODN : thm := keep "SODN" fun _ => new_definition
 [[SODN p n = iterate poly_add (0..n) (\i.poly_diff_iter p i)]]
#eval replay SODN

#eval phrase 20
def SOD : thm := keep "SOD" fun _ => new_definition
 [[!p. SOD p = SODN p (LENGTH p)]]
#eval replay SOD

#eval phrase 21
def PHI : thm := keep "PHI" fun _ => new_definition
 [[Phi f x = (exp (-- x)) * (poly (SOD f) x)]]
#eval replay PHI

def PLANETMATH_EQN_1_1_1 : thm := keep "PLANETMATH_EQN_1_1_1" fun _ => (do
  let lem1 ← HolLight.SPECL [([[\x.exp (--x)]]),
                        ([[\x.poly (SOD f) x]]),
                        ([[--(exp (--x))]]),
                        ([[poly (poly_diff (SOD f)) x]]),
                        ([[x:real]])] DIFF_MUL
  let EXP_NEG_X_DIFF ← prove ([[!x. ((\x.exp (--x)) diffl (-- (exp (--x))))(x)]])
     (STRIP_TAC THEN DIFF_TAC THEN REAL_ARITH_TAC2)
  let lem2 ← HolLight.SPEC ([[x:real]]) EXP_NEG_X_DIFF
  let lem3 ← HolLight.SPECL [([[SOD f]]), ([[x:real]])] POLY_DIFF
  let lem4 ← HolLight.CONJ lem2 lem3
  let lem5 ← HolLight.BETA_RULE (← HolLight.MP lem1 lem4)
  let lem6 ← rr (← ExceptT.mk [[(a*(b - c)) = (-- a*c) + (b*a)]])
  let PHI_abs ← prove ([[Phi f  = \x.((exp (-- x)) * (poly (SOD f) x))]])
     ((PURE_REWRITE_TAC [(← HolLight.SYM (ABS ([[x:real]]) (← HolLight.SPEC_ALL PHI)))]) THEN (ACCEPT_TAC (← HolLight.SYM (← ec (Session.ETA_CONV ([[\x.(Phi f x)]]))))))
  prove ([[! x f.((Phi f) diffl ((exp (--x)) * ((poly (poly_diff (SOD f)) x) - (poly (SOD f) x))) )(x)]])
   ((REPEAT STRIP_TAC) THEN
      (REWRITE_TAC [PHI_abs]) THEN
      (REWRITE_TAC [lem6]) THEN
      (ACCEPT_TAC lem5))
  : ExceptT String IO thm).run
#eval replay PLANETMATH_EQN_1_1_1

def POLY_SUB : thm := keep "POLY_SUB" fun _ => (do
  prove ([[!p1 p2 x. poly (p1 ++ (neg p2)) x = poly p1 x - poly p2 x]])
   ((REWRITE_TAC [POLY_ADD, poly_neg, POLY_CMUL]) THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval replay POLY_SUB

def ZERO_INSERT_NUMSEG : thm := keep "ZERO_INSERT_NUMSEG" fun _ => (do
  let lem01 ← ExceptT.mk (Session.SIMP_RULE [(← ar (← ExceptT.mk [[0 <= n]]))] (← HolLight.SPECL [([[0]]), ([[n:num]])] NUMSEG_LREC))
  let lem02 ← ExceptT.mk (Session.SIMP_RULE [(← ar (← ExceptT.mk [[0 + 1 = 1]]))] lem01)
  prove ([[!n. (0..n) = (0 INSERT (1..n))]])
   ((ACCEPT_TAC (← HolLight.GEN_ALL (← HolLight.GSYM lem02))))
  : ExceptT String IO thm).run
#eval replay ZERO_INSERT_NUMSEG

def PDI_POLYDIFF_SUC_LEMMA : thm := keep "PDI_POLYDIFF_SUC_LEMMA" fun _ => (do
  prove ([[!f n .(poly_diff_iter (poly_diff f) n) = poly_diff_iter f (SUC n)]])
   (STRIP_TAC THEN INDUCT_TAC THENL
      [(SIMP_TAC [PDI_DEF]),
        (ONCE_REWRITE_TAC [PDI_DEF]) THEN
        (ONCE_REWRITE_TAC [PDI_DEF]) THEN
        (SIMP_TAC [PDI_POLY_DIFF_COMM])])
  : ExceptT String IO thm).run
#eval replay PDI_POLYDIFF_SUC_LEMMA

def SOD_POLY_DIFF_ITERATE : thm := keep "SOD_POLY_DIFF_ITERATE" fun _ => (do
  let lemA1 ← HolLight.SPECL [([[1]]), ([[0]])] NUMSEG_EMPTY
  let lemA2 ← ExceptT.mk (Session.SIMP_RULE [(← ar (← ExceptT.mk [[0 < 1]]))] lemA1)
  let lem1 ← HolLight.MATCH_MP ITERATE_IMAGE_NONZERO MONOIDAL_POLY_ADD
  let lem2 ← HolLight.ISPECL [([[poly_diff_iter f]]), ([[SUC]]), ([[0..(LENGTH (poly_diff f))]])] lem1
  let lem3 ← ExceptT.mk (Session.SIMP_RULE [FINITE_NUMSEG] lem2)
  let lem4 ← HolLight.ONCE_REWRITE_RULE [(← ar (← ExceptT.mk [[~(~(x=y) /\ (SUC x) = (SUC y))]]))] lem3
  let lem5 ← ExceptT.mk (Session.SIMP_RULE [] lem4)
  let lem6 ← HolLight.ISPECL [([[0]]), ([[n:num]]), ([[1]])] NUMSEG_OFFSET_IMAGE
  let lem7 ← ExceptT.mk (Session.SIMP_RULE [(← ar (← ExceptT.mk [[!m.m+1 = SUC m]]))] lem6)
  let lem8 ← ExceptT.mk (Session.SIMP_RULE [(← ar (← ExceptT.mk [[SUC 0 = 1]]))] lem7)
  let lem9 ← HolLight.ONCE_REWRITE_RULE [(← ec (Session.ETA_CONV ([[(\i. SUC i)]])))] lem8
  let lem10 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM lem9)] lem5
  let lem11 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM (← ec (Session.ETA_CONV ([[(\i. poly_diff_iter f i)]]))))] lem10
  let lem12 ← ExceptT.mk (Session.SIMP_RULE [o_DEF] lem11)
  let lemma0 ← prove ([[! h t.SUC (LENGTH (poly_diff (CONS h t))) = LENGTH (CONS h t)]])
     ((SIMP_TAC [LENGTH_POLY_DIFF, Session.listDefs.LENGTH, PRE]))
  prove ([[!f .(SOD (poly_diff f)) = iterate (++) (1..(LENGTH f)) (\i.poly_diff_iter f i)]])
   ((ONCE_REWRITE_TAC [SOD]) THEN (ONCE_REWRITE_TAC [SODN]) THEN
      (ONCE_REWRITE_TAC [PDI_POLYDIFF_SUC_LEMMA]) THEN LIST_INDUCT_TAC THENL
      [(SIMP_TAC [poly_diff, Session.listDefs.LENGTH]) THEN
        (SIMP_TAC [(← HolLight.GSYM lemma0), lem12]) THEN
        (SIMP_TAC [NUMSEG_SING, MONOIDAL_POLY_ADD, ITERATE_SING]) THEN
        (SIMP_TAC [lemA2, (← HolLight.MATCH_MP ITERATE_CLAUSES_GEN MONOIDAL_POLY_ADD)]) THEN
        (ONCE_REWRITE_TAC [POLY_ADD_IDENT]) THEN
        (SIMP_TAC [PDI_DEF, POLY_DIFF_CLAUSES]),
        (SIMP_TAC [lem12, (← HolLight.GSYM lemma0)])])
  : ExceptT String IO thm).run
#eval replay SOD_POLY_DIFF_ITERATE

def ZERO_ITERATE_POLYADD_LEMMA : thm := keep "ZERO_ITERATE_POLYADD_LEMMA" fun _ => (do
  let lem0 ← prove ([[!n. ~(0 IN (1..n))]])
     (STRIP_TAC THEN (ONCE_REWRITE_TAC [IN_NUMSEG]) THEN
                        ARITH_TAC)
  let lem1 ← HolLight.ISPEC ([[poly_add]]) ITERATE_CLAUSES_GEN
  let lem2 ← ExceptT.mk (Session.SIMP_RULE [MONOIDAL_POLY_ADD] lem1)
  let lem3 ← HolLight.CONJUNCT2 lem2
  let lem4 ← HolLight.ISPECL [([[f:(num -> (real)list)]]), ([[0]]), ([[1..n]])] lem3
  let lem5 ← HolLight.ISPECL [([[poly_add]]), ([[f:(num -> (real)list)]]), ([[1..n]])] FINITE_SUPPORT
  let lem6 ← ExceptT.mk (Session.SIMP_RULE [FINITE_NUMSEG] lem5)
  let lem7 ← HolLight.MP lem4 lem6
  let lem9 ← ExceptT.mk (Session.SIMP_RULE [lem0] lem7)
  prove ([[!n f .iterate (++) (0 INSERT (1..n)) f
           = (f 0) ++ iterate (++) (1..n) f]])
   ((ACCEPT_TAC (← HolLight.GEN_ALL lem9)))
  : ExceptT String IO thm).run
#eval replay ZERO_ITERATE_POLYADD_LEMMA

def SOD_SOD_POLYDIFF : thm := keep "SOD_SOD_POLYDIFF" fun _ => (do
  prove ([[!f .(SOD f) = f ++ (SOD (poly_diff f))]])
   ((ONCE_REWRITE_TAC [SOD_POLY_DIFF_ITERATE]) THEN (ONCE_REWRITE_TAC [SOD]) THEN
      (ONCE_REWRITE_TAC [SODN]) THEN
      (ONCE_REWRITE_TAC [ZERO_INSERT_NUMSEG]) THEN
      (ONCE_REWRITE_TAC [ZERO_ITERATE_POLYADD_LEMMA]) THEN
      BETA_TAC THEN (SIMP_TAC [PDI_DEF]))
  : ExceptT String IO thm).run
#eval replay SOD_SOD_POLYDIFF

def SUC_INSERT_NUMSEG : thm := keep "SUC_INSERT_NUMSEG" fun _ => (do
  let lem01 ← ExceptT.mk (Session.SIMP_RULE [(← ar (← ExceptT.mk [[0 <= SUC n]]))] (← HolLight.SPECL [([[0]]), ([[n:num]])] NUMSEG_REC))
  prove ([[!n. (0..(SUC n)) = (SUC n) INSERT (0..n)]])
   (ACCEPT_TAC (← HolLight.GEN_ALL lem01))
  : ExceptT String IO thm).run
#eval replay SUC_INSERT_NUMSEG

def SUC_NOT_IN_NUMSEG : thm := keep "SUC_NOT_IN_NUMSEG" fun _ => (do
  prove ([[!m n. ~((SUC n) IN (m..n))]])
   (STRIP_TAC THEN (ONCE_REWRITE_TAC [IN_NUMSEG]) THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval replay SUC_NOT_IN_NUMSEG

def SUC_ITERATE_PDI_POLYDIFF_LEMMA : thm := keep "SUC_ITERATE_PDI_POLYDIFF_LEMMA" fun _ => (do
  let lem1 ← HolLight.ISPEC ([[poly_add]]) ITERATE_CLAUSES_GEN
  let lem2 ← ExceptT.mk (Session.SIMP_RULE [MONOIDAL_POLY_ADD] lem1)
  let lem3 ← HolLight.CONJUNCT2 lem2
  let lem4 ← HolLight.ISPECL [([[(\i.poly_diff_iter (poly_diff p) i)]]), ([[SUC n]]), ([[0..n]])] lem3
  let lem5 ← HolLight.ISPECL [([[poly_add]]), ([[\i.poly_diff_iter (poly_diff p) i]]), ([[0..n]])] FINITE_SUPPORT
  let lem6 ← ExceptT.mk (Session.SIMP_RULE [FINITE_NUMSEG] lem5)
  let lem7 ← HolLight.MP lem4 lem6
  let lem9 ← ExceptT.mk (Session.SIMP_RULE [(← HolLight.SPEC ([[0]]) SUC_NOT_IN_NUMSEG)] lem7)
  prove ([[iterate (++) ((SUC n) INSERT (0..n)) (\i.poly_diff_iter (poly_diff p) i) =
     (poly_diff_iter (poly_diff p) (SUC n)) ++
     iterate (++) (0..n) (\i.poly_diff_iter (poly_diff p) i)]])
   (ACCEPT_TAC lem9)
  : ExceptT String IO thm).run
#eval replay SUC_ITERATE_PDI_POLYDIFF_LEMMA

def SODN_POLY_DIFF_COMM : thm := keep "SODN_POLY_DIFF_COMM" fun _ => (do
  let lem ← HolLight.MP (← HolLight.ISPEC ([[poly_add]]) ITERATE_SING) MONOIDAL_POLY_ADD
  let lem1 ← HolLight.ISPEC ([[poly_add]]) ITERATE_CLAUSES_GEN
  let lem2 ← ExceptT.mk (Session.SIMP_RULE [MONOIDAL_POLY_ADD] lem1)
  let lem3 ← HolLight.CONJUNCT2 lem2
  let lem10 ← ExceptT.mk (Session.SIMP_RULE [(← HolLight.GSYM SUC_INSERT_NUMSEG)] SUC_ITERATE_PDI_POLYDIFF_LEMMA)
  let lema00 ← HolLight.ISPECL [([[(\i.poly_diff_iter (p) i)]]), ([[SUC n]]), ([[0..n]])] lem3
  let lema0 ← ExceptT.mk (Session.SIMP_RULE [(← HolLight.GSYM SUC_INSERT_NUMSEG)] lema00)
  let lem15 ← HolLight.ISPECL [([[poly_add]]), ([[\i.poly_diff_iter (p) i]]), ([[0..n]])] FINITE_SUPPORT
  let lem16 ← ExceptT.mk (Session.SIMP_RULE [FINITE_NUMSEG] lem15)
  let lema1 ← HolLight.MP lema0 lem16
  let lema2 ← ExceptT.mk (Session.SIMP_RULE [(← HolLight.SPEC ([[0]]) SUC_NOT_IN_NUMSEG)] lema1)
  let lema3 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM SODN)] lema2
  prove ([[!n p.(SODN (poly_diff p) n) = poly_diff (SODN p n)]])
   (INDUCT_TAC THENL
      [(ONCE_REWRITE_TAC [SODN]) THEN
        (SIMP_TAC [NUMSEG_SING, ITERATE_SING]) THEN
        (ONCE_REWRITE_TAC [lem]) THEN
        BETA_TAC THEN
        (SIMP_TAC [PDI_POLY_DIFF_COMM]),
        (ONCE_REWRITE_TAC [SODN]) THEN (ONCE_REWRITE_TAC [lem10]) THEN
        (ONCE_REWRITE_TAC [(← HolLight.GSYM SODN)]) THEN (ASM_SIMP_TAC []) THEN
        (ONCE_REWRITE_TAC [PDI_DEF]) THEN
        (ONCE_REWRITE_TAC [PDI_POLY_DIFF_COMM]) THEN
        (ONCE_REWRITE_TAC [(← HolLight.GSYM POLYDIFF_ADD)]) THEN
        STRIP_TAC THEN AP_TERM_TAC THEN
        (ONCE_REWRITE_TAC [lema3]) THEN (SIMP_TAC [PDI_DEF])])
  : ExceptT String IO thm).run
#eval replay SODN_POLY_DIFF_COMM

def SUC_ITERATE_POLYADD_LEMMA : thm := keep "SUC_ITERATE_POLYADD_LEMMA" fun _ => (do
  let lem1 ← HolLight.ISPEC ([[poly_add]]) ITERATE_CLAUSES_GEN
  let lem2 ← ExceptT.mk (Session.SIMP_RULE [MONOIDAL_POLY_ADD] lem1)
  let lem3 ← HolLight.CONJUNCT2 lem2
  let lem4 ← HolLight.ISPECL [([[f:(num -> (real)list)]]), ([[SUC n]]), ([[0..n]])] lem3
  let lem5 ← HolLight.ISPECL [([[poly_add]]), ([[f:(num -> (real)list)]]), ([[0..n]])] FINITE_SUPPORT
  let lem6 ← ExceptT.mk (Session.SIMP_RULE [FINITE_NUMSEG] lem5)
  let lem7 ← HolLight.MP lem4 lem6
  let lem9 ← ExceptT.mk (Session.SIMP_RULE [(← HolLight.SPEC ([[0]]) SUC_NOT_IN_NUMSEG)] lem7)
  prove ([[!n f .iterate (++) ((SUC n) INSERT (0..n)) f
           = (f (SUC n)) ++ iterate (++) (0..n) f]])
   (ACCEPT_TAC (← HolLight.GEN_ALL lem9))
  : ExceptT String IO thm).run
#eval replay SUC_ITERATE_POLYADD_LEMMA

def NUMSEG_LENGTH_POLYDIFF_LEMMA : thm := keep "NUMSEG_LENGTH_POLYDIFF_LEMMA" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[0 <= SUC n]])
  prove ([[!f. (0..(LENGTH f)) = ((LENGTH f) INSERT (0..(LENGTH (poly_diff f))))]])
   ((SIMP_TAC [LENGTH_POLY_DIFF]) THEN LIST_INDUCT_TAC THENL
      [(SIMP_TAC [Session.listDefs.LENGTH, PRE]) THEN (SIMP_TAC [NUMSEG_CLAUSES]) THEN
        (SIMP_TAC [INSERT_DEF, NOT_IN_EMPTY, IN]),
        (SIMP_TAC [Session.listDefs.LENGTH, PRE]) THEN
        (SIMP_TAC [h1, NUMSEG_REC])])
  : ExceptT String IO thm).run
#eval replay NUMSEG_LENGTH_POLYDIFF_LEMMA

def POLY_DIFF_LENGTH_LT : thm := keep "POLY_DIFF_LENGTH_LT" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[!n.(~(n=0)) ==> (PRE n) < n]])
  prove ([[!p. (~(p=[])) ==> (LENGTH (poly_diff p)) < (LENGTH p)]])
   (SIMP_TAC [LENGTH_POLY_DIFF, Session.listThms1.LENGTH_EQ_NIL,
                 h1])
  : ExceptT String IO thm).run
#eval replay POLY_DIFF_LENGTH_LT

#eval phrase 22
def POLY_DIFF_LENGTH_LE_SUC : thm := keep "POLY_DIFF_LENGTH_LE_SUC" fun _ => (do
  prove ([[! p n . (LENGTH p <= SUC n)  ==> (LENGTH (poly_diff p) <= n)]])
   ((REPEAT STRIP_TAC) THEN (ASM_CASES_TAC ([[p:(real)list =[] ]])) THENL
      [(ASM_SIMP_TAC [poly_diff, Session.listDefs.LENGTH]) THEN ARITH_TAC,
        (ASM_MESON_TAC [POLY_DIFF_LENGTH_LT, LT_SUC_LE, LTE_TRANS])])
  : ExceptT String IO thm).run
#eval replay POLY_DIFF_LENGTH_LE_SUC

def PDI_LENGTH_AUX : thm := keep "PDI_LENGTH_AUX" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[n <= 0 <=> n = 0]])
  prove ([[! n p. (LENGTH p <= n) ==> poly_diff_iter p n = [] ]])
   (INDUCT_TAC THENL
      [MESON_TAC [PDI_DEF, Session.listThms1.LENGTH_EQ_NIL, h1],
        ASM_MESON_TAC [PDI_DEF, PDI_POLY_DIFF_COMM, POLY_DIFF_LENGTH_LE_SUC]])
  : ExceptT String IO thm).run
#eval replay PDI_LENGTH_AUX

def PDI_LENGTH_NIL : thm := keep "PDI_LENGTH_NIL" fun _ => (do
  prove ([[! p . poly_diff_iter p (LENGTH p) = [] ]])
   (SIMP_TAC [PDI_LENGTH_AUX, LE_REFL])
  : ExceptT String IO thm).run
#eval replay PDI_LENGTH_NIL

def SOD_POLYDIFF_THEOREM : thm := keep "SOD_POLYDIFF_THEOREM" fun _ => (do
  let lemmmag ← prove ([[0 INSERT (0..0) = (0..0)]])
     ((SIMP_TAC [NUMSEG_SING]) THEN
          (SIMP_TAC [INSERT_DEF, NOT_IN_EMPTY, IN]))
  let SUC_LENGTH_CONS ← prove ([[SUC (LENGTH (t:(real)list)) = (LENGTH (CONS h t))]])
     ((SIMP_TAC [Session.listDefs.LENGTH]))
  prove ([[!f .(SOD (poly_diff f)) = (poly_diff (SOD f))]])
   ((ONCE_REWRITE_TAC [SOD]) THEN
      (ONCE_REWRITE_TAC [SODN_POLY_DIFF_COMM]) THEN
      (ONCE_REWRITE_TAC [SODN]) THEN
      STRIP_TAC THEN
      (CONV_TAC (HolLight.RAND_CONV (HolLight.ONCE_REWRITE_CONV [NUMSEG_LENGTH_POLYDIFF_LEMMA]))) THEN
      (SPEC_TAC (([[f:(real)list]]), ([[f:(real)list]]))) THEN
      LIST_INDUCT_TAC THENL
      [(SIMP_TAC [poly_diff]) THEN
        (SIMP_TAC [Session.listDefs.LENGTH]) THEN
        (SIMP_TAC [SUM_SING_NUMSEG]) THEN
        (SIMP_TAC [lemmmag]),
         (SIMP_TAC [LENGTH_POLY_DIFF]) THEN
         (SIMP_TAC [Session.listDefs.LENGTH, PRE]) THEN
         (CONV_TAC (HolLight.RAND_CONV (HolLight.ONCE_REWRITE_CONV [SUC_ITERATE_POLYADD_LEMMA]))) THEN
         (SIMP_TAC [Session.listDefs.LENGTH, PRE]) THEN
         (SIMP_TAC [(← HolLight.GSYM SODN)]) THEN
         (ONCE_REWRITE_TAC [(← HolLight.GSYM SODN)]) THEN
         (ONCE_REWRITE_TAC [SUC_LENGTH_CONS]) THEN
         (ONCE_REWRITE_TAC [PDI_LENGTH_NIL]) THEN
         (SIMP_TAC [POLY_ADD_CLAUSES])])
  : ExceptT String IO thm).run
#eval replay SOD_POLYDIFF_THEOREM

def SOD_SOD_DIFF_LEMMA : thm := keep "SOD_SOD_DIFF_LEMMA" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[((x:real) + y) -y = x]])
  prove ([[!f x.(poly (SOD f) x) - (poly (poly_diff (SOD f)) x) = poly f x]])
   (MESON_TAC [SOD_SOD_POLYDIFF, POLY_ADD, POLY_SUB, SOD_POLYDIFF_THEOREM,
                 h1])
  : ExceptT String IO thm).run
#eval replay SOD_SOD_DIFF_LEMMA

def PLANETMATH_EQN_1_1_2 : thm := keep "PLANETMATH_EQN_1_1_2" fun _ => (do
  let lem17 ← prove ([[!x y.(x - y) = (-- (y - x))]])
     (REAL_ARITH_TAC2)
  prove ([[!f x.
        ((exp (--x)) * ((poly (poly_diff (SOD f)) x) - (poly (SOD f) x)))
        = (-- (exp (--x))) * (poly f x)]])
   ((REPEAT STRIP_TAC) THEN
      (ONCE_REWRITE_TAC [lem17]) THEN (ONCE_REWRITE_TAC [SOD_SOD_DIFF_LEMMA]) THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval replay PLANETMATH_EQN_1_1_2

def PLANETMATH_EQN_1_1_3 : thm := keep "PLANETMATH_EQN_1_1_3" fun _ => (do
  prove ([[! x f.((Phi f) diffl (-- (exp (--x)) * (poly f x)))(x)]])
   ((ONCE_REWRITE_TAC [(← HolLight.GSYM PLANETMATH_EQN_1_1_2)]) THEN (ACCEPT_TAC PLANETMATH_EQN_1_1_1))
  : ExceptT String IO thm).run
#eval replay PLANETMATH_EQN_1_1_3

def PHI_CONTL : thm := keep "PHI_CONTL" fun _ => (do
  let lem0 ← HolLight.SPECL [([[Phi f]]), ([[-- (exp (--x)) * (poly f x)]]), ([[x:real]])] DIFF_CONT
  HolLight.GEN_ALL (← HolLight.MP lem0 (← HolLight.SPEC_ALL PLANETMATH_EQN_1_1_3))
  : ExceptT String IO thm).run
#eval replay PHI_CONTL

def PHI_DIFFERENTIABLE : thm := keep "PHI_DIFFERENTIABLE" fun _ => (do
  prove ([[!f x.(Phi f) differentiable x]])
   ((SIMP_TAC [differentiable]) THEN (REPEAT STRIP_TAC) THEN
      (EXISTS_TAC ([[((exp (--x)) * ((poly (poly_diff (SOD f)) x) - (poly (SOD f) x)))]])) THEN (SIMP_TAC [PLANETMATH_EQN_1_1_1]))
  : ExceptT String IO thm).run
#eval replay PHI_DIFFERENTIABLE

def PLANETMATH_EQN_1_2 : thm := keep "PLANETMATH_EQN_1_2" fun _ => (do
  let FO_LEMMA2 ← HolLight.GEN_ALL (← prove ([[((! l z. (C (l:real) (z:real)) ==> l = (l' z))) ==> ((? (l:real) (z:real) .(A z) /\ (B  z) /\ (C l z) /\ (D l) ) ==> (? (z:real).((A z) /\ (B z) /\ (D (l' z)))))]])
     (HolLight.tactic_of do
        let lem0 ← (prove ([[(! (l:real) z.(C l (z:real)) ==> l = (l' z)) ==> ((C l z) = ((C l z) /\ l = (l' z)))]])
     (MESON_TAC []))
        pure (HolLight.tactic_of do
        let lem1 ← HolLight.UNDISCH lem0
        pure ((STRIP_TAC THEN (ONCE_REWRITE_TAC [lem1]) THEN (MESON_TAC []))))))
  let PROP_LEMMA ← tt (← ExceptT.mk [[! a b c d.((a /\ b /\ c) ==> d) = (b ==> c ==> a ==> d)]])
  let MVT_SPEC ← HolLight.SPECL [([[Phi f]]), ([[&0]]), ([[x:real]])] MVT
  let MVT_SPEC2 ← HolLight.ONCE_REWRITE_RULE [PROP_LEMMA] MVT_SPEC
  let MVT_SPEC3 ← HolLight.UNDISCH MVT_SPEC2
  let MVT_SPEC4 ← HolLight.UNDISCH MVT_SPEC3
  let MVT_SPEC5 ← HolLight.UNDISCH MVT_SPEC4
  let lem0 ← prove ([[! x. x - &0 = x]])
     (REAL_ARITH_TAC2)
  let MVT_SPEC6 ← HolLight.ONCE_REWRITE_RULE [lem0] MVT_SPEC5
  let DIFF_UNIQ_SPEC1 ← HolLight.SPEC ([[Phi f]]) DIFF_UNIQ
  let DIFF_UNIQ_SPEC2 ← HolLight.SPEC ([[l:real]]) DIFF_UNIQ_SPEC1
  let DIFF_UNIQ_SPEC3 ← HolLight.SPEC ([[ (-- (exp (--x)) * (poly f x)) ]]) DIFF_UNIQ_SPEC2
  let DIFF_UNIQ_SPEC4 ← HolLight.SPEC ([[x:real]]) DIFF_UNIQ_SPEC3
  let lem8 ← ExceptT.mk (Session.SIMP_RULE [PLANETMATH_EQN_1_1_3] DIFF_UNIQ_SPEC4)
  let lem9 ← HolLight.GENL [([[l:real]]), ([[x:real]])] lem8
  let lem10 ← HolLight.SPECL [([[\l x.((Phi f diffl l) x)]]), ([[\z.(&0)<z]]), ([[\z.z < (x:real)]]), ([[\l. (Phi f x) - (Phi f (&0)) = x * l]])] FO_LEMMA2
  let lem12 ← HolLight.SPEC ([[\x.(--(exp (--x))) * (poly f x)]]) lem10
  let lem13 ← HolLight.BETA_RULE lem12
  let lem14 ← HolLight.MP lem13 lem9
  let lem15 ← HolLight.MP lem14 MVT_SPEC6
  let lem70 ← HolLight.SPECL [([[f:(real)list]]), ([[x':real]])] PHI_DIFFERENTIABLE
  let lem71 ← HolLight.ADD_ASSUM ([[(&0) < x' /\ x' < x]]) lem70
  let lem72 ← HolLight.GEN ([[x':real]]) (← HolLight.DISCH_ALL lem71)
  let lem73 ← HolLight.MP (← HolLight.DISCH (concl lem72) lem15) lem72
  let lem80 ← HolLight.SPECL [([[f:(real)list]]), ([[x':real]])] PHI_CONTL
  let lem81 ← HolLight.ADD_ASSUM ([[(&0) <= x' /\ x' <= x]]) lem80
  let lem82 ← HolLight.GEN ([[x':real]]) (← HolLight.DISCH_ALL lem81)
  let lem83 ← HolLight.MP (← HolLight.DISCH (concl lem82) lem73) lem82
  pure (lem83)
  : ExceptT String IO thm).run
#eval replay PLANETMATH_EQN_1_2

def xi_DEF : thm := keep "xi_DEF" fun _ => (do
  let FO_LEM ← prove ([[  (! x f.(P x) ==> ? z. (Q z x f))
          = (! (x:real) (f:(real)list). ? (z:real). (P x) ==> (Q z x f))]])
     (MESON_TAC [])
  ExceptT.mk (Session.new_specification ["xi"] (← HolLight.CONV_RULE SKOLEM_CONV (← HolLight.ONCE_REWRITE_RULE [FO_LEM] (← HolLight.GEN_ALL (← HolLight.DISCH_ALL PLANETMATH_EQN_1_2)))))
  : ExceptT String IO thm).run
#eval replay xi_DEF

def PLANETMATH_LEMMA_1 : thm := keep "PLANETMATH_LEMMA_1" fun _ => (do
  let lemA ← HolLight.CONJUNCT2 (← HolLight.CONJUNCT2 (← HolLight.UNDISCH (← HolLight.SPEC_ALL xi_DEF)))
  let lemB ← HolLight.ONCE_REWRITE_RULE [PHI] lemA
  let lemC ← HolLight.ONCE_REWRITE_RULE [(← rr (← ExceptT.mk [[((A:real) - B = C) = (B = A - C)]]))] lemB
  let lemD ← ExceptT.mk (Session.SIMP_RULE [SessionLibrary.Analysis.REAL_NEG_0, REAL_EXP_0, REAL_MUL_LID] lemC)
  let lem01 ← HolLight.ASSUME ([[A = ((exp (-- x))*B - (C *( -- (exp (-- y))) * D))]])
  let lem02 ← HolLight.DISJ2 ([[exp x = &0]]) lem01
  let lem03 ← HolLight.REWRITE_RULE [(← HolLight.GSYM (← HolLight.SPEC ([[exp x]]) REAL_EQ_MUL_LCANCEL))] lem02
  let lem04 ← ExceptT.mk (Session.SIMP_RULE [REAL_EXP_NEG_MUL, REAL_EXP_ADD_MUL] lem03)
  let lem05 ← ExceptT.mk (Session.SIMP_RULE [SessionLibrary.Analysis.REAL_SUB_LDISTRIB] lem04)
  let lem07 ← ExceptT.mk (Session.SIMP_RULE [REAL_MUL_ASSOC, REAL_EXP_NEG_MUL, REAL_MUL_LID] lem05)
  let fact00 ← rr (← ExceptT.mk [[(B:real) - ((expx * C) * (--expy))  * D = B + C * (expx * expy) * D]])
  let lem08 ← HolLight.ONCE_REWRITE_RULE [fact00] lem07
  let lem09 ← ExceptT.mk (Session.SIMP_RULE [(← HolLight.GSYM REAL_EXP_ADD)] lem08)
  let lem10 ← ExceptT.mk (Session.SIMP_RULE [(← prove ([[(x:real) + -- y =  x - y]])
     (REAL_ARITH_TAC2))] lem09)
  let lem11 ← HolLight.GEN_ALL (← HolLight.DISCH_ALL lem10)
  let lem12 ← HolLight.SPECL [([[poly (SOD f) (&0)]]),
                         ([[poly (SOD f) x]]),
                         ([[x:real]]),
                         ([[x:real]]),
                         ([[xi x f]]),
                         ([[poly f (xi x f)]])] lem11
  let lem13 ← HolLight.MP lem12 lemD
  let lem14 ← HolLight.SPECL [([[exp x]]), ([[poly (SOD f) (&0)]])] REAL_MUL_SYM
  prove ([[!x f.  &0 < x
            ==> poly (SOD f) (&0) * exp x =
                poly (SOD f) x + x * exp (x - xi x f) * poly f (xi x f)]])
   (ACCEPT_TAC (← HolLight.GEN_ALL (← HolLight.DISCH_ALL (← HolLight.ONCE_REWRITE_RULE [lem14] lem13))))
  : ExceptT String IO thm).run
#eval replay PLANETMATH_LEMMA_1

#eval (do
  replay PDI_DEF
  replay PDI_POLY_DIFF_COMM
  replay SODN
  replay SOD
  replay PHI
  replay PLANETMATH_EQN_1_1_1
  replay POLY_SUB
  replay ZERO_INSERT_NUMSEG
  replay PDI_POLYDIFF_SUC_LEMMA
  replay SOD_POLY_DIFF_ITERATE
  replay ZERO_ITERATE_POLYADD_LEMMA
  replay SOD_SOD_POLYDIFF
  replay SUC_INSERT_NUMSEG
  replay SUC_NOT_IN_NUMSEG
  replay SUC_ITERATE_PDI_POLYDIFF_LEMMA
  replay SODN_POLY_DIFF_COMM
  replay SUC_ITERATE_POLYADD_LEMMA
  replay NUMSEG_LENGTH_POLYDIFF_LEMMA
  replay POLY_DIFF_LENGTH_LT
  replay POLY_DIFF_LENGTH_LE_SUC
  replay PDI_LENGTH_AUX
  replay PDI_LENGTH_NIL
  replay SOD_POLYDIFF_THEOREM
  replay SOD_SOD_DIFF_LEMMA
  replay PLANETMATH_EQN_1_1_2
  replay PLANETMATH_EQN_1_1_3
  replay PHI_CONTL
  replay PHI_DIFFERENTIABLE
  replay PLANETMATH_EQN_1_2
  replay xi_DEF
  replay PLANETMATH_LEMMA_1
  IO.println "module Pm_lemma1 :\n  sig\n    val PDI_DEF : thm\n    val PDI_POLY_DIFF_COMM : thm\n    val SODN : thm\n    val SOD : thm\n    val PHI : thm\n    val PLANETMATH_EQN_1_1_1 : thm\n    val POLY_SUB : thm\n    val ZERO_INSERT_NUMSEG : thm\n    val PDI_POLYDIFF_SUC_LEMMA : thm\n    val SOD_POLY_DIFF_ITERATE : thm\n    val ZERO_ITERATE_POLYADD_LEMMA : thm\n    val SOD_SOD_POLYDIFF : thm\n    val SUC_INSERT_NUMSEG : thm\n    val SUC_NOT_IN_NUMSEG : thm\n    val SUC_ITERATE_PDI_POLYDIFF_LEMMA : thm\n    val SODN_POLY_DIFF_COMM : thm\n    val SUC_ITERATE_POLYADD_LEMMA : thm\n    val NUMSEG_LENGTH_POLYDIFF_LEMMA : thm\n    val POLY_DIFF_LENGTH_LT : thm\n    val POLY_DIFF_LENGTH_LE_SUC : thm\n    val PDI_LENGTH_AUX : thm\n    val PDI_LENGTH_NIL : thm\n    val SOD_POLYDIFF_THEOREM : thm\n    val SOD_SOD_DIFF_LEMMA : thm\n    val PLANETMATH_EQN_1_1_2 : thm\n    val PLANETMATH_EQN_1_1_3 : thm\n    val PHI_CONTL : thm\n    val PHI_DIFFERENTIABLE : thm\n    val PLANETMATH_EQN_1_2 : thm\n    val xi_DEF : thm\n    val PLANETMATH_LEMMA_1 : thm\n   end" : IO Unit)
end Pm_lemma1

#eval phrase 23
namespace Pm_lemma2
def POLY_MCLAURIN : thm := keep "POLY_MCLAURIN" fun _ => (do
  let lem002 ← HolLight.SPECL [([[poly p]]), ([[\n.poly (poly_diff_iter p n)]])] MCLAURIN_ALL_LE
  let lem003 ← ExceptT.mk (Session.SIMP_RULE [Pm_lemma1.PDI_DEF, POLY_DIFF] lem002)
  let lem004 ← HolLight.REWRITE_RULE [(← ec (Session.ETA_CONV ([[(\x.poly l x)]])))] POLY_DIFF
  let lem005 ← HolLight.MATCH_MP lem003 (← HolLight.GEN ([[m:num]]) (← HolLight.SPECL [([[poly_diff_iter p m]])] lem004))
  let lem007 ← HolLight.SPECL [([[x:real]]), ([[LENGTH (p:(real)list)]])] lem005
  let lem008 ← HolLight.ONCE_REWRITE_RULE [Pm_lemma1.PDI_LENGTH_NIL] lem007
  let lem009 ← HolLight.ONCE_REWRITE_RULE [poly] lem008
  let lem010 ← ExceptT.mk (Session.SIMP_RULE [(← rr (← ExceptT.mk [[!x. ((&0)/x) = &0]]))] lem009)
  let lem011 ← ExceptT.mk (Session.SIMP_RULE [SessionLibrary.Analysis.REAL_MUL_LZERO, REAL_ADD_RID] lem010)
  let lem012 ← prove ([[(? t . (A t) /\ B) ==> B]])
     (MESON_TAC [])
  prove ([[! p x. poly p x =
            psum (0, LENGTH p) (\m.poly (poly_diff_iter p m) (&0) / &(FACT m) * x pow m)]])
   (ACCEPT_TAC (← HolLight.GEN_ALL (← HolLight.MATCH_MP lem012 lem011)))
  : ExceptT String IO thm).run
#eval replay POLY_MCLAURIN

def DIFF_ADD_CONST_COMMUTE : thm := keep "DIFF_ADD_CONST_COMMUTE" fun _ => (do
  let lem01 ← HolLight.CONJ (← HolLight.SPEC_ALL DIFF_X) (← HolLight.SPECL [([[a:real]]), ([[x:real]])] DIFF_CONST)
  let lem02 ← HolLight.BETA_RULE (← HolLight.MATCH_MP DIFF_ADD lem01)
  let lem03 ← HolLight.ONCE_REWRITE_RULE [(← rr (← ExceptT.mk [[&1 + &0 = &1]]))] lem02
  let lem04 ← HolLight.SPECL [([[f:real->real]]), ([[\(x:real).((x + a)):real]]), ([[l:real]]), ([[&1]])] DIFF_CHAIN
  let MUL_ONE ← rr (← ExceptT.mk [[! x.(&1) * x = x /\ x * (&1) = x]])
  let lem05 ← HolLight.ONCE_REWRITE_RULE [MUL_ONE] (← HolLight.BETA_RULE lem04)
  let lem06 ← HolLight.GEN_ALL (← ExceptT.mk (Session.SIMP_RULE [lem03] lem05))
  prove ([[!f a l x . (f diffl l) (x + a) ==> ((\x. f (x + a)) diffl l) x]])
   (ACCEPT_TAC lem06)
  : ExceptT String IO thm).run
#eval replay DIFF_ADD_CONST_COMMUTE

def POLY_DIFF_ADD_CONST_COMMUTE : thm := keep "POLY_DIFF_ADD_CONST_COMMUTE" fun _ => (do
  let lem01 ← HolLight.SPECL [([[\x.poly p1 x]]), ([[-- a:real]]), ([[l:real]]), ([[x:real]])] DIFF_ADD_CONST_COMMUTE
  let lem02 ← HolLight.ONCE_REWRITE_RULE [(← rr (← ExceptT.mk [[w + --v = w - v]]))] (← HolLight.BETA_RULE lem01)
  let lem03 ← HolLight.SPECL [([[p1:(real)list]]), ([[(x:real) -a]])] POLY_DIFF
  let lem04 ← HolLight.MATCH_MP lem02 lem03
  let lem05 ← HolLight.ASSUME ([[!x.poly p2 x = poly p1 (x - a)]])
  let lem06 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM lem05)] lem04
  let lem07 ← HolLight.SPECL [([[p2:(real)list]]), ([[x:real]])] POLY_DIFF
  let lem08 ← HolLight.MATCH_MP DIFF_UNIQ (← HolLight.CONJ lem07 lem06)
  prove ([[! p1 p2 a.(!x.(poly p2 x) = (poly p1 (x-a)))
            ==> (!x . ((poly (poly_diff p2) x) = (poly (poly_diff p1) (x-a))))]])
   ((REPEAT STRIP_TAC) THEN (ACCEPT_TAC lem08))
  : ExceptT String IO thm).run
#eval replay POLY_DIFF_ADD_CONST_COMMUTE

def HARD_WON : thm := keep "HARD_WON" fun _ => (do
  let lem ← HolLight.SPECL [([[poly_diff_iter p1 n]]), ([[poly_diff_iter p2 n]]), ([[a:real]])] POLY_DIFF_ADD_CONST_COMMUTE
  let tm := ([[(!x . poly p2 x = poly p1 (x -a )) ==>
                   (\x.poly (poly_diff_iter p2 n) x) = (\x. poly (poly_diff_iter p1 n) (x - a))]])
  prove ([[! p1 p2 a n.(!x.(poly p2 x) = (poly p1 (x-a)))
            ==> ((\x.poly (poly_diff_iter p2 n) x) = (\x.(poly (poly_diff_iter p1 n) (x - a)))) ]])
   ((STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC) THEN
      INDUCT_TAC THENL
      [SIMP_TAC [Pm_lemma1.PDI_DEF],
        STRIP_TAC THEN (ONCE_REWRITE_TAC [Pm_lemma1.PDI_DEF]) THEN (UNDISCH_TAC tm) THEN
        (ASM_REWRITE_TAC [FUN_EQ_THM]) THEN (ACCEPT_TAC lem)])
  : ExceptT String IO thm).run
#eval replay HARD_WON

def POLY_SHIFT_DEF : thm := keep "POLY_SHIFT_DEF" fun _ => (do
  ExceptT.mk (Session.new_recursive_definition list_RECURSION ([[   (poly_shift [] a = [])
                /\ (poly_shift (CONS c t) a =
                   (CONS c (poly_shift t a)) ++ (a ## (poly_shift t a)))]]))
  : ExceptT String IO thm).run
#eval replay POLY_SHIFT_DEF

def POLY_SHIFT : thm := keep "POLY_SHIFT" fun _ => (do
  let lem01 ← HolLight.ASSUME ([[! a x . poly  t (x + a) = poly (poly_shift t a ) x]])
  prove ([[! p a x .(poly p (x + a)) = (poly (poly_shift p a) x)]])
   (LIST_INDUCT_TAC THENL
      [(ONCE_REWRITE_TAC [POLY_SHIFT_DEF, poly]) THEN (SIMP_TAC [poly]),
       (REPEAT STRIP_TAC) THEN (ONCE_REWRITE_TAC [POLY_SHIFT_DEF]) THEN
       (ONCE_REWRITE_TAC [POLY_ADD]) THEN (ONCE_REWRITE_TAC [POLY_CMUL]) THEN
       (ONCE_REWRITE_TAC [poly, (← HolLight.GSYM lem01)]) THEN
       (ONCE_REWRITE_TAC [(← HolLight.GSYM lem01)]) THEN REAL_ARITH_TAC2])
  : ExceptT String IO thm).run
#eval replay POLY_SHIFT

def POLY_SHIFT_LENGTH : thm := keep "POLY_SHIFT_LENGTH" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[! n. SUC n >n]])
  let h1 ← ar (← ExceptT.mk [[MAX (x:num) y = if (x > y) then x else y]])
  prove ([[! p a . (LENGTH (poly_shift p a)) = (LENGTH p)]])
   (LIST_INDUCT_TAC THENL
      [(SIMP_TAC [POLY_SHIFT_DEF]),
        (SIMP_TAC [POLY_SHIFT_DEF]) THEN
        (ASM_SIMP_TAC [Session.listDefs.LENGTH, POLY_CMUL_LENGTH, POLY_ADD_LENGTH,
           h1,
           h2])])
  : ExceptT String IO thm).run
#eval replay POLY_SHIFT_LENGTH

def POLY_TAYLOR : thm := keep "POLY_TAYLOR" fun _ => (do
  let lem01 ← HolLight.SPEC ([[poly_shift p a]]) POLY_MCLAURIN
  let lem02 ← HolLight.SPECL [([[p:(real)list]]), ([[poly_shift p a]]), ([[-- a:real]]), ([[n:num]])] HARD_WON
  let lem03 ← HolLight.GSYM (← HolLight.SPECL [([[p:(real)list]]), ([[a:real]])] POLY_SHIFT)
  let lem04 ← ExceptT.mk (Session.SIMP_RULE [(← rr (← ExceptT.mk [[a - --b = a + b]]))] lem02)
  let lem05 ← HolLight.ONCE_REWRITE_RULE [ETA_AX] (← HolLight.MP lem04 lem03)
  let lem06 ← HolLight.BETA_RULE (← HolLight.ONCE_REWRITE_RULE [lem05] lem01)
  let lem07 ← HolLight.ONCE_REWRITE_RULE [(← rr (← ExceptT.mk [[&0 + a = a]]))] lem06
  let lem08 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM POLY_SHIFT)] lem07
  let lem09 ← HolLight.ONCE_REWRITE_RULE [POLY_SHIFT_LENGTH] lem08
  let lem10 := HolLight.RATOR_CONV (HolLight.ONCE_REWRITE_CONV [(← rr (← ExceptT.mk [[(x:real) = (x + a) - a]]))]) ([[x pow m]])
  let lem11 ← HolLight.ONCE_REWRITE_RULE [lem10] lem09
  let lem12 ← HolLight.SPEC ([[(x - a):real]]) lem11
  let lem13 ← HolLight.ONCE_REWRITE_RULE [(← rr (← ExceptT.mk [[(x:real) - a + a = x]]))] lem12
  prove ([[! p x a. poly p x =
              psum (0,LENGTH p) (\m.poly (poly_diff_iter p m) a/ &(FACT m) * (x - a) pow m)]])
   (ACCEPT_TAC (← HolLight.GEN_ALL lem13))
  : ExceptT String IO thm).run
#eval replay POLY_TAYLOR

def PLANETMATH_LEMMA_2_A : thm := keep "PLANETMATH_LEMMA_2_A" fun _ => (do
  prove ([[! p a x . poly p x =
       ((\s .psum (0,LENGTH p) ((\m.poly (poly_diff_iter p m) a/ &(FACT m) * (s m))))
         (\m.(x - a) pow m))]])
   (BETA_TAC THEN (MATCH_ACCEPT_TAC POLY_TAYLOR))
  : ExceptT String IO thm).run
#eval replay PLANETMATH_LEMMA_2_A

def ITERATE_SUC_REC : thm := keep "ITERATE_SUC_REC" fun _ => (do
  let lem0 ← HolLight.UNDISCH_ALL (← HolLight.SPEC_ALL (← HolLight.GSYM NUMSEG_REC))
  let lem1 ← HolLight.ISPEC ([[op:D -> D -> D]]) ITERATE_CLAUSES_GEN
  let lem2 ← HolLight.CONJUNCT2 (← HolLight.UNDISCH lem1)
  let lem3 ← HolLight.ISPECL [([[f:(num -> D)]]), ([[SUC n]]), ([[m..n]])] lem2
  let lem4 ← ExceptT.mk (Session.SIMP_RULE [] (← HolLight.DISCH_ALL lem3))
  let lem50 ← prove ([[!m n. ~((SUC n) IN (m..n))]])
     (STRIP_TAC THEN (ONCE_REWRITE_TAC [IN_NUMSEG]) THEN ARITH_TAC)
  let lem5 ← ExceptT.mk (Session.SIMP_RULE [lem50, FINITE_SUPPORT, FINITE_NUMSEG] lem4)
  let lem6 ← HolLight.ADD_ASSUM ([[m <= SUC n]]) lem5
  let lem7 ← HolLight.ONCE_REWRITE_RULE [lem0] lem6
  prove ([[!(op:D -> D -> D) m n (f:num -> D) .
              monoidal op ==>
              (m <= SUC n) ==>
              iterate op (m..(SUC n)) f
               = op (f (SUC n)) (iterate op (m..n) f)]])
   (SIMP_TAC [lem7])
  : ExceptT String IO thm).run
#eval replay ITERATE_SUC_REC

#eval phrase 24
def ITERATE_POLY_ADD_PRE_REC : thm := keep "ITERATE_POLY_ADD_PRE_REC" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[n > 0 ==> n = SUC (n - 1)]])
  let h1 ← ar (← ExceptT.mk [[0 <= x]])
  prove ([[!f n . n > 0
        ==> iterate (++) (0..n) f = (f n) ++ (iterate (++) (0..n-1) f)]])
   (MESON_TAC [ITERATE_CLAUSES_NUMSEG, MONOIDAL_POLY_ADD, POLY_ADD_SYM,
                 h1, h2])
  : ExceptT String IO thm).run
#eval replay ITERATE_POLY_ADD_PRE_REC

#eval phrase 25
def PSUM_ITERATE : thm := keep "PSUM_ITERATE" fun _ => (do
  let lem01 ← ar (← ExceptT.mk [[~(n+m=0) ==> (SUC n + m) -1 = SUC ((n + m) -1)]])
  let lem02 ← HolLight.MP (← HolLight.ISPEC ([[(+)]]) ITERATE_SING) MONOIDAL_REAL_ADD
  let lem03 ← prove ([[iterate (+) (m..SUC ((n + m) - 1)) f
           = f (SUC ((n+m)-1)) + iterate (+) (m..(n+m)-1) f]])
     (MESON_TAC [(← ar (← ExceptT.mk [[m <= SUC ((n+m)-1)]])), ITERATE_CLAUSES_NUMSEG,
                        MONOIDAL_REAL_ADD, REAL_ADD_SYM])
  let lem04 ← HolLight.UNDISCH (← HolLight.UNDISCH (← ar (← ExceptT.mk [[~(n+m=0) ==> n=0 ==> m-1 < m]])))
  let lem05 ← ExceptT.mk (Session.SIMP_RULE [lem04] (← HolLight.SPECL [([[m:num]]), ([[m-1]])] NUMSEG_EMPTY))
  let h7 ← ar (← ExceptT.mk [[~(n=0) ==> n>0 /\ SUC (n-1) = n]])
  let h6 ← ar (← ExceptT.mk [[~(0 > 0)]])
  let h5 ← rr (← ExceptT.mk [[&0 + x = x]])
  let h4 ← ar (← ExceptT.mk [[(SUC 0 +m) -1 = m]])
  let h3 ← ar (← ExceptT.mk [[n + m = 0 ==> n = 0]])
  let h2 ← ar (← ExceptT.mk [[(SUC n) > 0]])
  let h1 ← ar (← ExceptT.mk [[~(0 > 0)]])
  prove ([[! n m f. psum (m,n) f
              = if (n > 0) then (iterate (+) (m..((n+m)-1)) f) else &0]])
   (INDUCT_TAC THENL
      [SIMP_TAC [h1, sum_DEF],
        (SIMP_TAC [h2]) THEN (REPEAT STRIP_TAC) THEN
        (ASM_CASES_TAC ([[n + m =0]])) THENL
        [(REWRITE_TAC [(← HolLight.UNDISCH h3)]) THEN
          (REWRITE_TAC [lem02, NUMSEG_SING, h4]) THEN
          (MESON_TAC [sum_DEF, ADD_CLAUSES, h5]),
          (ONCE_REWRITE_TAC [sum_DEF, (← HolLight.UNDISCH lem01)]) THEN
          (REWRITE_TAC [lem03]) THEN (ASM_CASES_TAC ([[n = 0]])) THEN
          (ASM_SIMP_TAC [h6, ADD_CLAUSES, REAL_ADD_LID, REAL_ADD_RID,
             lem05, ITERATE_CLAUSES_GEN, MONOIDAL_REAL_ADD, NEUTRAL_REAL_ADD,
             REAL_ADD_SYM, ADD_SYM, h7])]])
  : ExceptT String IO thm).run
#eval replay PSUM_ITERATE

#eval phrase 26
def FACT_DIV_RCANCELS : thm := keep "FACT_DIV_RCANCELS" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[!x. &0 < x ==> ~(x = &0)]])
  prove ([[!n x. x / &(FACT n) * &(FACT n) = x]])
   (MESON_TAC [h1,
                 REAL_DIV_RMUL, FACT_LT, REAL_OF_NUM_LT])
  : ExceptT String IO thm).run
#eval replay FACT_DIV_RCANCELS

def PLANETMATH_LEMMA_2_B : thm := keep "PLANETMATH_LEMMA_2_B" fun _ => (do
  let lem6 ← HolLight.ISPECL [([[(\i.poly_diff_iter p i)]]), ([[LENGTH (p:(real)list)]])] ITERATE_POLY_ADD_PRE_REC
  let lem7 ← HolLight.UNDISCH lem6
  let lem8 ← HolLight.UNDISCH (← ar (← ExceptT.mk [[~(LENGTH (p:(real)list) > 0) ==> (LENGTH p = 0)]]))
  let lem9 ← HolLight.ONCE_REWRITE_RULE [Session.listThms1.LENGTH_EQ_NIL] lem8
  let h1 ← ar (← ExceptT.mk [[x + 0 = x]])
  prove ([[! p (x:real) a . poly (SOD p) a =
       ((\s .psum (0,LENGTH p) ((\m.poly (poly_diff_iter p m) a/ &(FACT m) * (s m))))
         (\m. &(FACT m)))]])
   (BETA_TAC THEN (REPEAT STRIP_TAC) THEN (ONCE_REWRITE_TAC [FACT_DIV_RCANCELS]) THEN
      (ONCE_REWRITE_TAC [PSUM_ITERATE]) THEN (ASM_CASES_TAC ([[LENGTH (p:(real)list) > 0]])) THENL
      [(ASM_SIMP_TAC [Pm_lemma1.SOD, Pm_lemma1.SODN, ITERATE_RADD_POLYADD, h1]) THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN (SIMP_TAC [lem7, Pm_lemma1.PDI_LENGTH_NIL, POLY_ADD_CLAUSES]),
        (ASM_SIMP_TAC []) THEN
        (SIMP_TAC [lem9, poly, Pm_lemma1.SOD, Pm_lemma1.SODN, NUMSEG_SING, MONOIDAL_POLY_ADD, ITERATE_SING, Session.listDefs.LENGTH, Pm_lemma1.PDI_DEF])])
  : ExceptT String IO thm).run
#eval replay PLANETMATH_LEMMA_2_B

#eval (do
  replay POLY_MCLAURIN
  replay DIFF_ADD_CONST_COMMUTE
  replay POLY_DIFF_ADD_CONST_COMMUTE
  replay HARD_WON
  replay POLY_SHIFT_DEF
  replay POLY_SHIFT
  replay POLY_SHIFT_LENGTH
  replay POLY_TAYLOR
  replay PLANETMATH_LEMMA_2_A
  replay ITERATE_SUC_REC
  replay ITERATE_POLY_ADD_PRE_REC
  replay PSUM_ITERATE
  replay FACT_DIV_RCANCELS
  replay PLANETMATH_LEMMA_2_B
  IO.println "module Pm_lemma2 :\n  sig\n    val POLY_MCLAURIN : thm\n    val DIFF_ADD_CONST_COMMUTE : thm\n    val POLY_DIFF_ADD_CONST_COMMUTE : thm\n    val HARD_WON : thm\n    val POLY_SHIFT_DEF : thm\n    val POLY_SHIFT : thm\n    val POLY_SHIFT_LENGTH : thm\n    val POLY_TAYLOR : thm\n    val PLANETMATH_LEMMA_2_A : thm\n    val ITERATE_SUC_REC : thm\n    val ITERATE_POLY_ADD_PRE_REC : thm\n    val PSUM_ITERATE : thm\n    val FACT_DIV_RCANCELS : thm\n    val PLANETMATH_LEMMA_2_B : thm\n   end" : IO Unit)
end Pm_lemma2

#eval phrase 27
namespace Pm_eqn4
def N_IS_INT : thm := keep "N_IS_INT" fun _ => (do
  prove ([[!n . integer (&n)]])
   (MESON_TAC [is_int])
  : ExceptT String IO thm).run
#eval replay N_IS_INT

def NEG_N_IS_INT : thm := keep "NEG_N_IS_INT" fun _ => (do
  prove ([[!n . integer (--(&n))]])
   (MESON_TAC [is_int])
  : ExceptT String IO thm).run
#eval replay NEG_N_IS_INT

#eval phrase 28
def PLANETMATH_EQN_3 : thm := keep "PLANETMATH_EQN_3" fun _ => (do
  let RW ← HolLight.SPECL [([[0]]), ([[nu:num]])] REAL_OF_NUM_LT
  prove ([[!f. 0 < nu
          ==> poly (SOD f) (&0) * exp (&nu) =
              poly (SOD f) (&nu) +
              &nu * exp (&nu - xi (&nu) f) * poly f (xi (&nu) f)]])
   (ACCEPT_TAC (← HolLight.ONCE_REWRITE_RULE [RW] (← HolLight.SPEC ([[(&nu):real]]) Pm_lemma1.PLANETMATH_LEMMA_1)))
  : ExceptT String IO thm).run
#eval replay PLANETMATH_EQN_3

def LHS : thm := keep "LHS" fun _ => new_definition
 [[LHS c f = sum (0..(PRE (LENGTH c))) (\i.(EL i c)*(poly (SOD f) (&i)))]]
#eval replay LHS

def RHS : thm := keep "RHS" fun _ => new_definition
 [[RHS  c f = -- sum (1..(PRE (LENGTH c)) )
                          (\i.  (&i)
                              * (EL i c)
                              * (exp ((&i) - (xi (&i) f)))
                              * (poly f (xi (&i) f))
                          )]]
#eval replay RHS

def E_POW_N : thm := keep "E_POW_N" fun _ => (do
  prove ([[!n.(exp (real_of_num 1)) pow n = exp(&n)]])
   (SIMP_TAC [(← HolLight.GSYM REAL_EXP_N), SessionLibrary.Analysis.REAL_MUL_RID])
  : ExceptT String IO thm).run
#eval replay E_POW_N

def NO_CONST_TERM_POLY_ROOT : thm := keep "NO_CONST_TERM_POLY_ROOT" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[((&0):real) + x = x]])
  prove ([[!p . (~(x = &0) /\ ((HD p) = &0) /\ (poly p x = &0) /\ ~(p = []))
           ==> ((poly (TL p) x) = &0)]])
   (LIST_INDUCT_TAC THEN
      (ASM_SIMP_TAC [Session.listDefs.HD, Session.listDefs.TL, Session.listThms1.NOT_CONS_NIL, poly]) THEN
      (MESON_TAC [h1, REAL_ENTIRE]))
  : ExceptT String IO thm).run
#eval replay NO_CONST_TERM_POLY_ROOT

def NEGATED_POLY_ROOT : thm := keep "NEGATED_POLY_ROOT" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[(-- &1) * ((&0):real) = &0]])
  prove ([[!p . (poly p x = &0) ==> (poly ((-- &1) ## p) x = &0)]])
   (MESON_TAC [POLY_CMUL, h1])
  : ExceptT String IO thm).run
#eval replay NEGATED_POLY_ROOT

def POLY_NUKE : thm := keep "POLY_NUKE" fun _ => (do
  ExceptT.mk (Session.new_recursive_definition list_RECURSION ([[   (poly_nuk [] = [])
                /\ (poly_nuk (CONS (c:real) t) =
                   (if (c = &0) then (poly_nuk t) else (CONS c t)))]]))
  : ExceptT String IO thm).run
#eval replay POLY_NUKE

def POLY_NUKE_ROOT : thm := keep "POLY_NUKE_ROOT" fun _ => (do
  prove ([[!p . ((~(x = &0)) /\ (poly p x = &0)) ==> (poly (poly_nuk p) x = &0)]])
   (LIST_INDUCT_TAC THENL
      [SIMP_TAC [POLY_NUKE],
        (ASM_CASES_TAC ([[(h:real) = &0]])) THEN
        (ASM_MESON_TAC [Session.listDefs.HD, Session.listDefs.TL, POLY_NUKE, Session.listThms1.NOT_CONS_NIL, NO_CONST_TERM_POLY_ROOT])])
  : ExceptT String IO thm).run
#eval replay POLY_NUKE_ROOT

def POLY_NUKE_ZERO : thm := keep "POLY_NUKE_ZERO" fun _ => (do
  prove ([[!p . (poly p = poly []) <=> (poly (poly_nuk p) = poly [])]])
   (LIST_INDUCT_TAC THEN (ASM_MESON_TAC [POLY_ZERO, Session.listDefs.ALL, POLY_NUKE]))
  : ExceptT String IO thm).run
#eval replay POLY_NUKE_ZERO

def POLY_CONST_NO_ROOTS : thm := keep "POLY_CONST_NO_ROOTS" fun _ => (do
  let h2 ← rr (← ExceptT.mk [[(x:real) * &0 = &0]])
  let h1 ← rr (← ExceptT.mk [[(x:real) + &0 = x]])
  prove ([[! c.  ~(poly [c] = poly []) ==> ~(poly [c] x = &0)]])
   ((MESON_TAC [poly, REAL_ENTIRE, POLY_ZERO, Session.listDefs.ALL,
                  h1,
                  h2]))
  : ExceptT String IO thm).run
#eval replay POLY_CONST_NO_ROOTS

def LENGTH_1 : thm := keep "LENGTH_1" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[SUC x = 1 <=> x = 0]])
  prove ([[! lst . (LENGTH lst = 1) <=> (? x. lst = [x])]])
   (LIST_INDUCT_TAC THEN
      (MESON_TAC [Session.listDefs.LENGTH, h1, Session.listThms1.NOT_CONS_NIL, Session.listThms1.LENGTH_EQ_NIL]))
  : ExceptT String IO thm).run
#eval replay LENGTH_1

def SOUP_LEMMA : thm := keep "SOUP_LEMMA" fun _ => (do
  let l0 ← ar (← ExceptT.mk [[(~(n = 0) /\ ~(n = 1)) <=> n > 1]])
  let l1 ← HolLight.UNDISCH (← HolLight.UNDISCH (← BRW1 (← HolLight.SPEC_ALL POLY_NUKE_ROOT)))
  prove ([[!p . ~(x = &0) /\ ~(poly p = poly []) /\ (poly p x = &0)
            ==> LENGTH (poly_nuk p) > 1]])
   ((ONCE_REWRITE_TAC [(← HolLight.GSYM l0)]) THEN (REPEAT STRIP_TAC) THENL
      [(ASM_MESON_TAC [Session.listDefs.LENGTH, Session.listThms1.LENGTH_EQ_NIL, POLY_NUKE_ZERO]),
        (ASM_MESON_TAC [l1, POLY_CONST_NO_ROOTS, LENGTH_1, Session.listDefs.LENGTH, POLY_NUKE_ZERO])])
  : ExceptT String IO thm).run
#eval replay SOUP_LEMMA

def POLY_NUKE_HD_NONZERO : thm := keep "POLY_NUKE_HD_NONZERO" fun _ => (do
  prove ([[!p . ~(poly p = poly []) ==> ~((HD (poly_nuk p)) = &0)]])
   (LIST_INDUCT_TAC THEN (ASM_CASES_TAC ([[(h:real) = &0]])) THEN
      (ASM_SIMP_TAC [Session.listDefs.HD, POLY_ZERO, Session.listDefs.ALL, POLY_NUKE]))
  : ExceptT String IO thm).run
#eval replay POLY_NUKE_HD_NONZERO

def IS_INT_POLY_NUKE : thm := keep "IS_INT_POLY_NUKE" fun _ => (do
  prove ([[!p . (ALL integer p) ==> (ALL integer (poly_nuk p))]])
   (LIST_INDUCT_TAC THEN (ASM_MESON_TAC [Session.listDefs.ALL, POLY_NUKE, N_IS_INT]))
  : ExceptT String IO thm).run
#eval replay IS_INT_POLY_NUKE

def POLY_X_NOT_POLY_NIL : thm := keep "POLY_X_NOT_POLY_NIL" fun _ => (do
  prove ([[~(poly [&0;&1] = poly [])]])
   ((SIMP_TAC [FUN_EQ_THM, POLY_X, poly, (← prove ([[(~ ! x .P x) <=> (? x. ~ P x)]])
     (MESON_TAC []))]) THEN (EXISTS_TAC ([[real_of_num 1]])) THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval replay POLY_X_NOT_POLY_NIL

def NOT_TRANSCENDENTAL_ZERO : thm := keep "NOT_TRANSCENDENTAL_ZERO" fun _ => (do
  prove ([[~ (transcendental (&0))]])
   ((REWRITE_TAC [transcendental, algebraic]) THEN
        (EXISTS_TAC ([[[&0 ; &1]:(real)list]])) THEN
        (MESON_TAC [POLY_X, POLY_X_NOT_POLY_NIL, Session.listDefs.ALL, N_IS_INT]))
  : ExceptT String IO thm).run
#eval replay NOT_TRANSCENDENTAL_ZERO

def ALL_IS_INT_POLY_CMUL : thm := keep "ALL_IS_INT_POLY_CMUL" fun _ => (do
  prove ([[! p c. (integer c) /\ (ALL integer p) ==> (ALL integer (c ## p))]])
   (LIST_INDUCT_TAC THEN (ASM_SIMP_TAC [poly_cmul, Session.listDefs.ALL, INTEGER_MUL]))
  : ExceptT String IO thm).run
#eval replay ALL_IS_INT_POLY_CMUL

def TRANSCENDENTAL_MY_TRANSCENDENTAL : thm := keep "TRANSCENDENTAL_MY_TRANSCENDENTAL" fun _ => (do
  let contra_pos ← tt (← ExceptT.mk [[(~X ==> ~Y /\ ~Z) <=> ((Y \/ Z) ==> X)]])
  let contra_pos2 ← tt (← ExceptT.mk [[((~X /\ ~Y) ==> ~Z) <=> (Z ==> ~X ==> Y)]])
  let l0 ← prove ([[!c . LENGTH c > 1 ==> HD c > &0 ==> ~(poly c = poly [])]])
     (LIST_INDUCT_TAC THEN
                     (ASM_MESON_TAC [Session.listThms1.LENGTH_EQ_NIL, (← ar (← ExceptT.mk [[n > 1 ==> ~(n = 0)]])),
                                     (← rr (← ExceptT.mk [[(x:real) > &0 ==> ~(x = &0)]])),
                                     Session.listDefs.HD, Session.listDefs.ALL, POLY_ZERO]))
  let witness := ([[if ((&0) <= (HD (poly_nuk p)))
                   then (poly_nuk p)
                   else ((-- &1) ## (poly_nuk p))]])
  let l2 ← rr (← ExceptT.mk [[!(x:real). (&0 <= x) /\ ~(x = &0) ==> x > &0]])
  let l3 ← prove ([[! c p. LENGTH (c ## p) =  LENGTH p]])
     (STRIP_TAC THEN LIST_INDUCT_TAC THEN
                      (ASM_SIMP_TAC [poly_cmul, Session.listDefs.LENGTH]))
  let POLY_CMUL_HD ← prove ([[! x p . (~(p = [])) ==> HD (x ## p) = x * (HD p)]])
     (STRIP_TAC THEN LIST_INDUCT_TAC THEN (SIMP_TAC [Session.listThms1.NOT_CONS_NIL, poly_cmul, Session.listDefs.HD]))
  let h1 ← rr (← ExceptT.mk [[~(&0 <= (x:real)) <=> ((-- &1) * x) > &0]])
  prove ([[!x. transcendental x <=>
         (~(x = &0) /\
             ~ ? c.     (ALL integer c)
                     /\ ((LENGTH c) > 1)
                     /\ ((poly c x) = &0)
                     /\ (HD c) > &0 )]])
   ((REWRITE_TAC [transcendental, algebraic]) THEN
      (STRIP_TAC THEN EQ_TAC) THENL
      [(ONCE_REWRITE_TAC [contra_pos]) THEN STRIP_TAC THENL
        [ASM_MESON_TAC [transcendental, algebraic, NOT_TRANSCENDENTAL_ZERO],
        (EXISTS_TAC ([[c:(real)list]])) THEN
        (ASM_MESON_TAC [l0, NOT_TRANSCENDENTAL_ZERO])],
        (REWRITE_TAC [contra_pos2]) THEN
        (STRIP_TAC THEN STRIP_TAC) THEN (ASM_SIMP_TAC [IS_INT_POLY_NUKE]) THEN
        (EXISTS_TAC witness) THEN
        (ASM_CASES_TAC ([[((&0) <= (HD (poly_nuk p)))]])) THEN
        (ASM_MESON_TAC [IS_INT_POLY_NUKE, ALL_IS_INT_POLY_CMUL, NEG_N_IS_INT,
                         l2, POLY_NUKE_HD_NONZERO, NEGATED_POLY_ROOT, SOUP_LEMMA,
                         l3, POLY_NUKE_ROOT, POLY_NUKE_ZERO, POLY_CMUL_HD,
                         h1])])
  : ExceptT String IO thm).run
#eval replay TRANSCENDENTAL_MY_TRANSCENDENTAL

def E_TRANSCENDENTAL_EQUIV : thm := keep "E_TRANSCENDENTAL_EQUIV" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[&0 < (x:real) ==> ~(&0 = x)]])
  prove ([[(transcendental (exp (&1))) <=>
     (~ ? c.  (ALL integer c)
           /\ ((LENGTH c) > 1)
           /\ ((poly c (exp (&1))) = &0)
           /\ (HD c) > &0 )]])
   (MESON_TAC [TRANSCENDENTAL_MY_TRANSCENDENTAL,
                REAL_EXP_POS_LT, h1])
  : ExceptT String IO thm).run
#eval replay E_TRANSCENDENTAL_EQUIV

def PLANETMATH_EQN_4 : thm := keep "PLANETMATH_EQN_4" fun _ => (do
  let foo2 ← prove ([[(HD c) > (real_of_num 0) ==> EL 0 c > &0]])
     (SIMP_TAC [Session.listDefs.EL])
  let lem01 ← HolLight.SPECL [([[f:num->real]]), ([[0]]), ([[0]]), ([[PRE (LENGTH (c:(real)list))]])] SUM_COMBINE_R
  let lem02 ← ar (← ExceptT.mk [[(0 <= 0 + 1 /\ 0 <= (PRE (LENGTH (c:(real)list))))]])
  let lem03 ← HolLight.GSYM (← HolLight.MP lem01 lem02)
  let lem06 ← HolLight.ISPECL [([[f1:num->real]]),
                           ([[f2:num->real]]),
                           ([[1]]), ([[(PRE (LENGTH (c:(real)list)))]])] SessionLibrary.Analysis.SUM_ADD
  let new0 ← HolLight.SPECL [([[f:num->real]]), ([[1]]), ([[PRE (LENGTH (c:(real)list))]])] PSUM_SUM_NUMSEG
  let new1 ← ExceptT.mk (Session.SIMP_RULE [(← ar (← ExceptT.mk [[~(1 = 0)]])), (← ar (← ExceptT.mk [[(1 + x) -1 = x]]))] new0)
  let new2 ← HolLight.ONCE_REWRITE_RULE [new1] lem06
  let lem001 ← rr (← ExceptT.mk [[((A:real) * B * C * D + B * E) = (B * (A * C * D + E))]])
  let lem0 ← rr (← ExceptT.mk [[(x:real) =  x * (&1) - (&0) * y]])
  let lem1 ← HolLight.GEN_ALL (← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM REAL_EXP_0)] lem0)
  let lem2 ← HolLight.SPECL [([[poly (SOD f) (&0)]]),
                         ([[ exp (&0 - xi (&0) f) * poly f (xi (&0) f)]])] lem1
  let PLANETMATH_EQN_3_TWEAKED ← HolLight.REWRITE_RULE [(← rr (← ExceptT.mk [[((A:real) = B+C) <=> (B = A -C)]]))] PLANETMATH_EQN_3
  let lem21 ← HolLight.GEN ([[nu:num]]) (← HolLight.SPEC_ALL PLANETMATH_EQN_3_TWEAKED)
  let lem3 ← HolLight.CONJ lem21 lem2
  let NUM_CASES_LEMMA ← prove ([[ !P .((! n .(0 < n) ==> (P n)) /\ (P 0) ==> ! n . P n)]])
     ((REPEAT STRIP_TAC) THEN (SPEC_TAC (([[n:num]]), ([[n:num]]))) THEN
           INDUCT_TAC THEN (ASM_SIMP_TAC []) THEN
           (ASM_SIMP_TAC [(← ar (← ExceptT.mk [[0 < (SUC n)]]))]))
  let lem4 ← HolLight.SPEC ([[(\nu.poly (SOD f) (&nu) = poly (SOD f) (&0) * exp (&nu) - &nu * (exp ((&nu) - xi (&nu) f)) * poly f (xi (&nu) f))]]) NUM_CASES_LEMMA
  let lem5 ← HolLight.BETA_RULE lem4
  let lem6 ← HolLight.MP lem5 lem3
  let lem100 ← ExceptT.mk (Session.SIMP_RULE [(← ar (← ExceptT.mk [[!n.0 <= n]])), (← ar (← ExceptT.mk [[(0:num) + 1 = 1]]))] (← HolLight.ISPECL [([[f:num->real]]), ([[0]]), ([[0]]), ([[PRE (LENGTH (c:(real)list))]])] SUM_COMBINE_R))
  let lem0001 ← HolLight.ASSUME ([[LENGTH (c:(real)list) > 1]])
  let lem0002 ← HolLight.MATCH_MP (← ar (← ExceptT.mk [[(x:num) > 1 ==> ~(x=0)]])) lem0001
  let lem0003 ← HolLight.REWRITE_RULE [Session.listThms1.LENGTH_EQ_NIL] lem0002
  let lem0004 ← HolLight.MATCH_MP POLY_SUM_EQUIV lem0003
  let SUM_LMUL_NUMSEG ← HolLight.GEN_ALL (← HolLight.ISPECL [([[f:num->real]]), ([[c:real]]), ([[n..m]])] SUM_LMUL)
  let h5 ← rr (← ExceptT.mk [[(A:real) * B * C = B * A * C]])
  let h4 ← rr (← ExceptT.mk [[(EL 0 c) * (poly (SOD f) (&0))  = (EL 0 c) * (poly (SOD f) (&0)) * (&1)]])
  let h3 ← rr (← ExceptT.mk [[(A:real) + B - A = B]])
  let h2 ← rr (← ExceptT.mk [[(A:real) + B + C = (A + C) + B]])
  let h1 ← ar (← ExceptT.mk [[0 + 1 = 1]])
  prove ([[(~ (transcendental (exp (&1)))) ==> ? c .
          ((ALL integer c) /\ ((LENGTH c) > 1) /\ ((EL 0 c) > &0) /\ (! f .((LHS c f) = (RHS c f))))]])
   ((ONCE_REWRITE_TAC [E_TRANSCENDENTAL_EQUIV]) THEN
       (ONCE_REWRITE_TAC [LHS, RHS]) THEN
       (REPEAT STRIP_TAC) THEN
       (EXISTS_TAC ([[c:(real)list]])) THEN
       (ONCE_REWRITE_TAC [(← HolLight.GSYM SessionLibrary.Analysis.REAL_RNEG_UNIQ)]) THEN
       (ONCE_REWRITE_TAC [lem03]) THEN
       (ONCE_REWRITE_TAC [NUMSEG_CONV ([[0..0]])]) THEN
       (ONCE_REWRITE_TAC [SUM_SING]) THEN
       (ASM_SIMP_TAC [foo2]) THEN
       BETA_TAC THEN
       (ONCE_REWRITE_TAC [h1]) THEN
       (ONCE_REWRITE_TAC [h2]) THEN
       (ONCE_REWRITE_TAC [(← HolLight.GSYM new2)]) THEN
       BETA_TAC THEN
       (ONCE_REWRITE_TAC [lem001]) THEN
       (CONV_TAC ((HolLight.RAND_CONV o HolLight.ABS_CONV o HolLight.RATOR_CONV o HolLight.RAND_CONV o HolLight.RATOR_CONV) (PURE_ONCE_REWRITE_CONV [lem6]))) THEN
       (ONCE_REWRITE_TAC [h3]) THEN
       (ONCE_REWRITE_TAC [h4]) THEN
       (ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_EXP_0)]) THEN
       (ONCE_REWRITE_TAC [(← HolLight.GSYM (HolLight.BETA_CONV ([[(\x.(EL x c) * (poly (SOD f) (&0)) * exp (&x)) (0)]])))]) THEN
       (ONCE_REWRITE_TAC [(← HolLight.GSYM (← HolLight.ISPEC ([[\x.(EL x c) * (poly (SOD f) (&0)) * exp (&x)]]) SUM_SING))]) THEN
       (ONCE_REWRITE_TAC [(← HolLight.GSYM (NUMSEG_CONV ([[0..0]])))]) THEN
       (ONCE_REWRITE_TAC [REAL_ADD_AC]) THEN
       (ONCE_REWRITE_TAC [lem100]) THEN
       (ONCE_REWRITE_TAC [h5]) THEN
       (ONCE_REWRITE_TAC [SUM_LMUL_NUMSEG]) THEN
       (ONCE_REWRITE_TAC [(← HolLight.GSYM E_POW_N)]) THEN
       (ONCE_REWRITE_TAC [(← HolLight.GSYM lem0004)]) THEN
       (ASM_SIMP_TAC []) THEN
       REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval replay PLANETMATH_EQN_4

#eval (do
  replay N_IS_INT
  replay NEG_N_IS_INT
  replay PLANETMATH_EQN_3
  replay LHS
  replay RHS
  replay E_POW_N
  replay NO_CONST_TERM_POLY_ROOT
  replay NEGATED_POLY_ROOT
  replay POLY_NUKE
  replay POLY_NUKE_ROOT
  replay POLY_NUKE_ZERO
  replay POLY_CONST_NO_ROOTS
  replay LENGTH_1
  replay SOUP_LEMMA
  replay POLY_NUKE_HD_NONZERO
  replay IS_INT_POLY_NUKE
  replay POLY_X_NOT_POLY_NIL
  replay NOT_TRANSCENDENTAL_ZERO
  replay ALL_IS_INT_POLY_CMUL
  replay TRANSCENDENTAL_MY_TRANSCENDENTAL
  replay E_TRANSCENDENTAL_EQUIV
  replay PLANETMATH_EQN_4
  IO.println "module Pm_eqn4 :\n  sig\n    val N_IS_INT : thm\n    val NEG_N_IS_INT : thm\n    val PLANETMATH_EQN_3 : thm\n    val LHS : thm\n    val RHS : thm\n    val E_POW_N : thm\n    val NO_CONST_TERM_POLY_ROOT : thm\n    val NEGATED_POLY_ROOT : thm\n    val POLY_NUKE : thm\n    val POLY_NUKE_ROOT : thm\n    val POLY_NUKE_ZERO : thm\n    val POLY_CONST_NO_ROOTS : thm\n    val LENGTH_1 : thm\n    val SOUP_LEMMA : thm\n    val POLY_NUKE_HD_NONZERO : thm\n    val IS_INT_POLY_NUKE : thm\n    val POLY_X_NOT_POLY_NIL : thm\n    val NOT_TRANSCENDENTAL_ZERO : thm\n    val ALL_IS_INT_POLY_CMUL : thm\n    val TRANSCENDENTAL_MY_TRANSCENDENTAL : thm\n    val E_TRANSCENDENTAL_EQUIV : thm\n    val PLANETMATH_EQN_4 : thm\n   end" : IO Unit)
end Pm_eqn4

#eval phrase 29
namespace Pm_eqn5
def POLY_MUL_ITER : thm := keep "POLY_MUL_ITER" fun _ => (do
  ExceptT.mk (Session.new_recursive_definition num_RECURSION ([[(poly_mul_iter f 0 = [&1]) /\
     (!n . poly_mul_iter f (SUC n) = (f (SUC n)) ** (poly_mul_iter f n))]]))
  : ExceptT String IO thm).run
#eval replay POLY_MUL_ITER

def PLANETMATH_EQN_5 : thm := keep "PLANETMATH_EQN_5" fun _ => new_definition
 [[g n p  = (&1/(&(FACT (p  -1)))) ##
                   ((poly_exp [&0;&1] (p-1)) **
                       (poly_exp (poly_mul_iter (\i.[-- &i; &1]) n) p))]]
#eval replay PLANETMATH_EQN_5

#eval (do
  replay POLY_MUL_ITER
  replay PLANETMATH_EQN_5
  IO.println "module Pm_eqn5 :\n  sig val POLY_MUL_ITER : thm val PLANETMATH_EQN_5 : thm  end" : IO Unit)
end Pm_eqn5

#eval phrase 30
namespace Pm_eqn4_rhs
def ABS_LE_MUL2 : thm := keep "ABS_LE_MUL2" fun _ => (do
  prove ([[!(w:real) x y z. abs(w) <= y /\ abs(x) <= z ==> abs(w * x) <= (y * z)]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC [ABS_POS])
  : ExceptT String IO thm).run
#eval replay ABS_LE_MUL2

def SEPTEMBER_2009_LEMMA : thm := keep "SEPTEMBER_2009_LEMMA" fun _ => (do
  let lem0 ← HolLight.ASSUME ([[!i. 0 <= i /\ i <= SUC n ==> abs (poly (f i) x) <= &n']])
  let lem1 ← HolLight.SPEC ([[SUC n]]) lem0
  let lem2 ← ExceptT.mk (Session.SIMP_RULE [(← ar (← ExceptT.mk [[0 <= SUC n /\ SUC n <= SUC n]]))] lem1)
  let lem3 ← prove ([[(!i:num.(P0 i) ==> (P1 i)) ==> (!i:num.((P1 i) ==> (Q i))) ==> (!i:num.((P0 i) ==> (Q i)))]])
     (MESON_TAC [])
  let lem4 ← ar (← ExceptT.mk [[!i.(0 <= i /\ i <= n) ==> (0 <= i /\ i <= SUC n)]])
  let lem5 ← HolLight.GEN ([[Q:num->bool]]) (← HolLight.MATCH_MP lem3 lem4)
  let lem6 ← HolLight.ASSUME ([[!n'. (!i. 0 <= i /\ i <= n ==> abs (poly (f i) x) <= &n') ==> abs (poly (poly_mul_iter f n) x) <= &n' pow n]])
  let lem7 ← HolLight.SPEC ([[n':num]]) lem6
  let lem9 ← HolLight.UNDISCH (← HolLight.BETA_RULE (← HolLight.SPEC ([[\i. abs (poly (f (i:num)) x) <= &n']]) lem5))
  let lem11 ← HolLight.MP lem7 lem9
  prove ([[!x f n n'.
    (!i.(0 <= i /\ i <= n) ==> (abs (poly (f i) x)) <= &(n')) ==>
    (abs (poly (poly_mul_iter f n) x)) <= (&(n') pow n)]])
   (STRIP_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
      [(REWRITE_TAC ([Pm_eqn5.POLY_MUL_ITER, poly, real_pow] ++ rewrites0)) THEN REAL_ARITH_TAC2,
        STRIP_TAC THEN STRIP_TAC THEN
        (REWRITE_TAC [Pm_eqn5.POLY_MUL_ITER, POLY_MUL, real_pow]) THEN
        (MATCH_MP_TAC ABS_LE_MUL2) THEN
        (SIMP_TAC [lem2, lem11])])
  : ExceptT String IO thm).run
#eval replay SEPTEMBER_2009_LEMMA

def SEPTEMBER_2009_LEMMA_2 : thm := keep "SEPTEMBER_2009_LEMMA_2" fun _ => (do
  let h3 ← rr (← ExceptT.mk [[--(-- &i + (x:real)) =  &i - x ]])
  let h2 ← rr (← ExceptT.mk [[-- &i + (x:real) =  x - &i ]])
  let h1 ← rr (← ExceptT.mk [[&0 <= -- &i + (x:real) <=>  &i <= x]])
  prove ([[&0 < x /\ x < &n
      ==> (!i. 0 <= i /\ i <= n ==> abs(poly [-- &i; &1] x) <= &n)]])
   ((REWRITE_TAC [(← HolLight.GSYM REAL_LE)]) THEN (REPEAT STRIP_TAC) THEN
      (REWRITE_TAC ([poly] ++ rewrites0)) THEN
      (REWRITE_TAC [h1, real_abs]) THEN (ASM_CASES_TAC ([[&i <= (x:real)]])) THENL
      [(ASM_SIMP_TAC []) THEN
        (REWRITE_TAC [h2]) THEN
        ASM_REAL_ARITH_TAC,
        (ASM_SIMP_TAC []) THEN
        (REWRITE_TAC [h3]) THEN
        ASM_REAL_ARITH_TAC])
  : ExceptT String IO thm).run
#eval replay SEPTEMBER_2009_LEMMA_2

def FACT_DIV_LCANCELS : thm := keep "FACT_DIV_LCANCELS" fun _ => (do
  let lem0 ← HolLight.SPECL [([[0]]), ([[FACT n]])] REAL_OF_NUM_LT
  let lem1 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM lem0)] FACT_LT
  let lem2 ← HolLight.SPECL [([[x:real]]), ([[(&(FACT n)):real]])] REAL_DIV_LMUL
  let lem3 ← rr (← ExceptT.mk [[!x:real. &0 < x ==> ~(x = &0)]])
  let lem4 ← HolLight.MATCH_MP lem3 (← HolLight.SPEC_ALL lem1)
  prove ([[!n x.  &(FACT n) * x / &(FACT n)  = x]])
   (ACCEPT_TAC (← HolLight.GEN_ALL (← HolLight.MP lem2 lem4)))
  : ExceptT String IO thm).run
#eval replay FACT_DIV_LCANCELS

def NOVEMBER_LEMMA_1 : thm := keep "NOVEMBER_LEMMA_1" fun _ => (do
  let l0 ← HolLight.SPECL [([[0]]), ([[FACT (p-1)]])] REAL_OF_NUM_LT
  let l2 := Prod.snd (← HolLight.EQ_IMP_RULE l0)
  let l3 ← HolLight.MP l2 (← HolLight.SPEC ([[(p:num) - 1]]) FACT_LT)
  let l4 ← HolLight.SPEC ([[(&(FACT (p - 1))):real]]) REAL_LE_LCANCEL_IMP
  let l5 ← ExceptT.mk (Session.SIMP_RULE [l3] l4)
  let ll0 := Prod.snd (← HolLight.EQ_IMP_RULE (← HolLight.SPEC_ALL REAL_ABS_REFL))
  let ll1 ← HolLight.IMP_TRANS (← rr (← ExceptT.mk [[(&0):real < x ==> &0 <= x]])) ll0
  let ll2 ← HolLight.UNDISCH ll1
  let asses : List term := [([[(p:num) > 1]]), ([[&0 < (x:real)]]), ([[(x:real) < &n]])]
  let j0 ← HolLight.SPECL [([[p - 1]]), ([[x:real]]), ([[(&n):real]])] REAL_POW_LE2
  let j1 ← rr (← ExceptT.mk [[(&0) < (x:real) /\ x < (&n) ==> (&0 <=x /\ x <= (&n))]])
  let j2 ← HolLight.UNDISCH_ALL (← BRW1 (← HolLight.IMP_TRANS j1 j0))
  let ll4 ← HolLight.SPECL [([[(x:real) pow (p - 1)]]), ([[((&n):real) pow (p - 1)]]), ([[(abs (r:real)) pow p]])] REAL_LE_MUL2
  let ll5 ← HolLight.SPECL [([[x:real]]), ([[(p:num) - 1]])] REAL_POW_LE
  let ll50 ← HolLight.UNDISCH (← HolLight.IMP_TRANS (← rr (← ExceptT.mk [[&0 < x ==> (&0) <= (x:real)]])) ll5)
  let ll6 ← ADD_ASSUMS asses ll4
  let ll7 ← rr (← ExceptT.mk [[(x:real) < y ==> x <= y]])
  let ll8 ← ExceptT.mk (Session.SIMP_RULE [j2, ll50, ll7, REAL_POW_LE, REAL_ABS_POS] ll6)
  let ll9 ← HolLight.ADD_ASSUM ([[p > 1]]) (← HolLight.SPEC ([[p:num]]) REAL_POW_LE2)
  let ll10 ← HolLight.UNDISCH (← ar (← ExceptT.mk [[p > 1 ==> ~(p = 0)]]))
  let ll11 ← ExceptT.mk (Session.SIMP_RULE [ll10] ll9)
  let ll12 ← HolLight.SPEC ([[abs (r:real)]]) ll11
  let ll13 ← ExceptT.mk (Session.SIMP_RULE [REAL_ABS_POS] ll12)
  let lem0 ← HolLight.UNDISCH (← HolLight.UNDISCH (← BRW1 SEPTEMBER_2009_LEMMA_2))
  let lem1 ← HolLight.MATCH_MP SEPTEMBER_2009_LEMMA lem0
  let lem2 ← HolLight.DISCH_ALL (← HolLight.DISCH ([[(&0) < (x:real)]]) lem1)
  let lem3 ← HolLight.SPEC ([[SUC n]]) (← HolLight.GEN ([[n:num]]) lem2)
  let h1 ← rr (← ExceptT.mk [[&1 * (x:real) = x]])
  prove ([[p > 1 ==>
      &0 < x /\ x < &n ==>
       (abs(poly (g n p) x)) <=
           (&1/(&(FACT (p  -1)))) * ((&n) pow (p - 1)) * ((&n pow n) pow p)]])
   (STRIP_TAC THEN STRIP_TAC THEN
     (ONCE_REWRITE_TAC [Pm_eqn5.PLANETMATH_EQN_5]) THEN
     (ONCE_REWRITE_TAC [POLY_CMUL]) THEN
     (ONCE_REWRITE_TAC [POLY_MUL]) THEN
     (ONCE_REWRITE_TAC [POLY_EXP]) THEN
     (ONCE_REWRITE_TAC [poly]) THEN
     (ONCE_REWRITE_TAC [poly]) THEN
     (ONCE_REWRITE_TAC [poly]) THEN
     (REWRITE_TAC rewrites0) THEN
     (ONCE_REWRITE_TAC [REAL_ABS_MUL]) THEN
     (ONCE_REWRITE_TAC [REAL_ABS_MUL]) THEN
     (ONCE_REWRITE_TAC [REAL_ABS_POW]) THEN
     (ONCE_REWRITE_TAC [REAL_ABS_DIV]) THEN
     (ONCE_REWRITE_TAC [ABS_N]) THEN
     (MATCH_MP_TAC l5) THEN
     (ONCE_REWRITE_TAC [REAL_MUL_ASSOC]) THEN
     (SIMP_TAC [FACT_DIV_LCANCELS, h1]) THEN
     (SIMP_TAC [ll2]) THEN
     (MATCH_MP_TAC ll8) THEN
     (MATCH_MP_TAC ll13) THEN
     (UNDISCH_TAC ([[&0 < (x:real)]])) THEN
     (UNDISCH_TAC ([[(x:real) < &n]])) THEN
     (SPEC_TAC (([[n:num]]), ([[n:num]]))) THEN
     INDUCT_TAC THENL [REAL_ARITH_TAC2, (ACCEPT_TAC lem3)])
  : ExceptT String IO thm).run
#eval replay NOVEMBER_LEMMA_1

def NOVEMBER_LEMMA_2 : thm := keep "NOVEMBER_LEMMA_2" fun _ => (do
  let l0 ← HolLight.SPECL [([[(&v):real]]), ([[f:(real)list]])] Pm_lemma1.xi_DEF
  let l1 ← HolLight.UNDISCH (← HolLight.ONCE_REWRITE_RULE [REAL_OF_NUM_LT] l0)
  let [ l2 , l3 , _ ] := HolLight.CONJUNCTS l1 | throw "let [..]: wrong length"
  let l4 ← HolLight.GEN_ALL (← rr (← ExceptT.mk [[(&v) <= y ==> z < (&v) ==> (z:real) < y]]))
  let l6 ← HolLight.SPECL [([[v:num]]), ([[z:real]]), ([[(&n):real]])] l4
  let l7 ← HolLight.UNDISCH l6
  let h2 ← ar (← ExceptT.mk [[1 <= v <=> 0 < v]])
  let h1 ← tt (← ExceptT.mk [[(X /\ Y ==> Z) <=> (X ==> Y ==> Z)]])
  prove ([[ 1 <= v /\ v <= n
       ==> ((&0) < ( xi (&v) f)  /\ (xi (&v) f) < (&n))]])
   ((ONCE_REWRITE_TAC [h1, h2]) THEN
      (ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_LE), (← HolLight.GSYM REAL_OF_NUM_LT)]) THEN
      STRIP_TAC THEN STRIP_TAC THEN (SIMP_TAC [l2]) THEN
      (MATCH_MP_TAC l7) THEN (ACCEPT_TAC l3))
  : ExceptT String IO thm).run
#eval replay NOVEMBER_LEMMA_2

def REAL_LE_MUL3 : thm := keep "REAL_LE_MUL3" fun _ => (do
  let lst : List term := [([[w0:real]]), ([[w1:real]]), ([[(x0 * y0):real]]), ([[(x1 * y1):real]])]
  let c0 ← HolLight.SPECL lst REAL_LE_MUL2
  prove ([[! w0 x0 y0 w1 x1 (y1:real).
     (&0 <= w0) ==> (&0 <= x0) ==> (&0 <= y0) ==>
     (w0 <= w1) ==> (x0 <= x1) ==> (y0 <= y1) ==>
     (w0 * x0 * y0) <= (w1 * x1 * y1)]])
   (MESON_TAC [c0, REAL_LE_MUL2, SessionLibrary.Analysis.REAL_LE_MUL])
  : ExceptT String IO thm).run
#eval replay REAL_LE_MUL3

def MAX_ABS_DEF : thm := keep "MAX_ABS_DEF" fun _ => (do
  ExceptT.mk (Session.new_recursive_definition list_RECURSION ([[    (max_abs [] = &0)
        /\  (max_abs (CONS h t) = real_max (real_abs h) (max_abs t))]]))
  : ExceptT String IO thm).run
#eval replay MAX_ABS_DEF

def MAX_ABS_LE : thm := keep "MAX_ABS_LE" fun _ => (do
  let l0 ← HolLight.UNDISCH (← rr (← ExceptT.mk [[~((abs h) <= max_abs t) ==> x <= (max_abs t) ==> x <= (abs h)]]))
  let h1 ← ar (← ExceptT.mk [[0 <= y]])
  prove ([[! cs i.
     (0 <= i /\ i < (LENGTH cs) ==>
       (real_abs (EL i cs)) <= (max_abs cs))]])
   (LIST_INDUCT_TAC THENL
      [(SIMP_TAC [Session.listDefs.LENGTH]) THEN ARITH_TAC,
        INDUCT_TAC THENL
        [(SIMP_TAC [Session.listDefs.HD, Session.listDefs.EL, MAX_ABS_DEF, REAL_MAX_MAX]),
          (SIMP_TAC [Session.listDefs.TL, Session.listDefs.EL, MAX_ABS_DEF, REAL_MAX_MAX, Session.listDefs.LENGTH, LT_SUC]) THEN
          (ASM_CASES_TAC ([[(real_abs h) <= (max_abs t)]])) THEN
          (ASM_SIMP_TAC [real_max, h1, l0])]])
  : ExceptT String IO thm).run
#eval replay MAX_ABS_LE

def KEATS_PART_1 : thm := keep "KEATS_PART_1" fun _ => (do
  let keats12 ← ar (← ExceptT.mk [[1 <= i /\ i <= (PRE (LENGTH (c:(real)list))) ==> (0 <= i /\ i < LENGTH c)]])
  let keats13 ← HolLight.IMP_TRANS keats12 (← HolLight.SPECL [([[c:(real)list]]), ([[i:num]])] MAX_ABS_LE)
  let keats14 ← HolLight.SPECL [([[real_of_num i]])] REAL_LE_LMUL
  let keats15 ← ar (← ExceptT.mk [[(&0) <= (real_of_num i)]])
  let keats16 ← ExceptT.mk (Session.SIMP_RULE [keats15] keats14)
  let keats17 ← HolLight.UNDISCH keats13
  let keats18 ← HolLight.MATCH_MP keats16 keats17
  prove ([[1 <= i /\ i <= PRE (LENGTH c) ==> ( &i * abs (EL i c) <= &i * max_abs c)]])
   (ACCEPT_TAC (← HolLight.DISCH_ALL keats18))
  : ExceptT String IO thm).run
#eval replay KEATS_PART_1

def KEATS_PART_2 : thm := keep "KEATS_PART_2" fun _ => (do
  let j0 ← HolLight.ASSUME ([[1 <= v /\ (v:num) <= (PRE (LENGTH (c:(real)list)))]])
  let j00 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM REAL_OF_NUM_LE)] (← HolLight.CONJUNCT2 j0)
  let j1 ← rr (← ExceptT.mk [[!n .(real_of_num v <= &n) ==> (&0 > --xi (&v) (g n p)) ==> (&n) > (&v) - (xi (&v) (g n p))]])
  let j2 ← HolLight.MP (← HolLight.SPEC ([[PRE (LENGTH (c:(real)list))]]) j1) j00
  let g_term := ([[g (PRE (LENGTH (c:(real)list))) p]])
  let k33 ← HolLight.SPEC ([[PRE (LENGTH (c:(real)list))]]) (← HolLight.GEN ([[n:num]]) NOVEMBER_LEMMA_2)
  let k34 ← HolLight.SPEC g_term (← HolLight.GEN ([[f:(real)list]]) k33)
  let k35 ← HolLight.DISCH ([[1 <= v /\ v <= (PRE (LENGTH (c:(real)list)))]]) (← HolLight.CONJUNCT1 (← HolLight.UNDISCH k34))
  let k36 ← HolLight.UNDISCH (← HolLight.SPEC ([[PRE (LENGTH (c:(real)list))]]) (← HolLight.GEN ([[n:num]]) k35))
  let k37 ← rr (← ExceptT.mk [[!x. (real_of_num 0) < x ==> (real_of_num 0) > -- x]])
  let k38 ← HolLight.MATCH_MP k37 k36
  let k40 ← HolLight.MP j2 k38
  let k41 ← rr (← ExceptT.mk [[!x (y:real).x > y ==> y <= x]])
  let k42 ← HolLight.MATCH_MP k41 k40
  let k42 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM REAL_EXP_MONO_LE)] k42
  let k43 ← rr (← ExceptT.mk [[!(x:real) . (&0) <= x ==> abs x = x]])
  let k44 ← HolLight.GEN ([[x:real]]) (← HolLight.MATCH_MP k43 (← HolLight.SPEC ([[x:real]]) REAL_EXP_POS_LE))
  let k45 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM k44)] k42
  let k46 ← HolLight.DISCH_ALL k45
  let k47 ← BRW0 (← ExceptT.mk (Session.SIMP_RULE [(← ar (← ExceptT.mk [[0 < v <=> 1 <= v]]))] k46))
  prove ([[(1 <= v /\ v <= PRE (LENGTH (c:(real)list))) ==>
       abs (exp ((&v) - xi (&v) (g (PRE (LENGTH c)) p))) <= abs (exp (&(PRE (LENGTH (c:(real)list)))))]])
   (ACCEPT_TAC k47)
  : ExceptT String IO thm).run
#eval replay KEATS_PART_2

def KEATS_PART_3 : thm := keep "KEATS_PART_3" fun _ => (do
  let k0 ← HolLight.UNDISCH NOVEMBER_LEMMA_2
  let k1 ← HolLight.UNDISCH NOVEMBER_LEMMA_1
  let k2 ← HolLight.GEN ([[x:real]]) k1
  let k3 ← HolLight.SPEC ([[xi (real_of_num i) f]]) k2
  let k5 ← HolLight.MATCH_MP k3 k0
  let g_term := ([[g (PRE (LENGTH (c:(real)list))) p]])
  let k6 ← HolLight.SPEC g_term (← HolLight.GEN ([[f:(real)list]]) k5)
  let k7 ← HolLight.SPEC ([[PRE (LENGTH (c:(real)list))]]) (← HolLight.GEN ([[n:num]]) (← HolLight.DISCH ([[1 <= v /\ v <= n]]) k6))
  let k8 ← HolLight.DISCH ([[0 < v]]) k7
  let k9 ← BRW0 (← ExceptT.mk (Session.SIMP_RULE [(← ar (← ExceptT.mk [[0 < v <=> 1 <= v]]))] k8))
  HolLight.UNDISCH (← prove ([[p > 1 ==> (1 <= i /\ i <= PRE (LENGTH (c:(real)list)))
     ==> abs (poly (g (PRE (LENGTH c)) p) (xi (&i) (g (PRE (LENGTH c)) p))) <=
         &1 / &(FACT (p - 1)) *
         &(PRE (LENGTH c)) pow (p - 1) *
         &(PRE (LENGTH c)) pow PRE (LENGTH c) pow p]])
     (MATCH_ACCEPT_TAC (← HolLight.DISCH_ALL k9)))
  : ExceptT String IO thm).run
#eval replay KEATS_PART_3

def RHS_4_F5_LE_SUM : thm := keep "RHS_4_F5_LE_SUM" fun _ => (do
  let keats4 := REFL ([[abs (RHS c f)]])
  let keats5 ← HolLight.CONV_RULE (HolLight.RAND_CONV (HolLight.REWRITE_CONV [Pm_eqn4.RHS])) keats4
  let keats6 ← HolLight.REWRITE_RULE [REAL_ABS_NEG] keats5
  let keats7 ← HolLight.SPECL [([[(\i.(&i) * (EL i c) * (exp (&i - (xi (&i) f))) * (poly f (xi
        (&i) f)))]]), ([[1]]), ([[PRE (LENGTH (c:(real)list))]])] SUM_ABS_NUMSEG
  let keats8 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM keats6)] keats7
  let keats9 ← HolLight.REWRITE_RULE [REAL_ABS_NUM, REAL_ABS_MUL] keats8
  let g_term := ([[g (PRE (LENGTH (c:(real)list))) p]])
  let keats10 ← HolLight.SPEC g_term (← HolLight.GEN ([[f:(real)list]]) keats9)
  prove ([[abs (RHS c (g (PRE (LENGTH c)) p)) <=
     sum (1..PRE (LENGTH c))
     (\i. &i *
          abs (EL i c) *
          abs (exp (&i - xi (&i) (g (PRE (LENGTH c)) p))) *
          abs
          (poly (g (PRE (LENGTH c)) p) (xi (&i) (g (PRE (LENGTH c)) p))))]])
   (ACCEPT_TAC keats10)
  : ExceptT String IO thm).run
#eval replay RHS_4_F5_LE_SUM

def RHS_4_BOUND_PRE : thm := keep "RHS_4_BOUND_PRE" fun _ => (do
  let w0 := ([[(real_of_num i) * (real_abs (EL i c))]])
  let w1 := ([[(real_of_num i) * (max_abs c)]])
  let x0 := ([[abs (exp (&v - xi (&v) (g (PRE (LENGTH (c:(real)list))) p)))]])
  let x1 := ([[abs (exp (&(PRE (LENGTH (c:(real)list)))))]])
  let y0 := ([[abs (poly (g (PRE (LENGTH (c:(real)list))) p) (xi (&i) (g (PRE
      (LENGTH c)) p)))]])
  let y1 := ([[ &1 / &(FACT (p - 1)) * &(PRE (LENGTH (c:(real)list))) pow (p -
      1) * &(PRE (LENGTH c)) pow PRE (LENGTH c) pow p]])
  let rename_free_var := fun oo nn tt => (do HolLight.SPEC nn (← HolLight.GEN oo tt) : ExceptT String IO _)
  let v2i := fun tt => (do rename_free_var ([[v:num]]) ([[i:num]]) tt : ExceptT String IO _)
  let josh0 ← HolLight.SPECL [w0, x0, y0, w1, x1, y1] REAL_LE_MUL3
  let josh2 ← HolLight.SPECL [([[real_of_num i]]), ([[real_abs (EL i c)]])] SessionLibrary.Analysis.REAL_LE_MUL
  let josh3 ← ExceptT.mk (Session.SIMP_RULE [REAL_ABS_POS, (← rr (← ExceptT.mk [[(real_of_num 0) <= &i]]))] josh2)
  let josh4 ← v2i (← ExceptT.mk (Session.SIMP_RULE [josh3, REAL_ABS_POS] josh0))
  let josh5 ← ExceptT.mk (Session.SIMP_RULE [(← HolLight.UNDISCH KEATS_PART_1)] josh4)
  let josh6 ← ExceptT.mk (Session.SIMP_RULE [(← HolLight.UNDISCH (← v2i KEATS_PART_2))] josh5)
  let josh7 ← ExceptT.mk (Session.SIMP_RULE [(← HolLight.UNDISCH KEATS_PART_3)] josh6)
  let josh8 ← HolLight.DISCH ([[1 <= i /\ i <= (PRE (LENGTH (c:(real)list)))]]) josh7
  let f0 := ([[(\i.
             &i *
             abs (EL i c) *
             abs (exp (&i - xi (&i) (g (PRE (LENGTH c)) p))) *
             abs (poly (g (PRE (LENGTH c)) p) (xi (&i) (g (PRE (LENGTH c))
             p))))]])
  let f1 := ([[(\i.
                 (&i * max_abs c) *
                 abs (exp (&(PRE (LENGTH c)))) *
                 &1 / &(FACT (p - 1)) *
                 &(PRE (LENGTH c)) pow (p - 1) *
                 &(PRE (LENGTH c)) pow PRE (LENGTH c) pow p)]])
  let josh9 ← HolLight.SPECL [f0, f1, ([[1]]), ([[PRE (LENGTH (c:(real)list))]])] SUM_LE_NUMSEG
  let josh10 ← HolLight.REWRITE_RULE [(← HolLight.GSYM REAL_MUL_ASSOC)] (← HolLight.BETA_RULE josh9)
  let josh11 ← HolLight.REWRITE_RULE [(← HolLight.GSYM REAL_MUL_ASSOC)] (← HolLight.GEN ([[i:num]]) josh8)
  let josh12 ← HolLight.MP josh10 josh11
  let josh13 ← HolLight.CONJ RHS_4_F5_LE_SUM josh12
  let josh14 ← HolLight.MATCH_MP SessionLibrary.Analysis.REAL_LE_TRANS josh13
  let josh15 ← HolLight.ONCE_REWRITE_RULE [SUM_RMUL] josh14
  prove ([[abs (RHS c (g (PRE (LENGTH c)) p)) <=
          (sum (1..PRE (LENGTH c)) &) *
               (max_abs c *
               abs (exp (&(PRE (LENGTH c)))) *
               &1 / &(FACT (p - 1)) *
               &(PRE (LENGTH c)) pow (p - 1) *
               &(PRE (LENGTH c)) pow PRE (LENGTH c) pow p)]])
   (ACCEPT_TAC josh15)
  : ExceptT String IO thm).run
#eval replay RHS_4_BOUND_PRE

def RHS_4_BOUND : thm := keep "RHS_4_BOUND" fun _ => (do
  let l1 ← HolLight.MATCH_MP (← HolLight.SPEC ([[&0:real]]) SessionLibrary.Analysis.REAL_LT_IMP_LE) (← HolLight.SPEC ([[x:real]]) REAL_EXP_POS_LT)
  let l2 ← HolLight.REWRITE_RULE [(← HolLight.GSYM REAL_ABS_REFL)] l1
  HolLight.ONCE_REWRITE_RULE [l2] RHS_4_BOUND_PRE
  : ExceptT String IO thm).run
#eval replay RHS_4_BOUND

#eval phrase 31
def JESSE_POW_LEMMA : thm := keep "JESSE_POW_LEMMA" fun _ => (do
  let c0 ← HolLight.UNDISCH (← ar (← ExceptT.mk [[(p:num) > 1 ==> p = SUC (p - 1) ]]))
  prove ([[(p:num) > 1 ==> !x.real_pow x p = x * (real_pow x (p-1))]])
   (STRIP_TAC THEN STRIP_TAC THEN
       (CONV_TAC (HolLight.RATOR_CONV (HolLight.ONCE_REWRITE_CONV [c0]))) THEN
       (SIMP_TAC [real_pow]))
  : ExceptT String IO thm).run
#eval replay JESSE_POW_LEMMA

def JESSE_REAL_ABS_LE : thm := keep "JESSE_REAL_ABS_LE" fun _ => (do
  let int10 ← HolLight.UNDISCH (← rr (← ExceptT.mk [[(real_abs x) <= y ==>  y = real_abs y]]))
  prove ([[!(x:real) y.(abs x) <= y ==> (abs x) <= (abs y)]])
   ((REPEAT STRIP_TAC) THEN (ASM_SIMP_TAC [(← HolLight.GSYM int10)]))
  : ExceptT String IO thm).run
#eval replay JESSE_REAL_ABS_LE

def OLDGERMAN_LEMMA : thm := keep "OLDGERMAN_LEMMA" fun _ => (do
  let w0 ← HolLight.MATCH_MP SUM_SUMMABLE (← HolLight.SPEC ([[C:real]]) REAL_EXP_CONVERGES)
  let w1 ← HolLight.MATCH_MP SER_ZERO w0
  let w2 ← HolLight.BETA_RULE w1
  let w3 ← HolLight.SPEC ([[C2:real]]) SEQ_CONST
  let w4 ← HolLight.CONJ w3 w2
  let w5 ← HolLight.BETA_RULE (← HolLight.MATCH_MP SEQ_MUL w4)
  let w6 ← HolLight.ONCE_REWRITE_RULE [(← rr (← ExceptT.mk [[(C2:real) * (&0) = &0]]))] w5
  let w7 ← HolLight.ONCE_REWRITE_RULE [SEQ] w6
  let w8 ← HolLight.GEN_ALL (← HolLight.BETA_RULE w7)
  let h1 ← ar (← ExceptT.mk [[n' >= SUC n ==> n' >= n]])
  prove ([[ !C2 C e.
        &0 < e
        ==> (?N . !n. n >= N ==>
        abs (C2 * inv (&(FACT n)) * C pow n - &0) < e)]])
   ((REPEAT STRIP_TAC) THEN
     (CHOOSE_TAC (← HolLight.UNDISCH (← HolLight.SPEC_ALL w8))) THEN
     (EXISTS_TAC ([[SUC N]])) THEN
     (ASM_SIMP_TAC [h1]))
  : ExceptT String IO thm).run
#eval replay OLDGERMAN_LEMMA

def RHS_4_LT_ONE_MESSY : thm := keep "RHS_4_LT_ONE_MESSY" fun _ => (do
  let c1 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.UNDISCH JESSE_POW_LEMMA)] RHS_4_BOUND
  let c2 ← HolLight.SPECL [([[real_pow (&(PRE (LENGTH (c:(real)list)))) (p-1)]])] REAL_MUL_SYM
  let c3 ← HolLight.ONCE_REWRITE_RULE [c2] c1
  let c4 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM REAL_MUL_ASSOC)] c3
  let c5 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM REAL_POW_MUL)] c4
  let c6 ← HolLight.ONCE_REWRITE_RULE [REAL_MUL_SYM] (← HolLight.CONJUNCT2 real_pow)
  let c7 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM c6)] c5
  let c8 ← rr (← ExceptT.mk [[!x. (real_of_num 1)/x = inv x]])
  let c9 ← HolLight.ONCE_REWRITE_RULE [c8] c7
  let c10 ← rr (← ExceptT.mk [[!x y z.(inv x) * y * z = y * inv x * z]])
  let c11 ← HolLight.ONCE_REWRITE_RULE [c10] c9
  let t0 := ([[sum (1..PRE (LENGTH c)) & *
     max_abs c *
     (exp (&(PRE (LENGTH c)))) *
     &(PRE (LENGTH c)) pow PRE (LENGTH c)]])
  let t1 := ([[real_of_num (PRE (LENGTH (c:(real)list))) pow SUC (PRE (LENGTH c))]])
  let int0 ← HolLight.SPECL [t0, t1, ([[real_of_num 1]])] OLDGERMAN_LEMMA
  let int1 ← ExceptT.mk (Session.SIMP_RULE [(← rr (← ExceptT.mk [[(real_of_num 0) < &1]]))] int0)
  let int2 ← ExceptT.mk (Session.SIMP_RULE [(← rr (← ExceptT.mk [[x - (real_of_num 0) = x]]))] int1)
  let t8 := ([[!n. n >= N
        ==> abs
            ((sum (1..PRE (LENGTH c)) & *
              max_abs c *
              (exp (&(PRE (LENGTH c)))) *
              &(PRE (LENGTH c)) pow PRE (LENGTH c)) *
             inv (&(FACT n)) *
             &(PRE (LENGTH c)) pow SUC (PRE (LENGTH c)) pow n) <
            &1]])
  let int5 ← HolLight.ASSUME t8
  let int50 ← rr (← ExceptT.mk [[((x:real) * y * z * w) * (a * b) = x * y * z * w * a *
   b]])
  let int51 ← HolLight.ONCE_REWRITE_RULE [int50] int5
  let int6 ← HolLight.SPEC ([[p - 1]]) int51
  let int7 ← ar (← ExceptT.mk [[ (p > N ==> p - 1 >= N)]])
  let int8 ← HolLight.UNDISCH (← HolLight.IMP_TRANS int7 int6)
  let int9 ← ar (← ExceptT.mk [[(x:real) <= y ==> y < (real_of_num 1) ==> x < (&1)]])
  let int10 ← HolLight.MATCH_MP JESSE_REAL_ABS_LE c11
  let int11 ← HolLight.MATCH_MP int9 int10
  let int12 ← HolLight.MP int11 int8
  let h1 ← ar (← ExceptT.mk [[p > 0 ==> ((p:num)  > N <=> p - 1 >= N)]])
  prove ([[?p0. !p. p > 1 ==> p> p0 ==> abs (RHS c (g (PRE (LENGTH c)) p)) < &1]])
   ((CHOOSE_TAC int2) THEN
     (EXISTS_TAC ([[N:num]])) THEN
     STRIP_TAC THEN
     STRIP_TAC THEN
     (ONCE_REWRITE_TAC [h1]) THEN
     DISCH_TAC THEN
     (MATCH_ACCEPT_TAC int12))
  : ExceptT String IO thm).run
#eval replay RHS_4_LT_ONE_MESSY

def LT_ONE : thm := keep "LT_ONE" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[p > SUC p0 ==> (p > p0 /\ p > 1)]])
  prove ([[!c. ?p0. !p. p> p0 ==> abs (RHS c (g (PRE (LENGTH c)) p)) < &1]])
   (STRIP_TAC THEN (CHOOSE_TAC RHS_4_LT_ONE_MESSY) THEN (EXISTS_TAC ([[SUC p0]])) THEN
      (ASM_MESON_TAC [h1]))
  : ExceptT String IO thm).run
#eval replay LT_ONE

#eval (do
  replay ABS_LE_MUL2
  replay SEPTEMBER_2009_LEMMA
  replay SEPTEMBER_2009_LEMMA_2
  replay FACT_DIV_LCANCELS
  replay NOVEMBER_LEMMA_1
  replay NOVEMBER_LEMMA_2
  replay REAL_LE_MUL3
  replay MAX_ABS_DEF
  replay MAX_ABS_LE
  replay KEATS_PART_1
  replay KEATS_PART_2
  replay KEATS_PART_3
  replay RHS_4_F5_LE_SUM
  replay RHS_4_BOUND_PRE
  replay RHS_4_BOUND
  replay JESSE_POW_LEMMA
  replay JESSE_REAL_ABS_LE
  replay OLDGERMAN_LEMMA
  replay RHS_4_LT_ONE_MESSY
  replay LT_ONE
  IO.println "module Pm_eqn4_rhs :\n  sig\n    val ABS_LE_MUL2 : thm\n    val SEPTEMBER_2009_LEMMA : thm\n    val SEPTEMBER_2009_LEMMA_2 : thm\n    val FACT_DIV_LCANCELS : thm\n    val NOVEMBER_LEMMA_1 : thm\n    val NOVEMBER_LEMMA_2 : thm\n    val REAL_LE_MUL3 : thm\n    val MAX_ABS_DEF : thm\n    val MAX_ABS_LE : thm\n    val KEATS_PART_1 : thm\n    val KEATS_PART_2 : thm\n    val KEATS_PART_3 : thm\n    val RHS_4_F5_LE_SUM : thm\n    val RHS_4_BOUND_PRE : thm\n    val RHS_4_BOUND : thm\n    val JESSE_POW_LEMMA : thm\n    val JESSE_REAL_ABS_LE : thm\n    val OLDGERMAN_LEMMA : thm\n    val RHS_4_LT_ONE_MESSY : thm\n    val LT_ONE : thm\n   end" : IO Unit)
end Pm_eqn4_rhs

#eval phrase 32
namespace Pm_eqn4_lhs
-- let N_IS_INT = ... (rebinds N_IS_INT)
def N_IS_INT_2 : thm := keep "N_IS_INT_2" fun _ => (do
  prove ([[!n . integer (&n)]])
   (MESON_TAC [is_int])
  : ExceptT String IO thm).run
#eval replay N_IS_INT_2

-- let NEG_N_IS_INT = ... (rebinds NEG_N_IS_INT)
def NEG_N_IS_INT_2 : thm := keep "NEG_N_IS_INT_2" fun _ => (do
  prove ([[!n . integer (--(&n))]])
   (MESON_TAC [is_int])
  : ExceptT String IO thm).run
#eval replay NEG_N_IS_INT_2

def INT_OF_REAL_ADD : thm := keep "INT_OF_REAL_ADD" fun _ => (do
  prove ([[!x y.(integer x) /\ (integer y)
           ==> (int_of_real (x + y)) =
               (int_of_real x) + (int_of_real y)]])
   (SIMP_TAC [integer, int_add, int_rep, N_IS_INT_2, NEG_N_IS_INT_2])
  : ExceptT String IO thm).run
#eval replay INT_OF_REAL_ADD

def INT_OF_REAL_MUL : thm := keep "INT_OF_REAL_MUL" fun _ => (do
  prove ([[!x y.(integer x) /\ (integer y)
           ==> (int_of_real (x * y)) =
               (int_of_real x) * (int_of_real y)]])
   (SIMP_TAC [is_int, int_mul, int_rep, N_IS_INT_2, NEG_N_IS_INT_2])
  : ExceptT String IO thm).run
#eval replay INT_OF_REAL_MUL

-- let rec INT_OF_REAL_CONV_helper t = ...
partial def INT_OF_REAL_CONV_helper (t : term) : ExceptT String IO (term × List term × List term) := do
  let q (x : IO (Except String term)) : ExceptT String IO term := ExceptT.mk x
  let real_op_2_int_op (t : term) : ExceptT String IO term := do
    if t == (← q [[real_add]]) then q [[int_add]]
    else if t == (← q [[real_sub]]) then q [[int_sub]]
    else if t == (← q [[real_mul]]) then q [[int_mul]]
    else if t == (← q [[real_pow]]) then q [[int_pow]]
    else if t == (← q [[real_neg]]) then q [[int_neg]]
    else pure t
  let ratorE (t : term) : ExceptT String IO term := ec (HolCore.Kernel.rator t)
  let randE (t : term) : ExceptT String IO term := ec (HolCore.Kernel.rand t)
  let iof ← q [[int_of_real]]
  if is_var t then return (← ec (mk_comb iof t), [], [t])
  else if (← ratorE t) == (← q [[real_of_num]]) then
    return (← ec (mk_comb iof t), [t], [])
  else if (← ratorE t) == (← q [[real_neg]]) then
    let (expr1, lst1, lst2) ← INT_OF_REAL_CONV_helper (← randE t)
    return (← ec (mk_comb (← q [[int_neg]]) expr1), lst1 ++ [t], lst2)
  else if (← ratorE (← ratorE t)) == (← q [[real_pow]]) then
    let rand1 ← randE (← ratorE t)
    let exponent ← randE t
    let (expr1, lst1, lst2) ← INT_OF_REAL_CONV_helper rand1
    return (← ec (mk_comb (← ec (mk_comb (← q [[int_pow]]) expr1)) exponent), lst1 ++ [t], lst2)
  else if (← ratorE (← ratorE t)) == (← q [[real_add]]) ||
          (← ratorE (← ratorE t)) == (← q [[real_mul]]) ||
          (← ratorE (← ratorE t)) == (← q [[real_sub]]) then
    let int_op ← real_op_2_int_op (← ratorE (← ratorE t))
    let rand1 ← randE (← ratorE t)
    let rand2 ← randE t
    let (expr1, lst11, lst12) ← INT_OF_REAL_CONV_helper rand1
    let (expr2, lst21, lst22) ← INT_OF_REAL_CONV_helper rand2
    return (← ec (mk_comb (← ec (mk_comb int_op expr1)) expr2), lst11 ++ lst21 ++ [t], lst12 ++ lst22)
  else return (t, [], [t])

-- let INT_OF_REAL_CONV = ...
def INT_OF_REAL_CONV_lemma : thm := keep "INT_OF_REAL_CONV_lemma" fun _ => (do
  ExceptT.mk (MESON [int_tybij] (← ExceptT.mk [[real_of_int x = y ==> int_of_real y = x]]))
  : ExceptT String IO thm).run
#eval replay INT_OF_REAL_CONV_lemma
def INT_OF_REAL_CONV (t : term) : IO (Except String thm) := (do
  let (exp, _real_sub_terms, is_int_assumpts) ← INT_OF_REAL_CONV_helper t
  let is_int_assumpts ← is_int_assumpts.mapM fun x => do ec (mk_comb (← ExceptT.mk [[integer]]) x)
  let fexp ← ec (HolCore.Kernel.rand (concl
    (← ExceptT.mk (HolLight.PURE_REWRITE_CONV [← HolLight.GSYM int_of_num] exp))))
  let rexp ← ec (mk_comb (← ExceptT.mk [[real_of_int]]) fexp)
  let c2 ← HolLight.CONJUNCT2 int_tybij
  let ths ← is_int_assumpts.mapM fun a => do
    HolLight.GEN_REWRITE_RULE HolCore.Lib.I [c2] (← HolLight.ASSUME a)
  let th3 ← ExceptT.mk (HolLight.PURE_REWRITE_CONV
    (ths ++ [int_pow_th, int_add_th, int_mul_th, int_sub_th, int_neg_th, int_of_num_th]) rexp)
  let ft ← HolLight.MATCH_MP INT_OF_REAL_CONV_lemma th3
  is_int_assumpts.foldrM (fun a th => HolLight.DISCH a th) ft
  : ExceptT String IO thm).run

def ALL_IS_INT : thm := keep "ALL_IS_INT" fun _ => (do
  prove ([[! h t . (ALL integer (CONS h t)) ==> (integer h)  /\ (ALL integer t)]])
   (SIMP_TAC [Session.listDefs.ALL])
  : ExceptT String IO thm).run
#eval replay ALL_IS_INT

def ALL_IS_INT_POLY_ADD : thm := keep "ALL_IS_INT_POLY_ADD" fun _ => (do
  let lem01 ← HolLight.UNDISCH (← HolLight.SPECL [([[h:real]]), ([[t:(real)list]])] ALL_IS_INT)
  let [ lem02 , lem03 ] := HolLight.CONJUNCTS lem01 | throw "let [..]: wrong length"
  let lem04 ← HolLight.UNDISCH (← HolLight.SPECL [([[h':real]]), ([[t':(real)list]])] ALL_IS_INT)
  let [ lem05 , lem06 ] := HolLight.CONJUNCTS lem04 | throw "let [..]: wrong length"
  let lem07 ← HolLight.CONJ lem02 lem05
  let lem08 ← HolLight.MATCH_MP INTEGER_ADD lem07
  let lem09 ← HolLight.ASSUME ([[! p2. ALL integer t /\ ALL integer p2 ==> ALL integer (t ++ p2)]])
  let lem10 ← HolLight.SPEC ([[t':(real)list]]) lem09
  let lem11 ← HolLight.CONJ lem03 lem06
  let lem12 ← HolLight.MP lem10 lem11
  prove ([[! p1 p2 . (ALL integer p1) /\ (ALL integer p2) ==> (ALL integer (p1 ++ p2))]])
   (LIST_INDUCT_TAC THENL
      [(SIMP_TAC [poly_add]),
        LIST_INDUCT_TAC THENL
        [(SIMP_TAC [poly_add]),
          (SIMP_TAC [poly_add]) THEN (ONCE_REWRITE_TAC [Session.listThms1.NOT_CONS_NIL]) THEN
          (SIMP_TAC []) THEN (SIMP_TAC [Session.listDefs.HD, Session.listDefs.TL]) THEN STRIP_TAC THEN
          (SIMP_TAC [Session.listDefs.ALL]) THEN
          CONJ_TAC THENL [(ACCEPT_TAC lem08), (ACCEPT_TAC lem12)]]])
  : ExceptT String IO thm).run
#eval replay ALL_IS_INT_POLY_ADD

-- let ALL_IS_INT_POLY_CMUL = ... (rebinds ALL_IS_INT_POLY_CMUL)
def ALL_IS_INT_POLY_CMUL_2 : thm := keep "ALL_IS_INT_POLY_CMUL_2" fun _ => (do
  prove ([[! p c. (integer c) /\ (ALL integer p) ==> (ALL integer (c ## p))]])
   (LIST_INDUCT_TAC THEN (ASM_SIMP_TAC [poly_cmul, Session.listDefs.ALL, INTEGER_MUL]))
  : ExceptT String IO thm).run
#eval replay ALL_IS_INT_POLY_CMUL_2

def ALL_IS_INT_POLY_MUL : thm := keep "ALL_IS_INT_POLY_MUL" fun _ => (do
  let lem01 ← HolLight.UNDISCH (← HolLight.SPECL [([[h:real]]), ([[t:(real)list]])] ALL_IS_INT)
  let lem02 ← HolLight.UNDISCH (← HolLight.SPECL [([[h':real]]), ([[t':(real)list]])] ALL_IS_INT)
  let [ lem03 , lem04 ] := HolLight.CONJUNCTS lem01 | throw "let [..]: wrong length"
  let [ lem05 , lem06 ] := HolLight.CONJUNCTS lem02 | throw "let [..]: wrong length"
  let lem07 ← HolLight.MATCH_MP INTEGER_MUL (← HolLight.CONJ lem03 lem05)
  let lem08 ← HolLight.MATCH_MP ALL_IS_INT_POLY_CMUL_2 (← HolLight.CONJ lem03 lem06)
  let lem09 ← HolLight.ASSUME ([[! p2. ALL integer t /\ ALL integer p2 ==> ALL integer (t ** p2)]])
  let lem10 ← HolLight.SPEC ([[(CONS h' t'):(real)list]]) lem09
  prove ([[! p1 p2 . (ALL integer p1) /\ (ALL integer p2) ==> (ALL integer (p1 ** p2))]])
   (LIST_INDUCT_TAC THENL
      [(LIST_INDUCT_TAC THENL [(SIMP_TAC [Session.listDefs.ALL, poly_mul]), (SIMP_TAC [poly_mul])]),
        LIST_INDUCT_TAC THENL
        [(SIMP_TAC [poly_mul]) THEN
          ((ASM_CASES_TAC ([[(t:(real)list) = [] ]])) THENL
          [(ASM_SIMP_TAC [Session.listDefs.ALL, poly_cmul]) THEN (SIMP_TAC [poly_cmul]),
            (ASM_SIMP_TAC [Session.listDefs.ALL, poly_cmul, poly_add]) THEN (SIMP_TAC [(← HolLight.SPEC ([[0]]) N_IS_INT_2)])]),
          STRIP_TAC THEN (ONCE_REWRITE_TAC [poly_mul]) THEN
          (ASM_CASES_TAC ([[(t:(real)list) = [] ]])) THENL
          [(ASM_SIMP_TAC [Session.listDefs.ALL, poly_cmul]) THEN STRIP_TAC THENL
            [(ACCEPT_TAC lem07), (ACCEPT_TAC lem08)],
            (ASM_SIMP_TAC []) THEN (MATCH_MP_TAC ALL_IS_INT_POLY_ADD) THEN
            CONJ_TAC THENL
            [(MATCH_MP_TAC ALL_IS_INT_POLY_CMUL_2) THEN CONJ_TAC THENL
              [(ACCEPT_TAC lem03), (ASM_SIMP_TAC [])],
              (SIMP_TAC [Session.listDefs.ALL]) THEN CONJ_TAC THENL
              [(ACCEPT_TAC (← HolLight.SPEC ([[0]]) N_IS_INT_2)), (ASM_SIMP_TAC [lem04, lem10])]]]]])
  : ExceptT String IO thm).run
#eval replay ALL_IS_INT_POLY_MUL

def NOT_POLY_MUL_ITER_NIL : thm := keep "NOT_POLY_MUL_ITER_NIL" fun _ => (do
  let lem02 ← ExceptT.mk (Session.SIMP_RULE [Session.listThms1.NOT_CONS_NIL] (← HolLight.ISPEC ([[[ -- &(SUC n); &1] ]]) NOT_POLY_MUL_NIL))
  let lem03 ← HolLight.ISPEC ([[(poly_mul_iter (\i.[ -- &i; &1]) n)]]) lem02
  let lem04 ← HolLight.UNDISCH lem03
  prove ([[! n . ~((poly_mul_iter (\i.[ -- &i; &1]) n) = [])]])
   (INDUCT_TAC THENL
      [(SIMP_TAC [Pm_eqn5.POLY_MUL_ITER, Session.listThms1.NOT_CONS_NIL]),
        (SIMP_TAC [Pm_eqn5.POLY_MUL_ITER, lem04])])
  : ExceptT String IO thm).run
#eval replay NOT_POLY_MUL_ITER_NIL

def ALL_IS_INT_POLY_MUL_ITER : thm := keep "ALL_IS_INT_POLY_MUL_ITER" fun _ => (do
  let FOOBAR_LEMMA ← prove ([[ALL integer [-- &(SUC n); &1] ]])
     ((SIMP_TAC [Session.listDefs.ALL]) THEN (SIMP_TAC [N_IS_INT_2, NEG_N_IS_INT_2]))
  prove ([[! n. (ALL integer (poly_mul_iter (\i.[-- &i; &1]) n))]])
   (INDUCT_TAC THENL
      [(ONCE_REWRITE_TAC [Pm_eqn5.POLY_MUL_ITER]) THEN
        (ONCE_REWRITE_TAC [Session.listDefs.ALL]) THEN (SIMP_TAC [Session.listDefs.ALL, N_IS_INT_2]),
        (ONCE_REWRITE_TAC [Pm_eqn5.POLY_MUL_ITER]) THEN BETA_TAC THEN
        (MATCH_MP_TAC ALL_IS_INT_POLY_MUL) THEN CONJ_TAC THENL
        [(ACCEPT_TAC FOOBAR_LEMMA), (ASM_SIMP_TAC [])]])
  : ExceptT String IO thm).run
#eval replay ALL_IS_INT_POLY_MUL_ITER

def ALL_IS_INT_POLY_EXP : thm := keep "ALL_IS_INT_POLY_EXP" fun _ => (do
  let lem01 ← HolLight.ASSUME ([[! p. ALL integer p ==> ALL integer (poly_exp p n)]])
  let lem02 ← HolLight.ASSUME ([[ ALL integer p]])
  let lem03 ← HolLight.MP (← HolLight.SPEC_ALL lem01) lem02
  let lem04 ← HolLight.CONJ lem02 lem03
  let lem05 ← HolLight.MATCH_MP ALL_IS_INT_POLY_MUL lem04
  prove ([[!n p. (ALL integer p) ==> (ALL integer (poly_exp p n))]])
   (INDUCT_TAC THENL
      [(ONCE_REWRITE_TAC [poly_exp]) THEN (ONCE_REWRITE_TAC [Session.listDefs.ALL]) THEN
        (ONCE_REWRITE_TAC [Session.listDefs.ALL]) THEN (SIMP_TAC [(← HolLight.SPEC ([[1]]) N_IS_INT_2)]),
        (ONCE_REWRITE_TAC [poly_exp]) THEN (REPEAT STRIP_TAC) THEN (ACCEPT_TAC lem05)])
  : ExceptT String IO thm).run
#eval replay ALL_IS_INT_POLY_EXP

def BLAHBLAH : thm := keep "BLAHBLAH" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[(SUC x) <= (SUC y) <=> x <= y]])
  let h1 ← rr (← ExceptT.mk [[&0 * h + h' = h']])
  prove ([[! p1 p2. (LENGTH p1 <= LENGTH p2) ==> (&0 ## p1 ++ p2) = p2]])
   (LIST_INDUCT_TAC THENL
       [(SIMP_TAC [Session.listDefs.LENGTH, poly_cmul, poly_add]),
         LIST_INDUCT_TAC THENL
         [(SIMP_TAC [Session.listDefs.LENGTH]) THEN ARITH_TAC,
           (ASM_SIMP_TAC [poly_cmul, poly_add, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD, Session.listDefs.TL,
                          h1, Session.listDefs.LENGTH,
                          h2])]])
  : ExceptT String IO thm).run
#eval replay BLAHBLAH

def BLAHBLAH3 : thm := keep "BLAHBLAH3" fun _ => (do
  let lem04 ← HolLight.ASSUME ([[! h t . LENGTH t <= LENGTH (poly_exp [&0;&1] n ** CONS h t)]])
  let lem05 ← HolLight.SPECL [([[h:real]]), ([[t:(real)list]])] lem04
  let lem06 ← ar (← ExceptT.mk [[!(x:num) y . x <= y ==> x <= SUC y]])
  let lem07 ← HolLight.MATCH_MP lem06 lem05
  let lem08 ← HolLight.GEN_ALL lem07
  prove ([[! n h t. (LENGTH t) <= LENGTH (poly_exp [&0;&1] n ** CONS h t)]])
   (INDUCT_TAC THENL
       [(SIMP_TAC [poly_exp, poly_mul, poly_cmul, POLY_CMUL_LID, Session.listDefs.LENGTH]) THEN ARITH_TAC,
         (SIMP_TAC [POLY_EXP_X_REC, poly_mul, NOT_POLY_EXP_X_NIL, poly_cmul, poly_add, Session.listThms1.NOT_CONS_NIL, Session.listDefs.LENGTH, Session.listDefs.TL]) THEN
         (ASM_SIMP_TAC [BLAHBLAH]) THEN (ACCEPT_TAC lem08)])
  : ExceptT String IO thm).run
#eval replay BLAHBLAH3

def TELEVISION : thm := keep "TELEVISION" fun _ => (do
  let lem ← HolLight.MATCH_MP BLAHBLAH (← HolLight.SPEC_ALL BLAHBLAH3)
  prove ([[!n p.(~ (p = [])) ==>  EL n (poly_exp [&0;&1] n ** p) = HD p]])
   (INDUCT_TAC THENL
      [(SIMP_TAC [Session.listDefs.EL, poly_exp, POLY_MUL_CLAUSES]) THEN LIST_INDUCT_TAC THENL
        [(SIMP_TAC []), (SIMP_TAC [Session.listThms1.NOT_CONS_NIL, POLY_CMUL_LID])],
          (SIMP_TAC [Session.listDefs.EL, POLY_EXP_X_REC, poly_mul, NOT_POLY_EXP_X_NIL]) THEN
          LIST_INDUCT_TAC THENL
          [(SIMP_TAC []),
            (SIMP_TAC [poly_cmul, poly_add, Session.listThms1.NOT_CONS_NIL, Session.listDefs.TL, Session.listDefs.HD]) THEN
            (ASM_SIMP_TAC [lem, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD])]])
  : ExceptT String IO thm).run
#eval replay TELEVISION

def JOSHUA : thm := keep "JOSHUA" fun _ => (do
  let lem0000 ← HolLight.SPECL [([[t:(real)list]]), ([[poly_exp [&0;&1] n ** (CONS h t)]])] BLAHBLAH
  let lem0001 ← HolLight.MATCH_MP lem0000 (← HolLight.SPEC_ALL BLAHBLAH3)
  let lem0002 ← HolLight.ASSUME ([[! n p . ~(p = []) /\ i < n ==> EL i (poly_exp [&0;&1] n ** p) = &0]])
  let lem0003 ← ExceptT.mk (Session.SIMP_RULE [Session.listThms1.NOT_CONS_NIL] (← HolLight.SPECL [([[n:num]]), ([[(CONS (h:real) t)]])] lem0002))
  let h1 ← ar (← ExceptT.mk [[(SUC i) < (SUC n) <=> i < n]])
  prove ([[!i n p.(~ (p = [])) /\ (i < n) ==>  EL i (poly_exp [&0;&1] n ** p) = &0]])
   (INDUCT_TAC THENL
      [INDUCT_TAC THENL
        [ARITH_TAC,
          LIST_INDUCT_TAC THENL
          [(SIMP_TAC []),
            (SIMP_TAC [POLY_EXP_X_REC, Session.listDefs.EL, Session.listDefs.HD, poly_mul, NOT_POLY_EXP_NIL, Session.listThms1.NOT_CONS_NIL, HD_POLY_ADD, poly_cmul]) THEN
             REAL_ARITH_TAC2]],
        INDUCT_TAC THENL
        [ARITH_TAC,
         (SIMP_TAC [Session.listDefs.EL, POLY_EXP_X_REC, poly_mul, NOT_POLY_EXP_NIL, Session.listThms1.NOT_CONS_NIL]) THEN
         LIST_INDUCT_TAC THENL
         [(SIMP_TAC []),
           (SIMP_TAC [poly_cmul, poly_add, Session.listThms1.NOT_CONS_NIL, Session.listDefs.TL, lem0001]) THEN
           (SIMP_TAC [h1, lem0003])]]])
  : ExceptT String IO thm).run
#eval replay JOSHUA

def POLY_MUL_HD : thm := keep "POLY_MUL_HD" fun _ => (do
  prove ([[! p1 p2. (~(p1 = []) /\ ~(p2 = [])) ==> (HD (p1 ** p2)) = (HD p1) * (HD p2)]])
   (LIST_INDUCT_TAC THENL
      [(SIMP_TAC []),
        LIST_INDUCT_TAC THENL
        [(SIMP_TAC []),
          (SIMP_TAC [Session.listThms1.NOT_CONS_NIL]) THEN (ONCE_REWRITE_TAC [poly_mul]) THEN
          (ASM_CASES_TAC ([[(t:(real)list) = [] ]])) THENL
          [(ASM_SIMP_TAC [Session.listDefs.HD, poly_cmul]),
            (ASM_SIMP_TAC [Session.listDefs.HD, poly_cmul, poly_add]) THEN
            (SIMP_TAC [Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD]) THEN REAL_ARITH_TAC2]]])
  : ExceptT String IO thm).run
#eval replay POLY_MUL_HD

def POLY_MUL_ITER_HD_FACTORIAL : thm := keep "POLY_MUL_ITER_HD_FACTORIAL" fun _ => (do
  let lem01 ← prove ([[~([-- &(SUC n); &1] = [])]])
     (SIMP_TAC [Session.listThms1.NOT_CONS_NIL])
  let lem02 ← HolLight.ISPECL [([[[-- &(SUC n); &1] ]]), ([[poly_mul_iter (\i.[-- &i; &1]) n]])] POLY_MUL_HD
  let lem03 ← HolLight.CONJ lem01 (← HolLight.SPEC_ALL NOT_POLY_MUL_ITER_NIL)
  let lem04 ← HolLight.MP lem02 lem03
  let lem05 ← prove ([[!n. ((-- &1) pow n) = -- ((-- &1) pow (SUC n))]])
     (STRIP_TAC THEN (ONCE_REWRITE_TAC [pow]) THEN REAL_ARITH_TAC2)
  prove ([[! n. (HD (poly_mul_iter (\i.[-- &i; &1]) n)) = ((-- &1) pow n) * (&(FACT n))]])
   (INDUCT_TAC THENL
      [(ONCE_REWRITE_TAC [Pm_eqn5.POLY_MUL_ITER]) THEN (SIMP_TAC [Session.listDefs.HD, FACT]) THEN REAL_ARITH_TAC2,
        (ONCE_REWRITE_TAC [Pm_eqn5.POLY_MUL_ITER]) THEN BETA_TAC THEN
        (ONCE_REWRITE_TAC [lem04]) THEN (ONCE_REWRITE_TAC [Session.listDefs.HD]) THEN
        (ASM_SIMP_TAC []) THEN (ONCE_REWRITE_TAC [FACT]) THEN
        (ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_MUL)]) THEN
        (CONV_TAC (HolLight.RATOR_CONV (HolLight.ONCE_REWRITE_CONV [lem05]))) THEN REAL_ARITH_TAC2])
  : ExceptT String IO thm).run
#eval replay POLY_MUL_ITER_HD_FACTORIAL

def PLANETMATH_THM_5_1 : thm := keep "PLANETMATH_THM_5_1" fun _ => (do
  let lem01 ← HolLight.SPECL [([[poly_exp [&0;&1] (p - 1)]]), ([[poly_exp (poly_mul_iter (\i.[-- &i; &1]) n) p]])] ALL_IS_INT_POLY_MUL
  let lem02 ← HolLight.SPECL [([[p-1]]), ([[[&0;&1] ]])] ALL_IS_INT_POLY_EXP
  let lem03 ← prove ([[ALL integer [&0;&1] ]])
     ((REWRITE_TAC [Session.listDefs.ALL]) THEN (SIMP_TAC [N_IS_INT_2]))
  let lem04 ← HolLight.MP lem02 lem03
  let lem05 ← HolLight.SPECL [([[p:num]]), ([[poly_mul_iter (\i.[-- &i; &1]) n]])] ALL_IS_INT_POLY_EXP
  let lem06 ← HolLight.MP lem05 (← HolLight.SPEC_ALL ALL_IS_INT_POLY_MUL_ITER)
  let lem07 ← HolLight.MP lem01 (← HolLight.CONJ lem04 lem06)
  let lem08 ← HolLight.SPECL [([[p-1]]), ([[poly_exp (poly_mul_iter (\i.[-- &i; &1]) n) p]])] TELEVISION
  let lem09 ← ExceptT.mk (Session.SIMP_RULE [NOT_POLY_EXP_NIL, NOT_POLY_MUL_ITER_NIL] lem08)
  let lem10 ← HolLight.SPECL [([[i:num]]), ([[p - 1]]), ([[poly_exp (poly_mul_iter (\i. [ -- &i; &1]) n ) p]])] JOSHUA
  let lem11 ← ExceptT.mk (Session.SIMP_RULE [NOT_POLY_MUL_ITER_NIL, NOT_POLY_EXP_NIL] lem10)
  let h2 ← rr (← ExceptT.mk [[&1 * &1 = &1]])
  let h1 ← ar (← ExceptT.mk [[0 * p = 0]])
  prove ([[! n p.
       p > 0 ==>
       n > 0 ==>
       ? As .
          ((g n p) = (&1/(&(FACT (p  - 1)))) ## As)
       /\ (! i. i< (p-1) ==> (EL i As) = &0)
       /\ ((EL (p-1) As) = ((-- &1) pow (n * p)) * ((&(FACT n)) pow p))
       /\ (ALL integer As)]])
   ((REPEAT STRIP_TAC) THEN
      (EXISTS_TAC ([[((poly_exp [&0;&1] (p-1)) ** (poly_exp (poly_mul_iter (\i.[-- &i; &1]) n) p))]])) THEN
      CONJ_TAC THENL
      [(ONCE_REWRITE_TAC [Pm_eqn5.PLANETMATH_EQN_5]) THEN (SIMP_TAC []),
        CONJ_TAC THENL
        [(SIMP_TAC [lem11]),
          CONJ_TAC THENL
          [(ONCE_REWRITE_TAC [lem09]) THEN
            (SPEC_TAC (([[n:num]]), ([[n:num]]))) THEN
            INDUCT_TAC THENL
            [(SIMP_TAC [Session.listThms1.NOT_CONS_NIL, HD_POLY_EXP, Session.listDefs.HD, Pm_eqn5.POLY_MUL_ITER, FACT, pow,
                         REAL_POW_ONE, h1, h2]),
              (SIMP_TAC [HD_POLY_EXP, NOT_POLY_MUL_ITER_NIL, POLY_MUL_ITER_HD_FACTORIAL]) THEN
              (SIMP_TAC [REAL_POW_MUL, REAL_POW_POW, BLAHBLAH3])],
            ACCEPT_TAC lem07]]])
  : ExceptT String IO thm).run
#eval replay PLANETMATH_THM_5_1

def as_def : thm := keep "as_def" fun _ => (do
  let ll01 ← HolLight.SPEC_ALL PLANETMATH_THM_5_1
  let FO_LEMMA1 ← prove ([[((p > 0) ==> (n > 0) ==> (? z. C p n z))
                            <=> (? z. (p > 0) ==> (n > 0) ==> C p n z)]])
     (MESON_TAC [])
  let ll02 ← HolLight.GEN_ALL (← ExceptT.mk (Session.SIMP_RULE [FO_LEMMA1] ll01))
  let ll03 ← HolLight.ONCE_REWRITE_RULE [SKOLEM_CONV (concl ll02)] ll02
  ExceptT.mk (Session.new_specification ["As"] ll03)
  : ExceptT String IO thm).run
#eval replay as_def

def g_eq_As : thm := keep "g_eq_As" fun _ => (do
  (HolLight.GEN_ALL o HolLight.DISCH_ALL o HolLight.CONJUNCT1 o HolLight.UNDISCH o HolLight.UNDISCH o HolLight.SPEC_ALL) as_def
  : ExceptT String IO thm).run
#eval replay g_eq_As

def prefix_As_zero : thm := keep "prefix_As_zero" fun _ => (do
  (HolLight.GEN_ALL o HolLight.DISCH_ALL o HolLight.CONJUNCT1 o HolLight.CONJUNCT2 o HolLight.UNDISCH o HolLight.UNDISCH o HolLight.SPEC_ALL) as_def
  : ExceptT String IO thm).run
#eval replay prefix_As_zero

def fact_As : thm := keep "fact_As" fun _ => (do
  (HolLight.GEN_ALL o HolLight.DISCH_ALL o HolLight.CONJUNCT1 o HolLight.CONJUNCT2 o HolLight.CONJUNCT2 o HolLight.UNDISCH o HolLight.UNDISCH o HolLight.SPEC_ALL) as_def
  : ExceptT String IO thm).run
#eval replay fact_As

def ALL_integer_As : thm := keep "ALL_integer_As" fun _ => (do
  (HolLight.GEN_ALL o HolLight.DISCH_ALL o HolLight.CONJUNCT2 o HolLight.CONJUNCT2 o HolLight.CONJUNCT2 o HolLight.UNDISCH o HolLight.UNDISCH o HolLight.SPEC_ALL) as_def
  : ExceptT String IO thm).run
#eval replay ALL_integer_As

def POLY_DIFF_AUX_LEM1 : thm := keep "POLY_DIFF_AUX_LEM1" fun _ => (do
  let lem0001 ← HolLight.ASSUME ([[! p k . i < LENGTH p ==> EL i (poly_diff_aux k p ) = EL i p * &(i + k)]])
  let lem0002 ← HolLight.SPECL [([[ t:(real)list]]), ([[SUC k]])] lem0001
  let lem0003 ← prove ([[SUC i < LENGTH (CONS (h:real) t) <=> i < LENGTH t]])
     ((SIMP_TAC [Session.listDefs.LENGTH]) THEN ARITH_TAC)
  let h2 ← ar (← ExceptT.mk [[i + SUC k = SUC i + k]])
  let h1 ← ar (← ExceptT.mk [[0 + k = k]])
  prove ([[! i p k. i < (LENGTH p) ==> EL i (poly_diff_aux k p) = (EL i p) * &(i + k)]])
   (INDUCT_TAC THENL
      [LIST_INDUCT_TAC THENL
        [(SIMP_TAC [poly_diff_aux, Session.listDefs.LENGTH]) THEN ARITH_TAC,
          (SIMP_TAC [poly_diff_aux, h1, poly_diff, Session.listDefs.LENGTH, Session.listDefs.EL, Session.listDefs.HD, Session.listDefs.TL]) THEN REAL_ARITH_TAC2],
        LIST_INDUCT_TAC THENL
        [(SIMP_TAC [Session.listDefs.LENGTH]) THEN ARITH_TAC,
          (SIMP_TAC [poly_diff_aux, Session.listDefs.EL, Session.listDefs.TL]) THEN STRIP_TAC THEN
          (SIMP_TAC [lem0003, lem0002, h2])]])
  : ExceptT String IO thm).run
#eval replay POLY_DIFF_AUX_LEM1

def EL_POLY_DIFF : thm := keep "EL_POLY_DIFF" fun _ => (do
  let lem01 ← HolLight.SPECL [([[SUC i]]), ([[t:(real)list]]), ([[1]])] POLY_DIFF_AUX_LEM1
  let h4 ← rr (← ExceptT.mk [[&1 * h = h]])
  let h3 ← rr (← ExceptT.mk [[&1 * h = h]])
  let h2 ← rr (← ExceptT.mk [[x * &1 = x]])
  let h1 ← ar (← ExceptT.mk [[SUC 0 = 1]])
  prove ([[! i p. i < (LENGTH (poly_diff p)) ==> EL i (poly_diff p) = (EL (SUC i) p) * &(SUC i)]])
   (INDUCT_TAC THENL
      [LIST_INDUCT_TAC THENL
        [((SIMP_TAC [Session.listDefs.LENGTH, poly_diff]) THEN ARITH_TAC),
          (SIMP_TAC [Session.listDefs.LENGTH, PRE, Session.listDefs.EL, Session.listDefs.HD, Session.listDefs.TL, h1, h2, poly_diff, Session.listThms1.NOT_CONS_NIL]) THEN
          (SPEC_TAC (([[t:(real)list]]), ([[t:(real)list]]))) THEN
          LIST_INDUCT_TAC THENL [(SIMP_TAC [Session.listDefs.LENGTH, poly_diff_aux]) THEN ARITH_TAC,
                                 (SIMP_TAC [Session.listDefs.HD, poly_diff_aux, h3])]],
       LIST_INDUCT_TAC THENL
       [((SIMP_TAC [Session.listDefs.LENGTH, Session.listDefs.HD, poly_diff, h4])) THEN ARITH_TAC,
          (SIMP_TAC [poly_diff, Session.listThms1.NOT_CONS_NIL, Session.listDefs.TL, LENGTH_POLY_DIFF_AUX]) THEN (SIMP_TAC [lem01, Session.listDefs.EL, Session.listDefs.TL]) THEN ARITH_TAC]])
  : ExceptT String IO thm).run
#eval replay EL_POLY_DIFF

def POLY_AT_ZERO : thm := keep "POLY_AT_ZERO" fun _ => (do
  prove ([[!p .(~(p = [])) ==> poly p (&0) = HD p]])
   (LIST_INDUCT_TAC THENL [SIMP_TAC [], (SIMP_TAC [poly, Session.listDefs.HD]) THEN REAL_ARITH_TAC2])
  : ExceptT String IO thm).run
#eval replay POLY_AT_ZERO

-- let PDI_POLY_DIFF_COMM = ... (rebinds PDI_POLY_DIFF_COMM)
def PDI_POLY_DIFF_COMM_2 : thm := keep "PDI_POLY_DIFF_COMM_2" fun _ => (do
  prove ([[! p n.(poly_diff_iter (poly_diff p) n) = (poly_diff (poly_diff_iter p n))]])
   (STRIP_TAC THEN INDUCT_TAC THENL
      [(SIMP_TAC [Pm_lemma1.PDI_DEF]),
       (ONCE_REWRITE_TAC [Pm_lemma1.PDI_DEF]) THEN (ASM_SIMP_TAC [])])
  : ExceptT String IO thm).run
#eval replay PDI_POLY_DIFF_COMM_2

def EL_PDI_AT_ZERO : thm := keep "EL_PDI_AT_ZERO" fun _ => (do
  let lem03 ← prove ([[SUC i < LENGTH (CONS (h:real) t) <=> i < LENGTH t]])
     ((SIMP_TAC [Session.listDefs.LENGTH]) THEN ARITH_TAC)
  let lem04 ← HolLight.ASSUME ([[!p . i < LENGTH p ==> poly (poly_diff_iter p i) (&0) = EL i p * &(FACT i)]])
  let lem05 ← ExceptT.mk (Session.SIMP_RULE [LENGTH_POLY_DIFF, Session.listDefs.LENGTH, PRE] (← HolLight.SPEC ([[poly_diff (CONS h t)]]) lem04))
  let lem06 ← prove ([[i < LENGTH t ==> i < LENGTH (poly_diff (CONS h t))]])
     (SIMP_TAC [LENGTH_POLY_DIFF, PRE, Session.listDefs.LENGTH])
  prove ([[!i p. (i < (LENGTH p))
         ==> ( poly (poly_diff_iter p i) (&0)) = ((EL i p) * (&(FACT i)))]])
   (INDUCT_TAC THENL
      [(LIST_INDUCT_TAC THENL
        [(SIMP_TAC [Session.listDefs.LENGTH]) THEN ARITH_TAC, (SIMP_TAC [Pm_lemma1.PDI_DEF, FACT, Session.listDefs.EL, Session.listThms1.NOT_CONS_NIL, POLY_AT_ZERO]) THEN REAL_ARITH_TAC2]),
        LIST_INDUCT_TAC THENL
        [(SIMP_TAC [Session.listDefs.LENGTH]) THEN ARITH_TAC,
          (SIMP_TAC [Pm_lemma1.PDI_DEF, (← HolLight.GSYM PDI_POLY_DIFF_COMM_2), lem03, lem05]) THEN
          (SIMP_TAC [lem06, EL_POLY_DIFF, FACT, REAL_OF_NUM_MUL, (← HolLight.GSYM REAL_MUL_ASSOC)])]])
  : ExceptT String IO thm).run
#eval replay EL_PDI_AT_ZERO

def EL_PDI_AT_ZERO2 : thm := keep "EL_PDI_AT_ZERO2" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[(i <= (SUC x) -1) <=> (i < (SUC x))]])
  prove ([[!i p. ((~ (p = [])) /\ (i <= (LENGTH p) - 1)) ==> ( poly (poly_diff_iter p i) (&0)) = ((EL i p) * (&(FACT i)))]])
   (STRIP_TAC THEN LIST_INDUCT_TAC THEN
      (SIMP_TAC [Session.listThms1.NOT_CONS_NIL, Session.listDefs.LENGTH, h1, EL_PDI_AT_ZERO]))
  : ExceptT String IO thm).run
#eval replay EL_PDI_AT_ZERO2

def POLY_CMUL_PDI : thm := keep "POLY_CMUL_PDI" fun _ => (do
  prove ([[!p c i. (poly_diff_iter (c ## p) i) = c ##(poly_diff_iter p i)]])
   (STRIP_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN (ASM_SIMP_TAC [Pm_lemma1.PDI_DEF, POLY_CMUL_POLY_DIFF]))
  : ExceptT String IO thm).run
#eval replay POLY_CMUL_PDI

def LENGTH_g : thm := keep "LENGTH_g" fun _ => (do
  let lem00 ← ar (← ExceptT.mk [[SUC ((SUC p ) - 1) = SUC p]])
  let lem01 ← prove ([[! n p. ~((poly_exp (poly_mul_iter (\i.[-- &i; &1]) n ) (SUC p)) = [])]])
     (SIMP_TAC [NOT_POLY_EXP_NIL, NOT_POLY_MUL_ITER_NIL])
  let lem02 ← HolLight.MATCH_MP POLY_MUL_LENGTH2 (← HolLight.SPEC_ALL lem01)
  let lem03 ← HolLight.SPECL [([[poly_exp [&0;&1] (SUC p - 1)]])] lem02
  let lem04 ← ExceptT.mk (Session.SIMP_RULE [POLY_EXP_X_LENGTH] lem03)
  let lem05 ← ExceptT.mk (Session.SIMP_RULE [lem00] lem04)
  prove ([[! n p . (LENGTH (g n p)) >= p ]])
   ((SIMP_TAC [Pm_eqn5.PLANETMATH_EQN_5, POLY_CMUL_LENGTH]) THEN STRIP_TAC THEN INDUCT_TAC THENL
       [ARITH_TAC, SIMP_TAC [lem05]])
  : ExceptT String IO thm).run
#eval replay LENGTH_g

def LENGTH_As : thm := keep "LENGTH_As" fun _ => (do
  let lem50 ← HolLight.ADD_ASSUM ([[p > 0]]) (← HolLight.ADD_ASSUM ([[n > 0]]) (← HolLight.SPEC_ALL LENGTH_g))
  let lem51 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.UNDISCH_ALL (← HolLight.SPEC_ALL g_eq_As))] lem50
  let lem52 ← HolLight.ONCE_REWRITE_RULE [POLY_CMUL_LENGTH] lem51
  prove ([[! n p . p > 0 ==> n > 0 ==> LENGTH (As n p) >= p]])
   (SIMP_TAC [lem52])
  : ExceptT String IO thm).run
#eval replay LENGTH_As

def REAL_MUL_RDIV : thm := keep "REAL_MUL_RDIV" fun _ => (do
  prove ([[!x y. ~(y = &0) ==> ((x * y) / y = x)]])
   (SIMP_TAC [real_div, (← HolLight.GSYM REAL_MUL_ASSOC), SessionLibrary.Analysis.REAL_MUL_RINV, SessionLibrary.Analysis.REAL_MUL_RID])
  : ExceptT String IO thm).run
#eval replay REAL_MUL_RDIV

def REAL_MUL_DIV_ASSOC : thm := keep "REAL_MUL_DIV_ASSOC" fun _ => (do
  prove ([[!x y z.((x * z) / y = x * (z / y))]])
   (SIMP_TAC [real_div, (← HolLight.GSYM REAL_MUL_ASSOC)])
  : ExceptT String IO thm).run
#eval replay REAL_MUL_DIV_ASSOC

def IS_INT_FACT_DIV : thm := keep "IS_INT_FACT_DIV" fun _ => (do
  let lem0 ← HolLight.SPEC_ALL (← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM (← HolLight.SPECL [([[FACT n]]), ([[0]])] REAL_OF_NUM_EQ))] FACT_NZ)
  let lem1 ← HolLight.SPECL [([[&(SUC n)]]), ([[&(FACT n)]])] REAL_MUL_RDIV
  let lem2 ← HolLight.MP lem1 lem0
  let lem4 ← HolLight.ASSUME ([[! m. n >= m ==> integer (&(FACT n)/ &(FACT m))]])
  let lem5 ← HolLight.UNDISCH (← HolLight.SPEC_ALL lem4)
  let lem6 ← prove ([[integer(&(SUC n))]])
     (SIMP_TAC [N_IS_INT_2])
  let lem7 ← HolLight.CONJ lem6 lem5
  let lem8 ← HolLight.MATCH_MP INTEGER_MUL lem7
  let lem9 ← HolLight.UNDISCH_ALL (← ar (← ExceptT.mk [[(~(n >= m)) ==> (SUC n >= m) ==>  m = SUC n]]))
  let h1 ← ar (← ExceptT.mk [[0 >= m ==> m = 0]])
  prove ([[! n m. n >= m ==> integer ( (&(FACT n))/(&(FACT m)) )]])
   (INDUCT_TAC THENL
      [(SIMP_TAC [h1, FACT_NZ, REAL_OF_NUM_EQ, REAL_DIV_REFL, N_IS_INT_2]),
        STRIP_TAC THEN (ASM_CASES_TAC ([[(n:num) >= m]])) THENL
        [(ASM_SIMP_TAC [FACT, (← HolLight.GSYM REAL_OF_NUM_MUL), lem2, N_IS_INT_2]) THEN
          (SIMP_TAC [FACT, (← HolLight.GSYM REAL_OF_NUM_MUL), REAL_MUL_DIV_ASSOC, lem8]),
          STRIP_TAC THEN
          (SIMP_TAC [lem9, FACT_NZ, REAL_OF_NUM_EQ, REAL_DIV_REFL, N_IS_INT_2])]])
  : ExceptT String IO thm).run
#eval replay IS_INT_FACT_DIV

def SATURDAY_LEMMA : thm := keep "SATURDAY_LEMMA" fun _ => (do
  let lem01 ← HolLight.UNDISCH (← ar (← ExceptT.mk [[p > 1 ==> SUC (p -1) = p]]))
  let lem02 ← HolLight.ADD_ASSUM ([[p > 1]]) (← HolLight.SPEC ([[p - 1]]) (← HolLight.CONJUNCT2 FACT))
  let lem03 ← HolLight.GSYM (← HolLight.ONCE_REWRITE_RULE [lem01] lem02)
  let lem04 ← HolLight.SPEC ([[&p]]) REAL_DIV_REFL
  let lem05 ← HolLight.ADD_ASSUM ([[p > 1]]) (← HolLight.SPECL [([[p:num]]), ([[0]])] REAL_OF_NUM_EQ)
  let lem06 ← ExceptT.mk (Session.SIMP_RULE [(← HolLight.UNDISCH (← ar (← ExceptT.mk [[p > 1 ==> ~(p = 0)]])))] lem05)
  let lem07 ← HolLight.GSYM (← HolLight.MP lem04 lem06)
  let h1 ← rr (← ExceptT.mk [[((x1:real) * x2) * x * (x3 * x4) = x * x1 * (x3 * (x2 * x4))]])
  prove ([[!x. p > 1 ==> m >= p ==> x * ((&(FACT m))/(&(FACT (p-1)))) = x * (&p) * ((&(FACT m))/(&(FACT p)))]])
   ((REPEAT STRIP_TAC) THEN
      (CONV_TAC (HolLight.RATOR_CONV (HolLight.ONCE_REWRITE_CONV [(← HolLight.GSYM REAL_MUL_LID)]))) THEN
      (ONCE_REWRITE_TAC [lem07]) THEN
      (ONCE_REWRITE_TAC [real_div]) THEN
      (ONCE_REWRITE_TAC [h1]) THEN
      (ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_INV_MUL)]) THEN
      (ONCE_REWRITE_TAC [REAL_OF_NUM_MUL]) THEN
      (SIMP_TAC [REAL_MUL_ASSOC, (← HolLight.GSYM REAL_INV_MUL)]) THEN
      (ONCE_REWRITE_TAC [lem03]) THEN
      (SIMP_TAC [REAL_MUL_ASSOC, (← HolLight.GSYM REAL_OF_NUM_MUL)]))
  : ExceptT String IO thm).run
#eval replay SATURDAY_LEMMA

def SHRIVER : thm := keep "SHRIVER" fun _ => (do
  let lem01 ← HolLight.UNDISCH_ALL (← ar (← ExceptT.mk [[i <= n ==> i <= SUC n]]))
  let lem02 ← HolLight.CONJ (← HolLight.ASSUME ([[(m:num) <= (i:num)]])) lem01
  let lem03 ← HolLight.ASSUME ([[!i. m <= i /\ i <= SUC n ==> (f0 i)]])
  let lem04 ← HolLight.SPEC_ALL lem03
  let lem05 ← HolLight.MP lem04 lem02
  prove ([[!f0. (!i. m <= i /\ i <= SUC n ==> (f0 i))
       ==> (!i. m <= i /\ i <= n ==> (f0 i)) ]])
   ((REPEAT STRIP_TAC) THEN (ACCEPT_TAC lem05))
  : ExceptT String IO thm).run
#eval replay SHRIVER

def IS_INT_SUM : thm := keep "IS_INT_SUM" fun _ => (do
  let l0 ← HolLight.SPECL [([[m:num]]), ([[n:num]]), ([[i:num]])] IN_NUMSEG
  let l1 ← HolLight.SPECL [([[m:num]]), ([[SUC n]])] NUMSEG_EMPTY
  let l2 ← HolLight.ADD_ASSUM ([[SUC n < m]]) l1
  let l3 := ASM_REWRITE_RULE [] l2
  let l4 ← (HolLight.UNDISCH o ar) ([[~(SUC n < m) ==> m <= SUC n]])
  let l5 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM IN_NUMSEG)] SHRIVER
  let l6 ← HolLight.SPEC ([[\(i:num).(integer (f i))]]) l5
  let l7 ← HolLight.BETA_RULE l6
  let l8 ← HolLight.ASSUME ([[! m. (!i. i IN m..n ==> integer (f i)) ==> integer (sum (m..n) f)]])
  let l9 ← HolLight.SPEC_ALL l8
  let l10 ← HolLight.UNDISCH (← HolLight.IMP_TRANS l7 l9)
  let jj0 ← ar (← ExceptT.mk [[(~(SUC n < m)) ==> m <= SUC n /\ (SUC n) <= SUC n]])
  let jj1 ← HolLight.UNDISCH (← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM IN_NUMSEG)] jj0)
  let jj2 ← HolLight.SPEC ([[SUC n]]) (← HolLight.ASSUME ([[!i. i IN m.. SUC n ==> integer (f i)]]))
  let jj3 ← HolLight.MP jj2 jj1
  let l18 ← HolLight.CONJ l10 jj3
  let l19 ← HolLight.MATCH_MP INTEGER_ADD l18
  let l20 ← HolLight.DISCH ([[!i. i IN m..SUC n ==> integer (f i)]]) l19
  let l21 ← HolLight.ASSUME ([[!i . i = 0 ==> integer (f 0)]])
  let l22 ← ExceptT.mk (Session.SIMP_RULE [] (← HolLight.SPEC ([[0]]) l21))
  prove ([[!f n m.(!i.m <= i /\  i <= n ==> integer (f i)) ==> integer (sum (m..n) f)]])
   ((ONCE_REWRITE_TAC [(← HolLight.GSYM l0)]) THEN STRIP_TAC THEN
    INDUCT_TAC THENL
    [STRIP_TAC THEN
      (ASM_CASES_TAC ([[m = 0]])) THENL
      [(ASM_SIMP_TAC []) THEN
        (ONCE_REWRITE_TAC [NUMSEG_CONV ([[0..0]])]) THEN
        (ONCE_REWRITE_TAC [SUM_SING]) THEN
        (SIMP_TAC [IN_SING]) THEN DISCH_TAC THEN (SIMP_TAC [l22]),
        (ASM_SIMP_TAC [NUMSEG_CLAUSES, SUM_CLAUSES, N_IS_INT_2])],
      STRIP_TAC THEN (ASM_CASES_TAC ([[SUC n < m]])) THENL
      [(ASM_SIMP_TAC [l3, SUM_CLAUSES, N_IS_INT_2]),
        (ASM_SIMP_TAC [l4, SUM_CLAUSES_NUMSEG]) THEN
        (ACCEPT_TAC l20)]])
  : ExceptT String IO thm).run
#eval replay IS_INT_SUM

def ALL_IMP_EL : thm := keep "ALL_IMP_EL" fun _ => (do
  prove ([[! (l:(a)list) i P. (ALL P l) ==> (i < LENGTH l) ==> P (EL i l)]])
   (SIMP_TAC [(← HolLight.GSYM Session.listThms2.ALL_EL)])
  : ExceptT String IO thm).run
#eval replay ALL_IMP_EL

def KEY_LEMMA : thm := keep "KEY_LEMMA" fun _ => (do
  let jem0 ← HolLight.ISPECL [([[(As n p)]]), ([[i:num]]), ([[integer]])] ALL_IMP_EL
  let jem1 ← HolLight.MP jem0 (← HolLight.UNDISCH (← HolLight.UNDISCH (← HolLight.SPEC_ALL ALL_integer_As)))
  let jem3 ← ar (← ExceptT.mk [[LENGTH (As n p) > 0 ==> ((i < LENGTH (As n p)) <=> i <= LENGTH (As n p) - 1)]])
  let jem4 ← HolLight.UNDISCH_ALL (← HolLight.SPEC_ALL LENGTH_As)
  let jem5 ← HolLight.UNDISCH (← ar (← ExceptT.mk [[p > 0 ==> (LENGTH (As n p) >= p) ==> (LENGTH (As n p) > 0)]]))
  let jem6 ← HolLight.MP jem5 jem4
  let jem7 ← HolLight.MP jem3 jem6
  let jem8 ← HolLight.ONCE_REWRITE_RULE [jem7] jem1
  let kem0 ← HolLight.SPECL [([[i:num]]), ([[p:num]])] IS_INT_FACT_DIV
  let kem1 ← HolLight.ADD_ASSUM ([[p <= (i:num)]]) (← HolLight.ADD_ASSUM ([[i <= (LENGTH (As n p) - 1)]]) kem0)
  let kem2 ← ExceptT.mk (Session.SIMP_RULE [(← HolLight.UNDISCH_ALL (← ar (← ExceptT.mk [[p <= i ==> i <= LENGTH (As n p) -1 ==> i >= p]])))] kem1)
  prove ([[n > 0 ==>
     p > 0 ==>
    ! i . p <= i /\ i <= (LENGTH (As n p) - 1) ==> integer ((&(FACT i)/ &(FACT p)) * (EL i (As n p)))]])
   ((REPEAT STRIP_TAC) THEN (SIMP_TAC [(← HolLight.UNDISCH jem8), kem2, INTEGER_MUL]))
  : ExceptT String IO thm).run
#eval replay KEY_LEMMA

def KEY_LEMMA2 : thm := keep "KEY_LEMMA2" fun _ => (do
  let lem0000 ← HolLight.SPEC ([[EL m (As n p)]]) SATURDAY_LEMMA
  let lem1000 ← HolLight.DISCH ([[m <= LENGTH (As n p) -1]]) (← HolLight.ADD_ASSUM ([[m <= LENGTH (As n p) -1]]) (← HolLight.UNDISCH_ALL lem0000))
  let lem2000 ← HolLight.DISCH ([[(m:num) >= p]]) lem1000
  let lem3000 ← HolLight.ONCE_REWRITE_RULE [(← ar (← ExceptT.mk [[(m:num) >= p <=> p <= m]]))] lem2000
  let lem4000 ← HolLight.ONCE_REWRITE_RULE [(← tt (← ExceptT.mk [[(a ==> b ==> c) <=> ((a  /\ b) ==> c)]]))] (← HolLight.GEN ([[m:num]]) lem3000)
  let lem5000 ← HolLight.MATCH_MP SUM_EQ_NUMSEG lem4000
  let nem2 ← HolLight.SPECL [([[\x.(&(FACT x)/ &(FACT p)) * (EL x (As n p))]]), ([[LENGTH (As n p) - 1]]), ([[p:num]])] IS_INT_SUM
  let nem3 ← HolLight.BETA_RULE nem2
  let nem4 ← ExceptT.mk (Session.SIMP_RULE [(← HolLight.UNDISCH (← HolLight.UNDISCH KEY_LEMMA))] nem3)
  let nem5 ← HolLight.ADD_ASSUM ([[p > 1]]) (← HolLight.DISCH ([[p > 0]]) nem4)
  let nem6 ← ExceptT.mk (Session.SIMP_RULE [(← (HolLight.UNDISCH o ar) ([[(p:num) > 1 ==> p > 0]]))] nem5)
  let h2 ← rr (← ExceptT.mk [[(x1:real) * x2 * x3 = x2 * (x3 * x1)]])
  let h1 ← rr (← ExceptT.mk [[(x1:real) * x2 * x3 = x2 * (x3 * x1)]])
  prove ([[p > 1 ==>
     n > 0 ==>
     ? K0 .   integer K0
           /\ (&1 / &(FACT ( p - 1))) * (sum (p.. LENGTH (As n p) -1) (\m. EL m (As n p) * &(FACT m))) = (&p) * K0]])
   (STRIP_TAC THEN STRIP_TAC THEN (ONCE_REWRITE_TAC [(← HolLight.GSYM SUM_LMUL)]) THEN
      BETA_TAC THEN (ONCE_REWRITE_TAC [real_div]) THEN (ONCE_REWRITE_TAC [REAL_MUL_LID]) THEN
      (ONCE_REWRITE_TAC [h1]) THEN
      (ONCE_REWRITE_TAC [(← HolLight.GSYM real_div)]) THEN (ONCE_REWRITE_TAC [lem5000]) THEN
      (ONCE_REWRITE_TAC [h2]) THEN
      (ONCE_REWRITE_TAC [SUM_LMUL]) THEN
      (EXISTS_TAC ([[sum (p .. LENGTH (As n p) -1) (\x. &(FACT x) / &(FACT p) * EL x (As n p))]])) THEN
      (SIMP_TAC [nem6]))
  : ExceptT String IO thm).run
#eval replay KEY_LEMMA2

def NOT_g_NIL : thm := keep "NOT_g_NIL" fun _ => (do
  prove ([[!n p . ~ ((g n p ) = [])]])
   (SIMP_TAC [Pm_eqn5.PLANETMATH_EQN_5, Session.listThms1.NOT_CONS_NIL, NOT_POLY_EXP_NIL, NOT_POLY_CMUL_NIL,
                 NOT_POLY_MUL_NIL, NOT_POLY_MUL_ITER_NIL])
  : ExceptT String IO thm).run
#eval replay NOT_g_NIL

-- let FACT_DIV_RCANCELS = ... (rebinds FACT_DIV_RCANCELS)
def FACT_DIV_RCANCELS_2 : thm := keep "FACT_DIV_RCANCELS_2" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[!x. &0 < x ==> ~(x = &0)]])
  prove ([[!n x. x / &(FACT n) * &(FACT n) = x]])
   (MESON_TAC [h1,
                 REAL_DIV_RMUL, FACT_LT, REAL_OF_NUM_LT])
  : ExceptT String IO thm).run
#eval replay FACT_DIV_RCANCELS_2

-- let PSUM_ITERATE = ... (rebinds PSUM_ITERATE)
def PSUM_ITERATE_2 : thm := keep "PSUM_ITERATE_2" fun _ => (do
  let lem01 ← ar (← ExceptT.mk [[~(n+m=0) ==> (SUC n + m) -1 = SUC ((n + m) -1)]])
  let lem02 ← HolLight.MP (← HolLight.ISPEC ([[(+)]]) ITERATE_SING) MONOIDAL_REAL_ADD
  let lem03 ← prove ([[iterate (+) (m..SUC ((n + m) - 1)) f
           = f (SUC ((n+m)-1)) + iterate (+) (m..(n+m)-1) f]])
     (MESON_TAC [(← ar (← ExceptT.mk [[m <= SUC ((n+m)-1)]])), ITERATE_CLAUSES_NUMSEG,
                        MONOIDAL_REAL_ADD, REAL_ADD_SYM])
  let lem04 ← HolLight.UNDISCH (← HolLight.UNDISCH (← ar (← ExceptT.mk [[~(n+m=0) ==> n=0 ==> m-1 < m]])))
  let lem05 ← ExceptT.mk (Session.SIMP_RULE [lem04] (← HolLight.SPECL [([[m:num]]), ([[m-1]])] NUMSEG_EMPTY))
  let h7 ← ar (← ExceptT.mk [[~(n=0) ==> n>0 /\ SUC (n-1) = n]])
  let h6 ← ar (← ExceptT.mk [[~(0 > 0)]])
  let h5 ← rr (← ExceptT.mk [[&0 + x = x]])
  let h4 ← ar (← ExceptT.mk [[(SUC 0 +m) -1 = m]])
  let h3 ← ar (← ExceptT.mk [[n + m = 0 ==> n = 0]])
  let h2 ← ar (← ExceptT.mk [[(SUC n) > 0]])
  let h1 ← ar (← ExceptT.mk [[~(0 > 0)]])
  prove ([[! n m f. psum (m,n) f
              = if (n > 0) then (iterate (+) (m..((n+m)-1)) f) else &0]])
   (INDUCT_TAC THENL
      [SIMP_TAC [h1, sum_DEF],
        (SIMP_TAC [h2]) THEN (REPEAT STRIP_TAC) THEN
        (ASM_CASES_TAC ([[n + m =0]])) THENL
        [(REWRITE_TAC [(← HolLight.UNDISCH h3)]) THEN
          (REWRITE_TAC [lem02, NUMSEG_SING, h4]) THEN
          (MESON_TAC [sum_DEF, ADD_CLAUSES, h5]),
          (ONCE_REWRITE_TAC [sum_DEF, (← HolLight.UNDISCH lem01)]) THEN
          (REWRITE_TAC [lem03]) THEN (ASM_CASES_TAC ([[n = 0]])) THEN
          (ASM_SIMP_TAC [h6, ADD_CLAUSES, REAL_ADD_LID, REAL_ADD_RID,
             lem05, ITERATE_CLAUSES_GEN, MONOIDAL_REAL_ADD, NEUTRAL_REAL_ADD,
             REAL_ADD_SYM, ADD_SYM, h7])]])
  : ExceptT String IO thm).run
#eval replay PSUM_ITERATE_2

def PLANETMATH_EQN_5_2 : thm := keep "PLANETMATH_EQN_5_2" fun _ => (do
  let lem01 ← HolLight.SPECL [([[g n p]]), ([[x:real]]), ([[(&0):real]])] Pm_lemma2.PLANETMATH_LEMMA_2_B
  let lem02 ← HolLight.GEN_ALL lem01
  let lem03 ← HolLight.SPEC_ALL (← HolLight.BETA_RULE lem02)
  let lem04 ← ExceptT.mk (Session.SIMP_RULE [FACT_DIV_RCANCELS_2] lem03)
  let lem05 ← ExceptT.mk (Session.SIMP_RULE [PSUM_ITERATE_2] lem04)
  let lem06 ← ExceptT.mk (Session.SIMP_RULE [(← ar (← ExceptT.mk [[(n:num) + 0 = n]]))] lem05)
  let lem07 ← HolLight.ADD_ASSUM ([[n > 0]]) (← HolLight.ADD_ASSUM ([[p > 0]]) lem06)
  let lem08 ← HolLight.REWRITE_RULE [(← HolLight.GSYM Session.listThms1.LENGTH_EQ_NIL), (← ar (← ExceptT.mk [[~(x = 0) <=> x > 0]]))] NOT_g_NIL
  let lem09 ← ExceptT.mk (Session.SIMP_RULE [lem08] lem07)
  let lem10 ← HolLight.CONV_RULE (HolLight.RAND_CONV (HolLight.REWRITE_CONV [(← HolLight.UNDISCH_ALL (← HolLight.SPEC_ALL g_eq_As))])) lem09
  let lem11 ← ExceptT.mk (Session.SIMP_RULE [POLY_CMUL_LENGTH] lem10)
  let lem12 ← HolLight.SPECL [([[m:num]]), ([[(As n p)]])] EL_PDI_AT_ZERO
  let lem13 ← ExceptT.mk (Session.SIMP_RULE [POLY_CMUL_PDI, POLY_CMUL, lem12] lem11)
  let lem14 ← HolLight.GSYM (BETA ([[(\m. poly (poly_diff_iter (As n p) m) (&0)) m]]))
  let lem15 ← HolLight.ISPECL [([[(\m. poly (poly_diff_iter (As n p) m) (&0))]]), ([[&1/ &(FACT (p - 1))]]), ([[0..LENGTH (As n p) -1]])] SUM_LMUL
  let lem16 ← HolLight.ONCE_REWRITE_RULE [lem14] lem13
  let lem17 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM SessionLibrary.Analysis.sum)] lem16
  let lem18 ← ExceptT.mk (Session.SIMP_RULE [(← HolLight.GSYM lem17)] lem15)
  let lem20 ← HolLight.SPECL [([[(\m.  poly (poly_diff_iter (As n p) m) (&0))]]), ([[(\m. EL m (As n p) * &(FACT m))]]), ([[0]]), ([[LENGTH (As n p) - 1]])] SUM_EQ_NUMSEG
  let lem21 ← HolLight.ONCE_REWRITE_RULE [(← ar (← ExceptT.mk [[0 <= i]]))] (← HolLight.BETA_RULE lem20)
  let lem22 ← HolLight.ADD_ASSUM ([[~(As n p = [])]]) (← HolLight.ONCE_REWRITE_RULE [EL_PDI_AT_ZERO2] lem21)
  let lem30 ← HolLight.SPECL [([[i:num]]), ([[As n p]])] EL_PDI_AT_ZERO2
  let lem31 := ASM_REWRITE_RULE [] (← HolLight.ADD_ASSUM ([[~(As n p = [])]]) lem30)
  let lem23 ← HolLight.ONCE_REWRITE_RULE [lem31] lem22
  let lem24 ← HolLight.REWRITE_RULE [(← HolLight.GSYM lem16)] lem23
  let lem25 ← HolLight.ONCE_REWRITE_RULE [lem24] lem18
  let lem30 ← HolLight.ISPECL [([[\m. EL m (As n p) * &(FACT m)]]), ([[0]]), ([[p-1]]), ([[(LENGTH (As n p) - 1) - (p - 1)]])] SUM_ADD_SPLIT
  let lem31 ← ExceptT.mk (Session.SIMP_RULE [(← ar (← ExceptT.mk [[0 <= x]]))] lem30)
  let lem32 ← HolLight.UNDISCH_ALL (← ar (← ExceptT.mk [[! x. x  >= p ==> (p - 1) + (x - 1) - (p -1)=  x - 1]]))
  let lem33 ← HolLight.UNDISCH_ALL (← HolLight.SPEC_ALL LENGTH_As)
  let lem34 ← HolLight.SPEC ([[LENGTH (As n p)]]) lem32
  let lem35 ← HolLight.MP lem34 lem33
  let lem36 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.UNDISCH (← ar (← ExceptT.mk [[p > 1 ==> (p - 1) + 1 = p]]))), lem35] lem31
  let lem37 ← HolLight.ONCE_REWRITE_RULE [lem36] lem25
  let lem38 ← ExceptT.mk (Session.SIMP_RULE [(← HolLight.UNDISCH (← ar (← ExceptT.mk [[p > 1 ==> p > 0]])))] (← HolLight.DISCH ([[p > 0]]) lem37))
  let lem39 ← HolLight.ISPECL [([[\m. EL m (As n p) * &(FACT m)]]), ([[0]]), ([[p-2]]), ([[1]])] SUM_ADD_SPLIT
  let lem40 ← HolLight.ADD_ASSUM ([[n > 0]]) (← HolLight.ADD_ASSUM ([[p > 1]]) lem39)
  let lem41 ← ExceptT.mk (Session.SIMP_RULE (← mapR (HolLight.UNDISCH o ar) [([[p > 1 ==> p - 2 + 1 = p-1]]), ([[p > 1 ==> (p - 2) + 1 = p - 1]])]) lem40)
  let lem42 ← ExceptT.mk (Session.SIMP_RULE [SUM_SING_NUMSEG, (← ar (← ExceptT.mk [[0 <= x]]))] lem41)
  let lem45 ← HolLight.ADD_ASSUM ([[p > 1]]) (← HolLight.SPEC_ALL prefix_As_zero)
  let lem46 ← ExceptT.mk (Session.SIMP_RULE [(← HolLight.UNDISCH_ALL (← ar (← ExceptT.mk [[p > 1 ==> p > 0]])))] lem45)
  let lem47 ← HolLight.UNDISCH (← HolLight.ONCE_REWRITE_RULE [(← HolLight.UNDISCH_ALL (← ar (← ExceptT.mk [[p > 1 ==> (i < p-1 <=> i <= p-2)]])))] lem46)
  let lem48 ← ExceptT.mk (Session.SIMP_RULE [(← rr (← ExceptT.mk [[((&0):real) + x = x]])), SUM_EQ_0_NUMSEG, (← rr (← ExceptT.mk [[((&0):real) * x = &0]])), lem47] lem42)
  let lem49 ← ExceptT.mk (Session.SIMP_RULE [(← HolLight.UNDISCH (← ar (← ExceptT.mk [[p > 1 ==> p > 0]])))] (← HolLight.ADD_ASSUM ([[p > 1]]) (← HolLight.SPEC_ALL fact_As)))
  let lem50 ← ExceptT.mk (Session.SIMP_RULE [(← HolLight.UNDISCH lem49)] lem48)
  let lem51 ← HolLight.ONCE_REWRITE_RULE [lem50] lem38
  let lem52 ← HolLight.SPECL [([[p - 1]]), ([[(&1):real]])] FACT_DIV_RCANCELS_2
  let lem53 ← ExceptT.mk (Session.SIMP_RULE [(← rr (← ExceptT.mk [[(x:real) * (y * z) = (x * z) * y]])), lem52, (← rr (← ExceptT.mk [[(x:real) * (y + z) = (x * y) + (x * z)]]))] lem51)
  let lem54 ← ExceptT.mk (Session.SIMP_RULE [(← rr (← ExceptT.mk [[&1 * x = (x:real)]]))] lem53)
  let josh0 ← HolLight.UNDISCH_ALL KEY_LEMMA2
  let josh1 ← rr (← ExceptT.mk [[!(y:real) x1 x2 . x1  = x2 <=> y + x1 = y + x2]])
  let josh2 ← HolLight.SPEC ([[(&(FACT n) pow p * -- &1 pow (n * p)):real]]) josh1
  let josh3 ← HolLight.ONCE_REWRITE_RULE [josh2] josh0
  let josh4 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM lem54)] josh3
  let josh5 ← HolLight.DISCH ([[~ (As n p = [])]]) josh4
  let jem4 ← HolLight.ADD_ASSUM ([[p > 1]]) (← HolLight.SPEC_ALL LENGTH_As)
  let jem5 ← HolLight.UNDISCH (← ExceptT.mk (Session.SIMP_RULE [(← HolLight.UNDISCH (← ar (← ExceptT.mk [[(p:num) > 1 ==> p > 0]])))] jem4))
  let jem6 ← HolLight.UNDISCH (← ar (← ExceptT.mk [[p > 1 ==> (LENGTH (As n p) >= p) ==> ~((LENGTH (As n p) = 0))]]))
  let jem7 ← HolLight.MP jem6 jem5
  let jem8 ← ExceptT.mk (Session.SIMP_RULE [Session.listThms1.LENGTH_EQ_NIL] jem7)
  let josh6 ← HolLight.MP josh5 jem8
  let josh7 ← HolLight.DISCH_ALL josh6
  let josh11 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM OLD_SUM)] lem17
  let josh12 ← HolLight.REWRITE_RULE [(← HolLight.GSYM josh11)] josh7
  let josh13 ← ExceptT.mk (Session.SIMP_RULE [] (← HolLight.DISCH_ALL josh12))
  let josh14 ← BRW ([[(X ==> Y ==> Z ==> W) <=> ((X /\ Y /\ Z) ==> W)]]) josh13
  let josh15 ← HolLight.ONCE_REWRITE_RULE [(← ar (← ExceptT.mk [[(p > 0 /\ n > 0 /\ p > 1) <=> (p > 1 /\ n > 0)]]))] (← HolLight.DISCH_ALL josh14)
  let josh16 ← BRW1 josh15
  let josh17 ← ExceptT.mk (Session.SIMP_RULE [PSUM_ITERATE_2, (← ar (← ExceptT.mk [[~(0 > 0)]]))] josh16)
  prove ([[p > 1 ==>
     n > 0 ==>
     (? K0.   integer K0
           /\ poly (SOD (g n p)) (&0) =
              &(FACT n) pow p * -- &1 pow (n * p) + &p * K0)]])
   (ACCEPT_TAC josh17)
  : ExceptT String IO thm).run
#eval replay PLANETMATH_EQN_5_2

def PLANETMATH_DIVIDES_FACT_PRIME_1 : thm := keep "PLANETMATH_DIVIDES_FACT_PRIME_1" fun _ => (do
  prove ([[!p n. (prime p) /\ p > n ==> ~(num_divides p (FACT n))]])
   ((SIMP_TAC [DIVIDES_FACT_PRIME]) THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval replay PLANETMATH_DIVIDES_FACT_PRIME_1

def INT_OF_REAL_NEG_NUM : thm := keep "INT_OF_REAL_NEG_NUM" fun _ => (do
  prove ([[!(n:num).int_of_real (-- (real_of_num n)) = -- (int_of_real (real_of_num n))]])
   (SIMP_TAC [(← HolLight.GSYM int_of_num), (← HolLight.GSYM int_of_num_th), (← HolLight.GSYM int_neg)])
  : ExceptT String IO thm).run
#eval replay INT_OF_REAL_NEG_NUM

def ABS_EQ_ONE : thm := keep "ABS_EQ_ONE" fun _ => (do
  prove ([[!(x:real) .((abs x) = &1) ==> ((x = &1) \/ (x = -- &1))]])
   (ARITH_TAC)
  : ExceptT String IO thm).run
#eval replay ABS_EQ_ONE

def POW_NEG_1 : thm := keep "POW_NEG_1" fun _ => (do
  let lem00 ← HolLight.ONCE_REWRITE_RULE [(← tt (← ExceptT.mk [[x \/ y <=> y \/ x]]))] ABS_EQ_ONE
  let lem01 ← HolLight.SPEC ([[(-- (&1 :real)) pow x]]) lem00
  let lem02 ← HolLight.SPEC ([[x:num]]) POW_M1
  let lem03 ← HolLight.MP lem01 lem02
  prove ([[!(x:num). (((-- (&1 :real)) pow x) = -- &1) \/  (((-- (&1 : real)) pow x) = &1)]])
   (STRIP_TAC THEN (ACCEPT_TAC lem03))
  : ExceptT String IO thm).run
#eval replay POW_NEG_1

def NUM_DIVIDES_INT_DIVIDES : thm := keep "NUM_DIVIDES_INT_DIVIDES" fun _ => (do
  prove ([[!(x:num) (y:num).(x divides y) <=> ((&x):int divides ((&y):int))]])
   ((ONCE_REWRITE_TAC [num_divides]) THEN (SIMP_TAC []))
  : ExceptT String IO thm).run
#eval replay NUM_DIVIDES_INT_DIVIDES

def SON_OF_A_GUN : thm := keep "SON_OF_A_GUN" fun _ => (do
  let POW_INT_NEG_1 := INT_OF_REAL_THM POW_NEG_1
  let lem0000 ← tt (← ExceptT.mk [[(A /\ B ==> C) <=> (A ==> B ==> C)]])
  let lem0001 ← HolLight.ONCE_REWRITE_RULE [lem0000] PLANETMATH_DIVIDES_FACT_PRIME_1
  let lem0002 ← HolLight.UNDISCH_ALL (← HolLight.SPEC_ALL lem0001)
  let lem0008 ← HolLight.ONCE_REWRITE_RULE [(← tt (← ExceptT.mk [[(x /\ y ==> z) <=> (x ==> ~z ==> ~y)]]))] PRIME_DIVEXP
  let lem0009 ← HolLight.SPECL [([[p:num]]), ([[p:num]]), ([[FACT n]])] lem0008
  let lem0010 ← HolLight.UNDISCH lem0009
  let lem0011 ← HolLight.MP lem0010 lem0002
  let h5 ← ar (← ExceptT.mk [[x * ((&1):int) = x]])
  let h4 ← ar (← ExceptT.mk [[x * (--(&1):int) = -- x]])
  let h3 ← ar (← ExceptT.mk [[-- -- (x:int) = x]])
  let h2 ← ar (← ExceptT.mk [[x * ((&1):int) = x]])
  let h1 ← ar (← ExceptT.mk [[x * (--(&1):int) = -- x]])
  prove ([[! (p:num) (n:num) .
     p > n
     ==> (prime p)
     ==> ~(int_divides (& p) (&(FACT n) pow p * -- &1 pow (n * p) ))]])
   (STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
       (DISJ_CASES_TAC (← HolLight.SPEC ([[(n * p):num]]) POW_INT_NEG_1)) THENL
       [(ASM_SIMP_TAC [INT_OF_NUM_POW, h1, h2]) THEN
         (ONCE_REWRITE_TAC [(← HolLight.GSYM INT_DIVIDES_RNEG)]) THEN
         (ONCE_REWRITE_TAC [h3]) THEN
         (ONCE_REWRITE_TAC [(← HolLight.GSYM NUM_DIVIDES_INT_DIVIDES)]) THEN
         (ACCEPT_TAC lem0011),
         (ASM_SIMP_TAC [INT_OF_NUM_POW, h4, h5]) THEN
         (ONCE_REWRITE_TAC [(← HolLight.GSYM NUM_DIVIDES_INT_DIVIDES)]) THEN
         (ACCEPT_TAC lem0011)])
  : ExceptT String IO thm).run
#eval replay SON_OF_A_GUN

def MAY_LEMMA : thm := keep "MAY_LEMMA" fun _ => (do
  let lem00 ← BRW ([[(x /\ y ==> z) <=> (x ==> ~z ==> ~y)]]) INT_DIVIDES_ADD_REVR
  let lem0 ← prove ([[int_divides ((&p):int) (&p * K0)]])
     (INTEGER_TAC)
  let lem1 ← (HolLight.UNDISCH_ALL o HolLight.SPEC_ALL) SON_OF_A_GUN
  let lem2 ← HolLight.SPECL [([[(&p):int]]), ([[((&p):int) * K0]]), ([[(&(FACT n) pow p):int *
      -- &1 pow (n * p)]])] lem00
  let lem3 ← HolLight.MP (← HolLight.MP lem2 lem0) lem1
  let lem4 ← HolLight.DISCH_ALL lem3
  let lem5 ← HolLight.ONCE_REWRITE_RULE [(← ar (← ExceptT.mk [[(x:int) + y = y + x]]))] lem4
  prove ([[(p:num) > (n:num)
      ==> (prime p)
      ==> ~(int_divides (& p) ((int_of_num (FACT n)) pow p * -- &1 pow (n * p) + &p * K0))]])
   ((ACCEPT_TAC lem5))
  : ExceptT String IO thm).run
#eval replay MAY_LEMMA

def PLANET_MATH_alpha_1 : thm := keep "PLANET_MATH_alpha_1" fun _ => (do
  let a1 ← HolLight.UNDISCH (← HolLight.UNDISCH (← ar (← ExceptT.mk [[n > 0 ==> p > n ==> p > 1]])))
  let a2 ← HolLight.UNDISCH (← ExceptT.mk (Session.SIMP_RULE [] (← HolLight.DISCH ([[n > 0]]) (← HolLight.MP PLANETMATH_EQN_5_2 a1))))
  let t1 := ([[integer K0 /\
              poly (SOD (g n p)) (&0) =
              &(FACT n) pow p * -- &1 pow (n * p) + &p * K0]])
  prove ([[n > 0 ==> p > n ==> prime p ==> (integer (poly (SOD (g n p )) (&0)))]])
   ((STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC) THEN (CHOOSE_TAC a2) THEN
      (SPLIT_CONJOINED_ASSUMPT_TAC t1) THEN (ASM_REWRITE_TAC []) THEN
      (ASM_SIMP_TAC [N_IS_INT_2, INTEGER_ADD, NEG_N_IS_INT_2, INTEGER_POW, INTEGER_MUL]))
  : ExceptT String IO thm).run
#eval replay PLANET_MATH_alpha_1

def PLANET_MATH_alpha_2 : thm := keep "PLANET_MATH_alpha_2" fun _ => (do
  let t1 := ([[integer K0 /\
              poly (SOD (g n p)) (&0) =
              &(FACT n) pow p * -- &1 pow (n * p) + &p * K0]])
  let t := ([[((real_of_num (FACT n)) pow p) * (-- &1 pow (n * p)) + (&p * K0)]])
  let arch0 := INT_OF_REAL_CONV t
  let a1 ← HolLight.UNDISCH (← HolLight.UNDISCH (← ar (← ExceptT.mk [[n > 0 ==> p > n ==> p > 1]])))
  let a2 ← HolLight.UNDISCH (← ExceptT.mk (Session.SIMP_RULE [] (← HolLight.DISCH ([[n > 0]]) (← HolLight.MP PLANETMATH_EQN_5_2 a1))))
  let a3 ← HolLight.SPEC ([[int_of_real K0]]) (← HolLight.GEN ([[K0:int]]) MAY_LEMMA)
  let a4 ← HolLight.GSYM (← HolLight.UNDISCH arch0)
  let a5 ← HolLight.ONCE_REWRITE_RULE [a4] a3
  prove ([[n > 0 ==> p > n ==> prime p ==>
     ( ~((&p) divides (int_of_real (poly (SOD (g n p )) (&0)))))]])
   (STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN (CHOOSE_TAC a2) THEN
      (SPLIT_CONJOINED_ASSUMPT_TAC t1) THEN (ASM_SIMP_TAC [a5]))
  : ExceptT String IO thm).run
#eval replay PLANET_MATH_alpha_2

def INT_OF_REAL_NEG_INT_OF_NUM : thm := keep "INT_OF_REAL_NEG_INT_OF_NUM" fun _ => (do
  prove ([[!n. int_of_real(-- (real_of_num n)) = -- int_of_num n]])
   (SIMP_TAC [int_of_num, INT_OF_REAL_NEG_NUM])
  : ExceptT String IO thm).run
#eval replay INT_OF_REAL_NEG_INT_OF_NUM

def PLANET_MATH_alpha_3 : thm := keep "PLANET_MATH_alpha_3" fun _ => (do
  let lem0 ← prove ([[!(x:num) (y:real).
               (x > 0) ==>
               (integer y) ==>
               (~(&x divides (int_of_real y))) ==>
               ~(y = &0)]])
     (MESON_TAC [is_int, INT_OF_NUM_GT, INT_DIVIDES_RNEG, REAL_OF_NUM_EQ, int_of_num, INT_OF_REAL_NEG_INT_OF_NUM, INT_OF_NUM_EQ, INT_DIVIDES_0])
  let lem1 ← ar (← ExceptT.mk [[n > 0 ==> p > n ==> p > 0]])
  prove ([[n > 0 ==> p > n ==> prime p ==>
      (~((poly (SOD (g n p)) (&0)) = &0))]])
   (MESON_TAC [lem0, lem1, PLANET_MATH_alpha_1, PLANET_MATH_alpha_2])
  : ExceptT String IO thm).run
#eval replay PLANET_MATH_alpha_3

def PLANET_MATH_alpha : thm := keep "PLANET_MATH_alpha" fun _ => (do
  prove ([[n > 0 ==> p > n ==> prime p ==>
     (     (integer (poly (SOD (g n p )) (&0)))
       /\ ~((&p) divides (int_of_real (poly (SOD (g n p )) (&0))))
       /\ ~((poly (SOD (g n p)) (&0)) = &0))]])
   (SIMP_TAC [PLANET_MATH_alpha_1, PLANET_MATH_alpha_2, PLANET_MATH_alpha_3])
  : ExceptT String IO thm).run
#eval replay PLANET_MATH_alpha

def REAL_FACT_NZ : thm := keep "REAL_FACT_NZ" fun _ => (do
  let l0 ← HolLight.GSYM (← HolLight.SPECL [([[FACT n]]), ([[0]])] REAL_OF_NUM_EQ)
  prove ([[~((&(FACT n)) = (real_of_num 0))]])
   (ACCEPT_TAC (← HolLight.SPEC_ALL (← HolLight.ONCE_REWRITE_RULE [l0] FACT_NZ)))
  : ExceptT String IO thm).run
#eval replay REAL_FACT_NZ

def IS_INT_FACT_DIV_FACT_DIV_FACT : thm := keep "IS_INT_FACT_DIV_FACT_DIV_FACT" fun _ => (do
  let l0 ← HolLight.MATCH_MP (← ar (← ExceptT.mk [[(~(x=0)) ==> 0 < x]])) (← HolLight.SPEC ([[k:num]]) FACT_NZ)
  let l1 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM REAL_OF_NUM_LT)] l0
  let l2 ← HolLight.MATCH_MP REAL_EQ_LDIV_EQ l1
  prove ([[! i k.integer ((&(FACT (i+k)))/(&(FACT i))/(&(FACT k)))]])
   ((REPEAT STRIP_TAC) THEN (REWRITE_TAC [is_int, l2]) THEN
      (EXISTS_TAC ([[ (binom(i+k,k))]])) THEN DISJ1_TAC THEN
      (MESON_TAC [BINOM_FACT, MULT_SYM, MULT_ASSOC, REAL_OF_NUM_MUL, REAL_OF_NUM_EQ]))
  : ExceptT String IO thm).run
#eval replay IS_INT_FACT_DIV_FACT_DIV_FACT

def POLY_CMUL_EL : thm := keep "POLY_CMUL_EL" fun _ => (do
  let l0 ← ar (← ExceptT.mk [[(SUC i) < (SUC j) <=> i < j]])
  let h1 ← ar (← ExceptT.mk [[~(n < (0:num))]])
  prove ([[!p c i.(i < (LENGTH p)) ==> (EL i (c ## p)) = c * (EL i p)]])
   (LIST_INDUCT_TAC THENL
      [(SIMP_TAC [Session.listDefs.LENGTH, h1]),
        STRIP_TAC THEN INDUCT_TAC THENL
        [(SIMP_TAC [poly_cmul, Session.listDefs.HD, Session.listDefs.EL]),
          (ASM_SIMP_TAC [Session.listDefs.LENGTH, poly_cmul, Session.listDefs.TL, Session.listDefs.EL, l0])]])
  : ExceptT String IO thm).run
#eval replay POLY_CMUL_EL

def PDI_COEFF_FACT : thm := keep "PDI_COEFF_FACT" fun _ => (do
  let t0 := ([[!q i.  i < LENGTH (poly_diff_iter q k)
                  ==> EL i (poly_diff_iter q k) = &(FACT (i + k)) / &(FACT i) * EL (i + k) q]])
  let l0 ← HolLight.SPECL [([[q:(real)list]]), ([[SUC i]])] (← HolLight.ASSUME t0)
  let l1 ← HolLight.ONCE_REWRITE_RULE [(← ar (← ExceptT.mk [[(SUC i) < x <=> i < (PRE x)]]))] l0
  let l2 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM LENGTH_POLY_DIFF)] l1
  let l3 ← HolLight.ONCE_REWRITE_RULE [FACT, (← HolLight.GSYM REAL_OF_NUM_MUL)] l2
  let l4 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM REAL_OF_NUM_MUL)] l3
  let l5 ← HolLight.REWRITE_RULE [real_div, REAL_INV_MUL] l4
  let l6 ← rr (← ExceptT.mk [[(w * (inv x) * y ) * z = (w * y * z) * (inv x)]])
  let l9 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM REAL_OF_NUM_LT)] (← ar (← ExceptT.mk [[0 < SUC i]]))
  let l10 ← HolLight.MATCH_MP REAL_EQ_RDIV_EQ l9
  let l11 ← HolLight.ONCE_REWRITE_RULE [l6] l5
  let l12 ← HolLight.ONCE_REWRITE_RULE [real_div] l10
  let l13 ← HolLight.ONCE_REWRITE_RULE [l12] l11
  let h3 ← ar (← ExceptT.mk [[i + (SUC k) = (SUC i) + k]])
  let h2 ← rr (← ExceptT.mk [[(real_of_num 1) * x = x]])
  let h1 ← ar (← ExceptT.mk [[i + 0 = i]])
  prove ([[! k q i.(i < LENGTH (poly_diff_iter q k)) ==>
            (EL i (poly_diff_iter q k)) = ((&(FACT (i+k)))/(&(FACT i))) * (EL (i+k) q)]])
   (INDUCT_TAC THENL
      [(REWRITE_TAC [Pm_lemma1.PDI_DEF, h1]) THEN
        (MESON_TAC [REAL_DIV_REFL, FACT_NZ, REAL_OF_NUM_EQ, h2]),
        (ONCE_REWRITE_TAC [Pm_lemma1.PDI_DEF]) THEN (SIMP_TAC [EL_POLY_DIFF]) THEN
        (ONCE_REWRITE_TAC [h3]) THEN
        (ONCE_REWRITE_TAC [FACT]) THEN (ONCE_REWRITE_TAC [real_div]) THEN
        (SIMP_TAC [l13, real_div, REAL_MUL_ASSOC])])
  : ExceptT String IO thm).run
#eval replay PDI_COEFF_FACT

def POLY_DIVIDES_POLY_DIFF : thm := keep "POLY_DIVIDES_POLY_DIFF" fun _ => (do
  let l0 ← ar (← ExceptT.mk [[op = SUC odp ==> SUC n <= op ==> n <= odp]])
  let l1 ← ar (← ExceptT.mk [[(SUC n <= m ) ==> ~(m = 0)]])
  prove ([[!p n a.
         (poly_divides (poly_exp [--a;&1] (SUC n)) p)
         ==> (poly_divides (poly_exp [--a;&1] n) (poly_diff p))]])
   (MESON_TAC [l0, l1, POLY_DIFF_ZERO, ORDER_DIVIDES, ORDER_DIFF])
  : ExceptT String IO thm).run
#eval replay POLY_DIVIDES_POLY_DIFF

def POLY_DIVIDES_MUL : thm := keep "POLY_DIVIDES_MUL" fun _ => (do
  prove ([[!p1 p2 p3.poly_divides p1 p2 ==> poly_divides p1 (p2 ** p3)]])
   ((ONCE_REWRITE_TAC [SessionLibrary.Poly.divides]) THEN (REPEAT STRIP_TAC) THEN
      (EXISTS_TAC ([[q ** p3]])) THEN
      (ASM_MESON_TAC [FUN_EQ_THM, POLY_MUL, POLY_MUL_ASSOC]))
  : ExceptT String IO thm).run
#eval replay POLY_DIVIDES_MUL

def POLY_DIVIDES_MUL3 : thm := keep "POLY_DIVIDES_MUL3" fun _ => (do
  prove ([[!p1 p2 p3.(poly_divides p1 p2) ==> (poly_divides p1 (p3 ** p2))]])
   ((ONCE_REWRITE_TAC [SessionLibrary.Poly.divides]) THEN (REPEAT STRIP_TAC) THEN
      (EXISTS_TAC ([[p3 ** q]])) THEN (UNDISCH_TAC ([[poly (p2) = poly (p1 ** q)]])) THEN
      (ONCE_REWRITE_TAC [FUN_EQ_THM]) THEN (REWRITE_TAC [POLY_MUL]) THEN
      (MESON_TAC [REAL_MUL_ASSOC, REAL_MUL_SYM]))
  : ExceptT String IO thm).run
#eval replay POLY_DIVIDES_MUL3

def POLY_DIVIDES_POLY_MUL_ITER : thm := keep "POLY_DIVIDES_POLY_MUL_ITER" fun _ => (do
  let l1 ← ar (← ExceptT.mk [[~(v <= n) ==> (v <= SUC n) ==> v = SUC n]])
  let l2 ← HolLight.UNDISCH (← HolLight.UNDISCH l1)
  prove ([[!f n v. 1 <= v ==> v <= n ==> poly_divides (f v) (poly_mul_iter f n)]])
   (STRIP_TAC THEN INDUCT_TAC THENL
      [ARITH_TAC,
        (ONCE_REWRITE_TAC [Pm_eqn5.POLY_MUL_ITER]) THEN STRIP_TAC THEN
        (ASM_CASES_TAC ([[v <= (n:num)]])) THENL
        [ASM_MESON_TAC [POLY_DIVIDES_MUL3],
          STRIP_TAC THEN STRIP_TAC THEN
          (MESON_TAC [l2, POLY_DIVIDES_MUL, POLY_DIVIDES_REFL])]])
  : ExceptT String IO thm).run
#eval replay POLY_DIVIDES_POLY_MUL_ITER

def POLY_DIVIDES_POLY_EXP2 : thm := keep "POLY_DIVIDES_POLY_EXP2" fun _ => (do
  let t0 := ([[!p1 p2.
                (?q. poly p2 = poly (p1 ** q))
                ==> (?q. poly (poly_exp p2 n) = poly (poly_exp p1 n ** q))]])
  let l0 ← HolLight.ASSUME t0
  let l1 ← HolLight.UNDISCH (← HolLight.REWRITE_RULE [SessionLibrary.Poly.divides] (← HolLight.SPEC_ALL l0))
  let l3 ← prove ([[(x2 = x5 * x6 /\ x1 = x4 * x7) ==> (x1:real) * x2 = (x4 * x5) * x6 * x7]])
     (MESON_TAC [REAL_MUL_SYM, REAL_MUL_ASSOC])
  prove ([[!n p1 p2.(poly_divides p1 p2) ==> poly_divides (poly_exp p1 n) (poly_exp p2 n)]])
   ((ONCE_REWRITE_TAC [SessionLibrary.Poly.divides]) THEN INDUCT_TAC THENL
     [(MESON_TAC [SessionLibrary.Poly.divides, poly_exp, POLY_DIVIDES_REFL]),
       (STRIP_TAC THEN STRIP_TAC THEN DISCH_TAC) THEN (CHOOSE_TAC l1) THEN
       (UNDISCH_TAC ([[?q. poly p2 = poly (p1 ** q)]])) THEN STRIP_TAC THEN
       (ONCE_REWRITE_TAC [poly_exp]) THEN (EXISTS_TAC ([[q ** q']])) THEN
       (REWRITE_TAC [poly_exp, FUN_EQ_THM, POLY_MUL]) THEN
       (ASM_MESON_TAC [l3, FUN_EQ_THM, POLY_MUL])])
  : ExceptT String IO thm).run
#eval replay POLY_DIVIDES_POLY_EXP2

def POLY_EXP_ONE : thm := keep "POLY_EXP_ONE" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[1 = SUC 0]])
  prove ([[!p .p = poly_exp p 1]])
   (MESON_TAC [poly_exp, h1, POLY_MUL_RID])
  : ExceptT String IO thm).run
#eval replay POLY_EXP_ONE

def POLY_DIVIDES_ROOT : thm := keep "POLY_DIVIDES_ROOT" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[1 <= ord ==> ~(ord = 0)]])
  prove ([[!p a.poly_divides [--a;&1] p ==> (poly p a) = &0]])
   (MESON_TAC [ORDER_ROOT, ORDER_DIVIDES, POLY_EXP_ONE,
                 h1])
  : ExceptT String IO thm).run
#eval replay POLY_DIVIDES_ROOT

def POLY_DIVIDES_PDI : thm := keep "POLY_DIVIDES_PDI" fun _ => (do
  let t0 := ([[!p a.  poly_divides (poly_exp [--a; &1] (SUC n)) p
                     ==> poly_divides [--a; &1] (poly_diff_iter p n)]])
  let l0 ← HolLight.ASSUME t0
  let l1 ← HolLight.SPEC ([[poly_diff p]]) l0
  let l2 ← HolLight.SPECL [([[p:(real)list]]), ([[SUC n]]), ([[a:real]])] POLY_DIVIDES_POLY_DIFF
  let l3 ← HolLight.UNDISCH l2
  let l4 ← HolLight.MATCH_MP l1 l3
  prove ([[!n p a.
         (poly_divides (poly_exp [--a;&1] (SUC n)) p)
         ==> (poly_divides [--a;&1] (poly_diff_iter p n))]])
   (INDUCT_TAC THENL
      [(SIMP_TAC [poly_exp, POLY_MUL_RID, Pm_lemma1.PDI_DEF]),
        (REPEAT STRIP_TAC) THEN (ASM_MESON_TAC [l4, Pm_lemma1.PDI_DEF, PDI_POLY_DIFF_COMM_2])])
  : ExceptT String IO thm).run
#eval replay POLY_DIVIDES_PDI

def POLY_DIVIDES_PDI2 : thm := keep "POLY_DIVIDES_PDI2" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[m > n <=> (SUC n) <= m]])
  prove ([[!n m p a.
          m > n
          ==> (poly_divides (poly_exp [--a;&1] m) p)
          ==> (poly_divides [--a;&1] (poly_diff_iter p n))]])
   (MESON_TAC [POLY_EXP_DIVIDES, POLY_DIVIDES_PDI,
                  h1])
  : ExceptT String IO thm).run
#eval replay POLY_DIVIDES_PDI2

def TAIL_GUNNER : thm := keep "TAIL_GUNNER" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[x < p <=> (p:num) > x]])
  prove ([[ x < p ==> 1 <= v ==> v <= n ==>
      poly (poly_diff_iter
           (poly_exp [&0; &1] (p - 1) **
            poly_exp (poly_mul_iter (\i. [-- &i; &1]) n) p)
          x)
          (&v)
       = &0 ]])
   (MESON_TAC [POLY_DIVIDES_ROOT, h1,
                  POLY_DIVIDES_PDI2, POLY_DIVIDES_MUL3, POLY_DIVIDES_POLY_EXP2,
                  POLY_DIVIDES_POLY_MUL_ITER])
  : ExceptT String IO thm).run
#eval replay TAIL_GUNNER

def IS_INT_POLY : thm := keep "IS_INT_POLY" fun _ => (do
  prove ([[!p x.(integer x) ==> (ALL integer p) ==> integer (poly p x)]])
   (LIST_INDUCT_TAC THEN
      (ASM_MESON_TAC [N_IS_INT_2, Session.listDefs.ALL, poly, INTEGER_ADD, INTEGER_MUL]))
  : ExceptT String IO thm).run
#eval replay IS_INT_POLY

def INV_POLY_CMUL : thm := keep "INV_POLY_CMUL" fun _ => (do
  prove ([[!y x . (~(x = &0)) ==> (x) ## (inv x) ## y = y]])
   (LIST_INDUCT_TAC THENL
      [ASM_MESON_TAC [poly_cmul],
        (REPEAT STRIP_TAC) THEN
        (REWRITE_TAC [poly_cmul, REAL_MUL_ASSOC]) THEN
        (ASM_MESON_TAC [SessionLibrary.Analysis.REAL_MUL_RINV, REAL_MUL_LID])])
  : ExceptT String IO thm).run
#eval replay INV_POLY_CMUL

def INV_POLY_CMUL2 : thm := keep "INV_POLY_CMUL2" fun _ => (do
  prove ([[!y x . (~(x = &0)) ==> (inv x) ## (x) ## y = y]])
   (MESON_TAC [INV_POLY_CMUL, REAL_INV_INV, REAL_INV_EQ_0])
  : ExceptT String IO thm).run
#eval replay INV_POLY_CMUL2

def POLY_CMUL_EQUALS : thm := keep "POLY_CMUL_EQUALS" fun _ => (do
  prove ([[!z x y. (~(z = &0)) ==> ((x = y) <=> (z ## x = z ## y))]])
   ((REPEAT STRIP_TAC) THEN EQ_TAC THENL
      [(SIMP_TAC []),
        (SPEC_TAC (([[x:(real)list]]), ([[x:(real)list]]))) THEN
        (SPEC_TAC (([[y:(real)list]]), ([[y:(real)list]]))) THEN
        LIST_INDUCT_TAC THENL
        [LIST_INDUCT_TAC THENL
          [(SIMP_TAC [POLY_CMUL_CLAUSES]),
            (ASM_MESON_TAC [POLY_CMUL_CLAUSES, Session.listThms1.NOT_CONS_NIL])],
          LIST_INDUCT_TAC THENL [(ASM_MESON_TAC [POLY_CMUL_CLAUSES, Session.listThms1.NOT_CONS_NIL]),
            (ONCE_REWRITE_TAC [poly_cmul]) THEN
            (ASM_MESON_TAC [REAL_EQ_LCANCEL_IMP, Session.listThms1.CONS_11])]]])
  : ExceptT String IO thm).run
#eval replay POLY_CMUL_EQUALS

def PDI_LENGTH_THM : thm := keep "PDI_LENGTH_THM" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[(x:num) - 0 = x]])
  prove ([[!f n. LENGTH(poly_diff_iter f n) = (LENGTH f) - n]])
   (STRIP_TAC THEN INDUCT_TAC THENL
      [(SIMP_TAC [Pm_lemma1.PDI_DEF, h1]),
        (ONCE_REWRITE_TAC [Pm_lemma1.PDI_DEF]) THEN
        (ONCE_REWRITE_TAC [LENGTH_POLY_DIFF]) THEN ASM_ARITH_TAC])
  : ExceptT String IO thm).run
#eval replay PDI_LENGTH_THM

def CAPTAINS_CLOTHES : thm := keep "CAPTAINS_CLOTHES" fun _ => (do
  let e0 := ([[(inv (&(FACT k))) ## (poly_diff_iter q k)]])
  let l1 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM (← HolLight.SPEC ([[inv (&(FACT k))]]) POLY_CMUL_LENGTH))] PDI_COEFF_FACT
  let l2 ← HolLight.UNDISCH (← HolLight.SPEC_ALL l1)
  let l3 ← prove ([[i < LENGTH( inv (&(FACT k)) ## poly_diff_iter q k)
                     ==> (i + k) < LENGTH q]])
     (MESON_TAC [PDI_LENGTH_THM, POLY_CMUL_LENGTH,
                                 (← ar (← ExceptT.mk [[(i:num) < f -k ==> (i+k) < f]]))])
  prove ([[! k q.
     (ALL integer q) ==>
     ? r .(ALL integer r) /\ r = (inv (&(FACT k))) ## (poly_diff_iter q k)]])
   ((REPEAT STRIP_TAC) THEN (EXISTS_TAC e0) THEN (SIMP_TAC []) THEN
      (ASM_SIMP_TAC [(← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM POLY_CMUL_LENGTH)] POLY_CMUL_EL)]) THEN
      (ONCE_REWRITE_TAC [(← HolLight.GSYM Session.listThms2.ALL_EL)]) THEN (REPEAT STRIP_TAC) THEN
      (ASM_SIMP_TAC [(← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM POLY_CMUL_LENGTH)] POLY_CMUL_EL)]) THEN
      (ONCE_REWRITE_TAC [l2]) THEN (ONCE_REWRITE_TAC [REAL_MUL_ASSOC]) THEN
      (MATCH_MP_TAC INTEGER_MUL) THEN STRIP_TAC THENL
      [(MESON_TAC [IS_INT_FACT_DIV_FACT_DIV_FACT, REAL_MUL_SYM, real_div, REAL_MUL_ASSOC]),
        (ASM_MESON_TAC [l3, ALL_IMP_EL])])
  : ExceptT String IO thm).run
#eval replay CAPTAINS_CLOTHES

def MESSY_JESSE2 : thm := keep "MESSY_JESSE2" fun _ => (do
  let root_canal ← rr (← ExceptT.mk [[(x:real) * (&0) = &0]])
  let bs := ([[\(v:num) . \(x:num).
               if (x <= (LENGTH (g n p)) ) then
                    (poly
                       ((inv (&(FACT x))) ##
                        (poly_diff_iter
                        (poly_exp [&0; &1] (p - 1) **
                         poly_exp (poly_mul_iter (\i. [-- &i; &1]) n) p)
                        x))
                       (&v))
               else (&0)]])
  let l0 ← prove ([[ALL integer [&0;&1] ]])
     (MESON_TAC [Session.listDefs.ALL, N_IS_INT_2])
  let t0 := ([[(poly_exp [&0; &1] (p - 1) **
              poly_exp (poly_mul_iter (\i. [-- &i; &1]) n) p)]])
  let l2 ← HolLight.SPECL [([[i:num]]), t0] CAPTAINS_CLOTHES
  let l3 ← prove ([[ALL integer (poly_exp [&0; &1] (p - 1) ** poly_exp (poly_mul_iter (\i. [-- &i; &1]) n) p)]])
     (MESON_TAC [l0, ALL_IS_INT_POLY_MUL, ALL_IS_INT_POLY_EXP, ALL_IS_INT_POLY_MUL_ITER])
  let l4 ← HolLight.MP l2 l3
  let l7 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM REAL_OF_NUM_EQ)] FACT_NZ
  let l8 ← ExceptT.mk (Session.SIMP_RULE [l7] (← HolLight.SPEC ([[(&(FACT i)):real]]) POLY_CMUL_EQUALS))
  let l10_0 ← HolLight.SPECL [([[y:(real)list]]), ([[(real_of_num (FACT i))]])] INV_POLY_CMUL
  let l12_0 ← HolLight.SPECL [([[y:(real)list]]), ([[(real_of_num (FACT i))]])] INV_POLY_CMUL2
  let l10 ← ExceptT.mk (Session.SIMP_RULE [REAL_FACT_NZ] l10_0)
  let l12 ← ExceptT.mk (Session.SIMP_RULE [REAL_FACT_NZ] l12_0)
  let l9 ← HolLight.ONCE_REWRITE_RULE [l8] l4
  let l11 ← HolLight.GSYM (← HolLight.ONCE_REWRITE_RULE [l10] l9)
  let l133 ← prove ([[
      (psum (0,m) (\i.(x i) * (if i <= m then (y i) else c))) =
      (psum (0,m) (\i.(x i) * (y i)))]])
     (MESON_TAC [SessionLibrary.Analysis.SUM_EQ, (← ar (← ExceptT.mk [[(0 <= i /\ i < (m:num) + 0) ==> i <= m]]))])
  let l18 ← HolLight.MATCH_MP SessionLibrary.Analysis.REAL_MUL_RINV (← HolLight.SPEC ([[i:num]]) l7)
  let lass2 ← HolLight.SPECL [([[g n p]]), ([[x:real]]), ([[v:real]])] Pm_lemma2.PLANETMATH_LEMMA_2_B
  let lass3 ← HolLight.BETA_RULE lass2
  let lass4 ← HolLight.CONV_RULE (HolLight.RAND_CONV (HolLight.RAND_CONV (HolLight.REWRITE_CONV [Pm_eqn5.PLANETMATH_EQN_5]))) lass3
  let lass5 ← HolLight.REWRITE_RULE [POLY_CMUL, POLY_CMUL_PDI] lass4
  let lass6 ← HolLight.CONV_RULE (HolLight.RAND_CONV (HolLight.ONCE_REWRITE_CONV [(← HolLight.GSYM (← HolLight.ISPEC ([[f:num->real]]) ETA_AX))])) (← HolLight.SPEC_ALL SUM_CMUL)
  let lass7 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM REAL_MUL_ASSOC)] lass5
  let lass8 ← HolLight.REWRITE_RULE [lass6] lass7
  let lass10 ← HolLight.ONCE_REWRITE_RULE [REAL_MUL_DIV_ASSOC] lass8
  let lass11 ← HolLight.ONCE_REWRITE_RULE [real_div] lass10
  let lass12 ← rr (← ExceptT.mk [[((w:real) * x * y) * z = w * x * y * z]])
  let lass13 ← HolLight.ONCE_REWRITE_RULE [lass12] lass11
  let lass14 ← HolLight.REWRITE_RULE [lass6] lass13
  let MUL_ONE ← rr (← ExceptT.mk [[! x.(&1) * x = x /\ x * (&1) = x]])
  let lass15 ← ExceptT.mk (Session.SIMP_RULE [REAL_MUL_LINV, REAL_FACT_NZ, MUL_ONE] lass14)
  let h2 ← ar (← ExceptT.mk [[~(i < (p:num)) ==> (p <= i)]])
  let h1 ← rr (← ExceptT.mk [[(x:real) * (&0) = &0]])
  prove ([[n > 0 ==> p > n ==>
     (? (Bs:num->num->real). ! v .
         (1 <= v) ==> (v <= n) ==>
         (    (! i . (integer (Bs v i)))
           /\ (poly (SOD (g n p)) (&v)) =
                 ((real_of_num 1) / (&(FACT (p - 1)))) *
                   (psum (0,LENGTH (g n p))
                      (\i. (&(FACT i)) * (Bs v i)))
           /\ (! i. (i < p) ==> (Bs v i) = &0)  ))]])
   (STRIP_TAC THEN STRIP_TAC THEN (EXISTS_TAC bs) THEN (REPEAT STRIP_TAC) THENL
      [(BETA_TAC THEN BETA_TAC) THEN (ASM_CASES_TAC ([[(i <= LENGTH (g n p))]])) THENL
        [(ASM_SIMP_TAC []) THEN (ASM_CASES_TAC ([[((i:num) < p)]])) THENL
          [(ASM_MESON_TAC [POLY_CMUL, TAIL_GUNNER,
                            N_IS_INT_2, h1]),
            (ASSUME_TAC (← HolLight.UNDISCH h2)) THEN
            (CHOOSE_TAC l11) THEN
            (SPLIT_CONJOINED_ASSUMPT_TAC (Prod.snd (← ec (HolCore.Basics.dest_exists (concl l11))))) THEN
            (ASM_REWRITE_TAC [l12]) THEN
            (ASM_MESON_TAC [N_IS_INT_2, IS_INT_POLY])],
          (ASM_MESON_TAC [N_IS_INT_2])],
        BETA_TAC THEN (SIMP_TAC [l133]) THEN
        (SIMP_TAC [POLY_CMUL, l18, REAL_MUL_ASSOC, REAL_MUL_LID]) THEN
        (SIMP_TAC [lass15, REAL_INV_1OVER]),
        BETA_TAC THEN (ASM_MESON_TAC [TAIL_GUNNER, POLY_CMUL, root_canal])])
  : ExceptT String IO thm).run
#eval replay MESSY_JESSE2

def INTEGER_PSUM : thm := keep "INTEGER_PSUM" fun _ => (do
  let l0 ← HolLight.ASSUME ([[!i. i < SUC m ==> integer (f i)]])
  let l1 ← HolLight.SPEC ([[m:num]]) l0
  let l2 ← ExceptT.mk (Session.SIMP_RULE [(← ar (← ExceptT.mk [[m < SUC m]]))] l1)
  let h2 ← ar (← ExceptT.mk [[(i:num) < m ==> i < SUC m]])
  let h1 ← ar (← ExceptT.mk [[0 + (x:num) = x]])
  prove ([[!f m.(! i . i < m ==> integer (f i)) ==> (integer (psum (0,m) f))]])
   (STRIP_TAC THEN INDUCT_TAC THENL
      [(MESON_TAC [SessionLibrary.Analysis.sum, int_of_num, int_of_num_th, N_IS_INT_2]),
        (SIMP_TAC [SessionLibrary.Analysis.sum, h1]) THEN
        STRIP_TAC THEN (MATCH_MP_TAC INTEGER_ADD) THEN
        (ASM_MESON_TAC [l2, h2])])
  : ExceptT String IO thm).run
#eval replay INTEGER_PSUM

def INT_DIVIDES_PSUM : thm := keep "INT_DIVIDES_PSUM" fun _ => (do
  let l0 ← HolLight.ASSUME ([[!i. i < SUC m ==> integer (f i) /\ p divides int_of_real (f i)]])
  let l1 ← HolLight.SPEC ([[m:num]]) l0
  let l2 ← ExceptT.mk (Session.SIMP_RULE [(← ar (← ExceptT.mk [[m < SUC m]]))] l1)
  let l3 ← HolLight.ASSUME ([[(!i. i < m ==> integer (f i)) ==> integer (psum (0,m) f)]])
  let l4 ← HolLight.SPEC ([[i:num]]) l0
  let l5 ← HolLight.DISCH ([[i < SUC m]]) (← HolLight.CONJUNCT1 (← HolLight.UNDISCH l4))
  let l8 ← prove ([[(!i.i < SUC m
                         ==> (integer (f i))) ==> (!i.i < m ==> (integer (f i)))]])
     (MESON_TAC [(← ar (← ExceptT.mk [[i < m ==> i < SUC m]]))])
  let ll1 ← HolLight.MP l8 (← HolLight.GEN_ALL l5)
  let ll2 ← HolLight.MP l3 ll1
  let ll3 ← HolLight.MATCH_MP INT_OF_REAL_ADD (← HolLight.CONJ ll2 (← HolLight.CONJUNCT1 l2))
  let h3 ← ar (← ExceptT.mk [[m < SUC m]])
  let h2 ← ar (← ExceptT.mk [[i < m ==> i < SUC m]])
  let h1 ← ar (← ExceptT.mk [[0 + (x:num) = x]])
  prove ([[!f m p.(! i . i < m ==>
             ((integer (f i)) /\ (int_divides p (int_of_real (f i)))))
                ==> (int_divides p (int_of_real (psum (0,m) f)))]])
   (STRIP_TAC THEN INDUCT_TAC THENL
      [(MESON_TAC [SessionLibrary.Analysis.sum, int_of_num, int_of_num_th, INT_DIVIDES_0]),
        (SIMP_TAC [SessionLibrary.Analysis.sum, h1]) THEN
        (ASSUME_TAC (← HolLight.SPECL [([[f:num->real]]), ([[m:num]])] INTEGER_PSUM)) THEN
        STRIP_TAC THEN
        STRIP_TAC THEN
        (ONCE_REWRITE_TAC [ll3]) THEN
        (MATCH_MP_TAC INT_DIVIDES_ADD) THEN
        CONJ_TAC THENL
        [(ASM_MESON_TAC [h2]),
          (ASM_MESON_TAC [h3])]])
  : ExceptT String IO thm).run
#eval replay INT_DIVIDES_PSUM

def PLANET_MATH_beta : thm := keep "PLANET_MATH_beta" fun _ => (do
  let l2 ← HolLight.GSYM (← HolLight.ONCE_REWRITE_RULE [REAL_MUL_SYM] real_div)
  let ll3 ← ar (← ExceptT.mk [[(int_of_num p) * &0 = &0]])
  let l7 ← HolLight.UNDISCH (← HolLight.SPECL [([[i:num]]), ([[p:num]])] IS_INT_FACT_DIV)
  let l11 ← prove ([[p > 0 ==> FACT p = p * (FACT (p-1))]])
     (MESON_TAC [FACT, (← ar (← ExceptT.mk [[p > 0 ==> SUC (p -1) = p ]]))])
  let l12 ← HolLight.UNDISCH (← HolLight.UNDISCH (← ar (← ExceptT.mk [[(p:num) > n ==> n > 0 ==> p > 0]])))
  let l13 ← HolLight.MP l11 l12
  let t9 := ([[1 <= (v:num) ==>
       v <= (n:num) ==>
       (!v. 1 <= v
              ==> v <= n
              ==> (!i. integer (Bs v i)) /\
                  poly (SOD (g n p)) (&v) =
                  &1 / &(FACT (p - 1)) *
                  psum (0,LENGTH (g n p)) (\i. &(FACT i) * Bs v i) /\
                  (!i. i < p ==> Bs v i = &0)) ==>
        (integer (Bs v i))]])
  let lll0 ← HolLight.UNDISCH (← HolLight.UNDISCH (← HolLight.UNDISCH (← prove (t9)
     (MESON_TAC []))))
  let l8 ← HolLight.REWRITE_RULE [l13, real_div, REAL_INV_MUL] l7
  let l9 ← HolLight.REWRITE_RULE [N_IS_INT_2, (← HolLight.GSYM REAL_OF_NUM_MUL)] l8
  let l10 ← HolLight.REWRITE_RULE [REAL_INV_MUL] l9
  let l11 ← HolLight.MATCH_MP INTEGER_MUL (← HolLight.CONJ l10 lll0)
  let l12 ← HolLight.MATCH_MP INT_OF_REAL_MUL (← HolLight.CONJ (← HolLight.SPEC ([[p:num]]) N_IS_INT_2) l11)
  let l15 ← HolLight.GSYM l12
  let lll8 ← ar (← ExceptT.mk [[p > n ==> n > 0 ==> ~(p = 0)]])
  let lll9 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM REAL_OF_NUM_EQ)] lll8
  let lll10 ← HolLight.UNDISCH (← HolLight.UNDISCH lll9)
  let sc1 ← prove ([[(~((x:real) = &0)) ==> (x * y * inv x) = y]])
     (MESON_TAC [SessionLibrary.Analysis.REAL_MUL_RID, REAL_MUL_ASSOC,
                                   REAL_MUL_SYM, REAL_MUL_LINV, REAL_MUL_LID])
  let sc2 ← prove ([[(~((x:real) = &0)) ==> (x * y * (inv x) * z) = y * z]])
     (MESON_TAC [sc1, REAL_MUL_ASSOC])
  let h6 ← ar (← ExceptT.mk [[(~((i:num) < p)) ==> i >= p]])
  let h5 ← rr (← ExceptT.mk [[(x:real) * (&0) = &0]])
  let h4 ← ar (← ExceptT.mk [[(~((i:num) < p)) ==> i >= p-1]])
  let h3 ← rr (← ExceptT.mk [[(x:real) * (&0) = &0]])
  let h2 ← ar (← ExceptT.mk [[(~((i:num) < p)) ==> i >= p-1]])
  let h1 ← rr (← ExceptT.mk [[(x:real) * (&0) = &0]])
  prove ([[p > n ==>
     n > 0 ==>
     (! v.
       (1 <= v /\ v <= n) ==>
       (   (integer (poly (SOD (g n p )) (&v)))
        /\ ((&p) divides (int_of_real (poly (SOD (g n p )) (&v))))
       )
     )]])
   ((REPEAT STRIP_TAC) THENL
        [(CHOOSE_TAC (← HolLight.UNDISCH (← HolLight.UNDISCH MESSY_JESSE2))) THEN
          (ASM_SIMP_TAC []) THEN
          (ONCE_REWRITE_TAC [(← HolLight.GSYM SUM_CMUL)]) THEN
          (MATCH_MP_TAC INTEGER_PSUM) THEN
          (REPEAT STRIP_TAC) THEN
          BETA_TAC THEN
          (ASM_CASES_TAC ([[i < (p:num)]])) THENL
          [(ASM_SIMP_TAC [N_IS_INT_2, h1]),
            (ASSUME_TAC (← HolLight.UNDISCH h2)) THEN
            (ASM_MESON_TAC [REAL_INV_1OVER, REAL_MUL_ASSOC,
                            IS_INT_FACT_DIV, l2, INTEGER_MUL])],
          (CHOOSE_TAC (← HolLight.UNDISCH (← HolLight.UNDISCH MESSY_JESSE2))) THEN
          (ASM_SIMP_TAC []) THEN
          (ONCE_REWRITE_TAC [(← HolLight.GSYM SUM_CMUL)]) THEN
          (MATCH_MP_TAC INT_DIVIDES_PSUM) THEN
          (REPEAT STRIP_TAC) THENL
          [BETA_TAC THEN
            (ASM_CASES_TAC ([[i < (p:num)]])) THENL
            [(ASM_SIMP_TAC [N_IS_INT_2, h3]),
              (ASSUME_TAC (← HolLight.UNDISCH h4)) THEN
              (ASM_MESON_TAC [REAL_INV_1OVER, REAL_MUL_ASSOC,
                              IS_INT_FACT_DIV, l2, INTEGER_MUL])],
            (ONCE_REWRITE_TAC [int_divides]) THEN BETA_TAC THEN
            (ASM_CASES_TAC ([[i < (p:num)]])) THENL
            [(ASM_SIMP_TAC [N_IS_INT_2, h5]) THEN
              (EXISTS_TAC ([[int_of_num 0]])) THEN
              (MESON_TAC [ll3, int_of_num_th, int_of_num]),
              (ASSUME_TAC (← HolLight.UNDISCH h6)) THEN
              (EXISTS_TAC ([[int_of_real (((&(FACT i))/(&(FACT p))) * (Bs (v:num) i))]])) THEN
              (ONCE_REWRITE_TAC [int_of_num]) THEN
              (ONCE_REWRITE_TAC [l13]) THEN
              (ONCE_REWRITE_TAC [N_IS_INT_2, (← HolLight.GSYM REAL_OF_NUM_MUL)]) THEN
              (SIMP_TAC [real_div]) THEN
              (ONCE_REWRITE_TAC [REAL_INV_MUL]) THEN
              (ONCE_REWRITE_TAC [REAL_MUL_LID]) THEN
              (ONCE_REWRITE_TAC [l15]) THEN
              (ASSUME_TAC lll10) THEN
              (ONCE_REWRITE_TAC [REAL_MUL_ASSOC]) THEN
              (ASM_MESON_TAC [sc2, REAL_MUL_SYM])]]])
  : ExceptT String IO thm).run
#eval replay PLANET_MATH_beta

def JUNE_LEMMA : thm := keep "JUNE_LEMMA" fun _ => (do
  let lem0 ← HolLight.CONJUNCT1 (← HolLight.UNDISCH_ALL PLANET_MATH_alpha)
  let lem1 ← HolLight.UNDISCH_ALL (← HolLight.SPEC_ALL (← HolLight.UNDISCH_ALL PLANET_MATH_beta))
  let lem2 ← HolLight.DISCH ([[1 <= v /\ v <= n]]) (← HolLight.CONJUNCT1 lem1)
  let lem3 ← HolLight.SPEC ([[SUC v]]) (← HolLight.GEN ([[v:num]]) lem2)
  let lem4 ← ExceptT.mk (Session.SIMP_RULE [(← ar (← ExceptT.mk [[1 <= SUC v]]))] lem3)
  prove ([[n > 0 ==> p > n ==> v <= n ==> integer (poly (SOD (g n p)) (&v))]])
   ((STRIP_TAC THEN STRIP_TAC) THEN
      (SPEC_TAC (([[v:num]]), ([[v:num]]))) THEN
      (INDUCT_TAC THENL [(SIMP_TAC [lem0]), (ACCEPT_TAC lem4)]))
  : ExceptT String IO thm).run
#eval replay JUNE_LEMMA

def DIVIDES_SUM_NOT_ZERO : thm := keep "DIVIDES_SUM_NOT_ZERO" fun _ => (do
  let l0 ← HolLight.ASSUME ([[(x:int) + y = &0]])
  let l1 ← HolLight.ONCE_REWRITE_RULE [(← ar (← ExceptT.mk [[((x:int) + y = &0) <=> (x = --y)]]))] l0
  prove ([[!(x:int) (y:int) (z:int).
         (~(z divides x)) /\  (z divides y) ==> ~(x + y = &0)]])
   ((REPEAT STRIP_TAC) THEN (UNDISCH_TAC ([[~((z:int) divides x)]])) THEN
      (REWRITE_TAC [l1]) THEN (UNDISCH_TAC ([[((z:int) divides y)]])) THEN
      INTEGER_TAC)
  : ExceptT String IO thm).run
#eval replay DIVIDES_SUM_NOT_ZERO

def NUM_OF_INT_ABS : thm := keep "NUM_OF_INT_ABS" fun _ => (do
  let j0 ← HolLight.UNDISCH (← prove ([[(num_of_int (abs y) = x) ==> x = num_of_int (abs y)]])
     (MESON_TAC []))
  let j1 ← ar (← ExceptT.mk [[&0 <= ((abs y):int)]])
  let j2 ← HolLight.MATCH_MP INT_OF_NUM_OF_INT j1
  prove ([[!(x:num) (y:int).num_of_int (abs y)  = x <=> abs y = &x]])
   ((REPEAT STRIP_TAC) THEN EQ_TAC THENL
      [(STRIP_TAC THEN SIMP_TAC [j0, j2]),
        (ASM_SIMP_TAC [NUM_OF_INT_OF_NUM])])
  : ExceptT String IO thm).run
#eval replay NUM_OF_INT_ABS

def INT_DIVIDES_IMP_ABS_NUM_DIVIDES : thm := keep "INT_DIVIDES_IMP_ABS_NUM_DIVIDES" fun _ => (do
  let w0 ← ar (← ExceptT.mk [[((&0):int) <= abs x]])
  let w1 := Prod.fst (← HolLight.EQ_IMP_RULE (← HolLight.SPEC ([[abs (x:int)]]) NUM_OF_INT))
  let w2 ← HolLight.MP w1 w0
  let w3 ← ar (← ExceptT.mk [[((&0):int) <= x ==> abs x = x]])
  let w4 ← ar (← ExceptT.mk [[(~(((&0):int) <= x)) ==> abs x = -- x]])
  prove ([[! (x:int) (y:num).
       (x divides (&y)) ==> ((num_of_int (abs x)) divides y)]])
   ((REWRITE_TAC [int_divides, num_divides]) THEN
      (REPEAT STRIP_TAC) THEN (ASM_REWRITE_TAC [w2]) THEN
      (ASM_CASES_TAC ([[((&0):int) <= x]])) THENL
      [(ONCE_REWRITE_TAC [(← HolLight.UNDISCH w3)]) THEN
        (EXISTS_TAC ([[x':int]])) THEN REFL_TAC,
        (ONCE_REWRITE_TAC [(← HolLight.UNDISCH w4)]) THEN
        (EXISTS_TAC ([[--x':int]])) THEN ARITH_TAC])
  : ExceptT String IO thm).run
#eval replay INT_DIVIDES_IMP_ABS_NUM_DIVIDES

def INT_PRIME_NUM_PRIME : thm := keep "INT_PRIME_NUM_PRIME" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[2 <= p ==> abs((&p):int) > &1]])
  prove ([[!p. int_prime (&p) <=> prime p]])
   ((ONCE_REWRITE_TAC [int_prime, prime]) THEN
      (MESON_TAC [SessionLibrary.Poly.divides, num_divides,
                  INT_ABS, INT_POS, INT_OF_NUM_EQ, INT_LT_IMP_NE, INT_GT,
                  h1,
                  INT_DIVIDES_IMP_ABS_NUM_DIVIDES, NUM_OF_INT_ABS, PRIME_GE_2,
                  prime, int_prime]))
  : ExceptT String IO thm).run
#eval replay INT_PRIME_NUM_PRIME

def DIVIDES_INT_OF_REAL_ADD : thm := keep "DIVIDES_INT_OF_REAL_ADD" fun _ => (do
  prove ([[!x y p.integer x /\
                 integer y /\
                 p divides (int_of_real x) /\
                 p divides (int_of_real y)
                 ==> p divides (int_of_real (x + y))]])
   (SIMP_TAC [INT_OF_REAL_ADD, INT_DIVIDES_ADD])
  : ExceptT String IO thm).run
#eval replay DIVIDES_INT_OF_REAL_ADD

def ITCHY_LEMMA : thm := keep "ITCHY_LEMMA" fun _ => (do
  let l0 := Prod.fst (← HolLight.EQ_IMP_RULE (← HolLight.SPECL [([[1]]), ([[0]])] (← HolLight.GSYM NUMSEG_EMPTY)))
  let l1 ← ir (← ExceptT.mk [[&p divides ((&0))]])
  let l2 ← HolLight.SPEC ([[0]]) (← HolLight.GEN_ALL int_of_num)
  let l3 ← HolLight.ONCE_REWRITE_RULE [l2] l1
  let l4 ← HolLight.SPECL [([[f:num->real]]), ([[n:num]]), ([[1]])] IS_INT_SUM
  let l5 ← prove ([[(!v. 1 <= v /\ v <= SUC n ==> integer (f v)) ==> (!i. 1 <= i /\ i <= n ==> integer (f i))]])
     (MESON_TAC [(← ar (← ExceptT.mk [[v <= n ==> v <= SUC n]]))])
  let l6 ← HolLight.IMP_TRANS l5 l4
  let l7 ← prove ([[(!v. 1 <= v /\ v <= SUC n ==> (integer (f v)) /\  (&p) divides int_of_real (f v)) ==> (&p) divides int_of_real (f (SUC n))]])
     (MESON_TAC [(← ar (← ExceptT.mk [[1 <= (SUC n) /\ SUC n <= SUC n]]))])
  let l9 ← prove ([[(!v. 1 <= v /\ v <= SUC n ==> integer (f v)) ==> integer (f (SUC n))]])
     (MESON_TAC [(← ar (← ExceptT.mk [[1 <= SUC n /\ SUC n <= SUC n]]))])
  let tm := ([[\(v:num).integer (f v) /\ (&p) divides int_of_real (f v)]])
  let l10 ← HolLight.BETA_RULE (← HolLight.SPEC tm SHRIVER)
  let l11 ← HolLight.UNDISCH (← HolLight.SPEC ([[1]]) (← HolLight.GEN ([[m:num]]) l10))
  let h2 ← ar (← ExceptT.mk [[1 <= SUC n]])
  let h1 ← ar (← ExceptT.mk [[0 < 1]])
  prove ([[! f p n.
       (!v.1<= v /\ v <=  n ==>
        integer (f v) /\
        &p divides int_of_real (f v)) ==>
        (&p divides int_of_real (sum (1..n) f))]])
   (STRIP_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
       [SIMP_TAC [h1, l0, SUM_CLAUSES, l3],
         DISCH_TAC THEN
         (SIMP_TAC [SUM_CLAUSES_NUMSEG, h2]) THEN
         (MATCH_MP_TAC DIVIDES_INT_OF_REAL_ADD) THEN CONJ_TAC THENL
         [ASM_SIMP_TAC [l6],
           CONJ_TAC THENL
           [ASM_SIMP_TAC [l9],
             CONJ_TAC THENL
             [ASM_SIMP_TAC [l11],
               ASM_SIMP_TAC [l7]]]]])
  : ExceptT String IO thm).run
#eval replay ITCHY_LEMMA

def GOTTA_DO_DISHES_LEMMA : thm := keep "GOTTA_DO_DISHES_LEMMA" fun _ => (do
  let mk_lemma := fun x y => (do
        let lem0 ← HolLight.SPECL [x, y, ([[z:int]])] DIVIDES_SUM_NOT_ZERO
        (do
        let lem1 ← tt (← ExceptT.mk [[(X /\ Y ==> Z) <=> (X ==> Y ==> Z)]])
        HolLight.UNDISCH (← HolLight.UNDISCH (← HolLight.ONCE_REWRITE_RULE [lem1] lem0)) : ExceptT String IO _) : ExceptT String IO _)
  let mk_tac := fun x y => HolLight.tactic_of do
        pure ((ASM_REWRITE_TAC [(← HolLight.GSYM int_of_num), INT_OF_REAL_NEG_INT_OF_NUM]) THEN
          STRIP_TAC THEN
          (REWRITE_TAC [(← HolLight.GSYM int_neg_th), (← HolLight.GSYM int_eq), (← HolLight.GSYM int_add_th), (← HolLight.GSYM int_of_num_th)]) THEN
          (ACCEPT_TAC (← mk_lemma x y)))
  prove ([[!(x:real) (y:real).
       (integer x) /\ (integer y) ==>
       (?(z:int).(~(z divides (int_of_real x)))
           /\ (z divides (int_of_real y)))
       ==> ~(x + y = &0)]])
   ((ONCE_REWRITE_TAC [is_int]) THEN
      (STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC) THENL
      [mk_tac ([[(&n):int]]) ([[(&n'):int]]),
        mk_tac ([[(&n):int]]) ([[--(&n'):int]]),
        mk_tac ([[--(&n):int]]) ([[(&n'):int]]),
        mk_tac ([[--(&n):int]]) ([[--(&n'):int]])])
  : ExceptT String IO thm).run
#eval replay GOTTA_DO_DISHES_LEMMA

def RAINY_DAY : thm := keep "RAINY_DAY" fun _ => (do
  let ss3 ← HolLight.SPECL [([[int_of_num n]]), ([[(&p):int]])] INT_PRIME_COPRIME_LT
  let ss4 ← HolLight.ONCE_REWRITE_RULE [(← ar (← ExceptT.mk [[abs ((&x):int) = &x]]))] ss3
  let ss40 ← prove ([[!(x:num) (y:num).  (int_of_num x) < (int_of_num y) <=> (real_of_num x) < (real_of_num y)]])
     (SIMP_TAC [INT_OF_NUM_LT, REAL_OF_NUM_LT])
  let ss5 ← HolLight.ONCE_REWRITE_RULE [ss40, INT_COPRIME_SYM, INT_PRIME_NUM_PRIME] ss4
  let ss6 ← HolLight.SPECL [([[(&p):int]]), ([[(&n):int]]), ([[int_of_real y]])] INT_COPRIME_DIVPROD
  let ss7 ← HolLight.ONCE_REWRITE_RULE [(← tt (← ExceptT.mk [[(X /\ Y ==> Z) <=> (Y ==> X ==> Z)]]))] ss6
  let ss8 ← HolLight.IMP_TRANS ss5 ss7
  let ss9 ← HolLight.ONCE_REWRITE_RULE [(← tt (← ExceptT.mk [[(A /\ B /\ C ==> D ==> E) <=> (A ==> B ==> C ==> D ==> E)]]))] ss8
  let ss10 ← HolLight.UNDISCH ss9
  let h1 ← rr (← ExceptT.mk [[(y:real) > z <=> z < y]])
  prove ([[! p x y.
       prime p ==>
       (&p) > x ==>
       integer x ==>
       x > (&0) ==>
       integer y ==>
       (((&p) divides (int_of_real (x * y)))
        <=> ((&p) divides int_of_real y))]])
   ((REPEAT STRIP_TAC) THEN (ASM_SIMP_TAC [INT_OF_REAL_MUL]) THEN
      EQ_TAC THENL
      [(SIMP_TAC [INT_DIVIDES_LMUL]) THEN
        (UNDISCH_TAC ([[integer x]])) THEN
        (ONCE_REWRITE_TAC [is_int]) THEN
        STRIP_TAC THENL
        [(ASM_REWRITE_TAC []) THEN
          (ONCE_REWRITE_TAC [(← HolLight.GSYM int_of_num)]) THEN
          (UNDISCH_TAC ([[(&(p:num)) > (x:real)]])) THEN
          (UNDISCH_TAC ([[(x:real) > &0]])) THEN
          (ASM_REWRITE_TAC []) THEN
          (ONCE_REWRITE_TAC [h1]) THEN
          (ACCEPT_TAC ss10),
          ASM_ARITH_TAC],
        (SIMP_TAC [INT_DIVIDES_LMUL])])
  : ExceptT String IO thm).run
#eval replay RAINY_DAY

def PLANET_MATH_gamma : thm := keep "PLANET_MATH_gamma" fun _ => (do
  let lemma01 ← HolLight.SPECL [([[\i. EL i c * poly (SOD (g n p)) (&i)]]), ([[n:num]]), ([[k:num]])] IS_INT_SUM
  let lemma02 ← HolLight.BETA_RULE lemma01
  let lemma021 ← HolLight.UNDISCH JUNE_LEMMA
  let lemma022 ← HolLight.UNDISCH_ALL (← ar (← ExceptT.mk [[n > 0 ==> p > n ==> p > 1]]))
  let lemma023 ← HolLight.DISCH_ALL (← ExceptT.mk (Session.SIMP_RULE [lemma022] lemma021))
  let lemma04 ← HolLight.UNDISCH (← HolLight.UNDISCH lemma023)
  let lemma08 ← HolLight.ISPECL [([[c:(real)list]]), ([[v:num]]), ([[integer]])] ALL_IMP_EL
  let lemma09 ← HolLight.ADD_ASSUM ([[n > 0]]) (← HolLight.UNDISCH lemma08)
  let lemma10 ← HolLight.ADD_ASSUM ([[n = PRE (LENGTH (c:(real)list))]]) lemma09
  let lemma11 ← ar (← ExceptT.mk [[n > 0 ==> (n = PRE (LENGTH (c:(real)list))) ==> ((v < LENGTH c) <=> (v <= n))]])
  let lemma12 ← HolLight.UNDISCH (← HolLight.UNDISCH lemma11)
  let lemma13 ← HolLight.ONCE_REWRITE_RULE [lemma12] lemma10
  let lemma15 ← HolLight.CONJ (← HolLight.UNDISCH (← HolLight.UNDISCH lemma04)) (← HolLight.UNDISCH lemma13)
  let lemma16 ← HolLight.MATCH_MP INTEGER_MUL (← HolLight.ONCE_REWRITE_RULE [CONJ_SYM] lemma15)
  let lemma17 ← HolLight.DISCH ([[v <= (n:num)]]) lemma16
  let lemma18 ← ADD_ASSUM_DISCH ([[k <= (v:num)]]) lemma17
  let lemma19 ← HolLight.ONCE_REWRITE_RULE [(← tt (← ExceptT.mk [[(X ==> Y ==> Z) <=> ((X /\ Y) ==> Z)]]))] lemma18
  let lemma20 ← HolLight.GEN ([[v:num]]) lemma19
  let lemma21 ← HolLight.GEN ([[k:num]]) (← HolLight.MATCH_MP lemma02 lemma20)
  let lemma29 ← HolLight.SPEC ([[0]]) lemma21
  let lemma30 ← HolLight.GSYM (← HolLight.ASSUME ([[n = PRE (LENGTH (c:(real)list))]]))
  let lemma300 ← HolLight.SPECL [([[f:(num -> real)]]), ([[0]]), ([[PRE (LENGTH (c:(real)list))]])] SUM_CLAUSES_LEFT
  let lemma31 ← HolLight.ADD_ASSUM ([[n > 0]]) (← HolLight.ADD_ASSUM ([[n = PRE (LENGTH (c:(real)list))]]) lemma300)
  let lemma32 ← HolLight.MP lemma31 (← ar (← ExceptT.mk [[0 <= PRE (LENGTH (c:(real)list))]]))
  let lemma0000 ← BRW ([[(X ==> Y ==> Z) <=> ((X /\ Y) ==> Z)]]) GOTTA_DO_DISHES_LEMMA
  let lemmaa00 ← HolLight.UNDISCH PLANET_MATH_alpha
  let lemmaa03 ← ar (← ExceptT.mk [[n >0 ==> ((n = PRE (LENGTH (c:(real)list))) ==> 0 < (LENGTH c))]])
  let lemmaa04 ← HolLight.ISPECL [([[c:(real)list]]), ([[0]]), ([[integer]])] ALL_IMP_EL
  let lemmaa05 ← HolLight.MP (← HolLight.UNDISCH lemmaa04) (← HolLight.UNDISCH (← HolLight.UNDISCH lemmaa03))
  let c1 ← ar (← ExceptT.mk [[n > 0 ==> n = PRE (LENGTH (c:(real)list)) ==> 0 < (LENGTH (c:(real)list))]])
  let c2 ← HolLight.UNDISCH (← HolLight.UNDISCH c1)
  let c3 ← HolLight.MP (← HolLight.UNDISCH lemmaa04) c2
  let c4 ← HolLight.CONJUNCT1 (← HolLight.UNDISCH (← HolLight.UNDISCH (← HolLight.UNDISCH PLANET_MATH_alpha)))
  let c40 ← HolLight.CONJUNCT2 (← HolLight.UNDISCH (← HolLight.UNDISCH (← HolLight.UNDISCH PLANET_MATH_alpha)))
  let c5 ← HolLight.SPECL [([[p:num]]), ([[(EL 0 c):real]]), ([[poly (SOD (g n p)) (&0)]])] RAINY_DAY
  let c7 ← HolLight.UNDISCH (← HolLight.UNDISCH c5)
  let c8 ← ExceptT.mk (Session.SIMP_RULE [c3] c7)
  let c9 ← HolLight.UNDISCH c8
  let c10 ← ExceptT.mk (Session.SIMP_RULE [c4] c9)
  let d0 ← HolLight.UNDISCH PLANET_MATH_beta
  let d1 ← BRW ([[(X ==> Y ==> Z) <=> (Y ==> X ==> Z)]]) d0
  let d2 ← ExceptT.mk (Session.SIMP_RULE [(← HolLight.UNDISCH (← ar (← ExceptT.mk [[p > (n:num) ==> n > 0 ==> p > 1]])))] d1)
  let d3 ← HolLight.UNDISCH d2
  let d8 ← HolLight.CONJUNCT2 (← HolLight.UNDISCH (← HolLight.SPEC_ALL d3))
  let d9 ← HolLight.SPECL [([[(&p):int]]), ([[int_of_real (EL v c)]]), ([[int_of_real (poly (SOD (g n p)) (&v))]])] INT_DIVIDES_LMUL
  let d10 ← HolLight.ADD_ASSUM ([[ALL integer c]]) d9
  let d11 ← HolLight.ADD_ASSUM ([[n = PRE (LENGTH (c:(real)list))]]) d10
  let d12 ← HolLight.ADD_ASSUM ([[1 <= v /\ v <= n]]) d11
  let d13 ← HolLight.CONJUNCT1 (← HolLight.UNDISCH (← HolLight.SPEC_ALL d3))
  let d14 ← HolLight.DISCH ([[1 <= v]]) (← HolLight.ADD_ASSUM ([[1 <= v]]) lemma13)
  let d15 ← BRW ([[(X ==> Y ==> Z) <=> (X /\ Y ==> Z)]]) d14
  let d16 ← HolLight.UNDISCH d15
  let d17 ← HolLight.CONJ d16 d13
  let d18 ← HolLight.GSYM (← HolLight.MATCH_MP INT_OF_REAL_MUL d17)
  let d19 ← HolLight.ONCE_REWRITE_RULE [d18] d12
  let d20 ← HolLight.MP d19 d8
  let d21 ← HolLight.UNDISCH (← HolLight.SPECL [([[1]]), ([[v:num]])] (← HolLight.GEN ([[k:num]]) lemma20))
  let d22 ← HolLight.CONJ d21 d20
  let d23 ← HolLight.DISCH ([[1 <=v /\ v <= n]]) d22
  let d24 ← HolLight.GEN ([[v:num]]) d23
  let d25 ← HolLight.MATCH_MP ITCHY_LEMMA d24
  let h1 ← ar (← ExceptT.mk [[0 + 1 = 1]])
  prove ([[n > 0 ==>
     p > n ==>
     prime p ==>
     &p > (EL 0 c) ==>
     (EL 0 c) > (&0) ==>
     n = PRE (LENGTH (c)) ==>
     (ALL integer c) ==>
     ( (integer (LHS c (g n p))) /\ ~((LHS c (g n p)) = &0))]])
   (((REPEAT STRIP_TAC) THENL
        [(ONCE_REWRITE_TAC [Pm_eqn4.LHS]) THEN (SIMP_TAC [lemma30, lemma29]),
          (UNDISCH_TAC ([[LHS c (g n p) = &0]])) THEN
          (REWRITE_TAC [Pm_eqn4.LHS]) THEN
          (SIMP_TAC [lemma32, h1]) THEN
          (ONCE_REWRITE_TAC [lemma30]) THEN
          (MATCH_MP_TAC lemma0000) THEN
          CONJ_TAC THENL
          [CONJ_TAC THENL
            [(MATCH_MP_TAC INTEGER_MUL) THEN (ASM_SIMP_TAC [lemmaa00, lemmaa05]),
              (ACCEPT_TAC (← HolLight.SPEC ([[1]]) lemma21))],
            (EXISTS_TAC ([[(&p):int]])) THEN CONJ_TAC THENL
            [(ONCE_REWRITE_TAC [c10]) THEN (ASM_SIMP_TAC [c40]),
             (ACCEPT_TAC d25)]]]))
  : ExceptT String IO thm).run
#eval replay PLANET_MATH_gamma

#eval (do
  replay N_IS_INT_2
  replay NEG_N_IS_INT_2
  replay INT_OF_REAL_ADD
  replay INT_OF_REAL_MUL
  replay INT_OF_REAL_CONV_lemma
  replay ALL_IS_INT
  replay ALL_IS_INT_POLY_ADD
  replay ALL_IS_INT_POLY_CMUL_2
  replay ALL_IS_INT_POLY_MUL
  replay NOT_POLY_MUL_ITER_NIL
  replay ALL_IS_INT_POLY_MUL_ITER
  replay ALL_IS_INT_POLY_EXP
  replay BLAHBLAH
  replay BLAHBLAH3
  replay TELEVISION
  replay JOSHUA
  replay POLY_MUL_HD
  replay POLY_MUL_ITER_HD_FACTORIAL
  replay PLANETMATH_THM_5_1
  replay as_def
  replay g_eq_As
  replay prefix_As_zero
  replay fact_As
  replay ALL_integer_As
  replay POLY_DIFF_AUX_LEM1
  replay EL_POLY_DIFF
  replay POLY_AT_ZERO
  replay PDI_POLY_DIFF_COMM_2
  replay EL_PDI_AT_ZERO
  replay EL_PDI_AT_ZERO2
  replay POLY_CMUL_PDI
  replay LENGTH_g
  replay LENGTH_As
  replay REAL_MUL_RDIV
  replay REAL_MUL_DIV_ASSOC
  replay IS_INT_FACT_DIV
  replay SATURDAY_LEMMA
  replay SHRIVER
  replay IS_INT_SUM
  replay ALL_IMP_EL
  replay KEY_LEMMA
  replay KEY_LEMMA2
  replay NOT_g_NIL
  replay FACT_DIV_RCANCELS_2
  replay PSUM_ITERATE_2
  replay PLANETMATH_EQN_5_2
  replay PLANETMATH_DIVIDES_FACT_PRIME_1
  replay INT_OF_REAL_NEG_NUM
  replay ABS_EQ_ONE
  replay POW_NEG_1
  replay NUM_DIVIDES_INT_DIVIDES
  replay SON_OF_A_GUN
  replay MAY_LEMMA
  replay PLANET_MATH_alpha_1
  replay PLANET_MATH_alpha_2
  replay INT_OF_REAL_NEG_INT_OF_NUM
  replay PLANET_MATH_alpha_3
  replay PLANET_MATH_alpha
  replay REAL_FACT_NZ
  replay IS_INT_FACT_DIV_FACT_DIV_FACT
  replay POLY_CMUL_EL
  replay PDI_COEFF_FACT
  replay POLY_DIVIDES_POLY_DIFF
  replay POLY_DIVIDES_MUL
  replay POLY_DIVIDES_MUL3
  replay POLY_DIVIDES_POLY_MUL_ITER
  replay POLY_DIVIDES_POLY_EXP2
  replay POLY_EXP_ONE
  replay POLY_DIVIDES_ROOT
  replay POLY_DIVIDES_PDI
  replay POLY_DIVIDES_PDI2
  replay TAIL_GUNNER
  replay IS_INT_POLY
  replay INV_POLY_CMUL
  replay INV_POLY_CMUL2
  replay POLY_CMUL_EQUALS
  replay PDI_LENGTH_THM
  replay CAPTAINS_CLOTHES
  replay MESSY_JESSE2
  replay INTEGER_PSUM
  replay INT_DIVIDES_PSUM
  replay PLANET_MATH_beta
  replay JUNE_LEMMA
  replay DIVIDES_SUM_NOT_ZERO
  replay NUM_OF_INT_ABS
  replay INT_DIVIDES_IMP_ABS_NUM_DIVIDES
  replay INT_PRIME_NUM_PRIME
  replay DIVIDES_INT_OF_REAL_ADD
  replay ITCHY_LEMMA
  replay GOTTA_DO_DISHES_LEMMA
  replay RAINY_DAY
  replay PLANET_MATH_gamma
  IO.println "module Pm_eqn4_lhs :\n  sig\n    val N_IS_INT : thm\n    val NEG_N_IS_INT : thm\n    val INT_OF_REAL_ADD : thm\n    val INT_OF_REAL_MUL : thm\n    val INT_OF_REAL_CONV_helper : term -> term * term list * term list\n    val INT_OF_REAL_CONV : term -> thm\n    val ALL_IS_INT : thm\n    val ALL_IS_INT_POLY_ADD : thm\n    val ALL_IS_INT_POLY_CMUL : thm\n    val ALL_IS_INT_POLY_MUL : thm\n    val NOT_POLY_MUL_ITER_NIL : thm\n    val ALL_IS_INT_POLY_MUL_ITER : thm\n    val ALL_IS_INT_POLY_EXP : thm\n    val BLAHBLAH : thm\n    val BLAHBLAH3 : thm\n    val TELEVISION : thm\n    val JOSHUA : thm\n    val POLY_MUL_HD : thm\n    val POLY_MUL_ITER_HD_FACTORIAL : thm\n    val PLANETMATH_THM_5_1 : thm\n    val as_def : thm\n    val g_eq_As : thm\n    val prefix_As_zero : thm\n    val fact_As : thm\n    val ALL_integer_As : thm\n    val POLY_DIFF_AUX_LEM1 : thm\n    val EL_POLY_DIFF : thm\n    val POLY_AT_ZERO : thm\n    val PDI_POLY_DIFF_COMM : thm\n    val EL_PDI_AT_ZERO : thm\n    val EL_PDI_AT_ZERO2 : thm\n    val POLY_CMUL_PDI : thm\n    val LENGTH_g : thm\n    val LENGTH_As : thm\n    val REAL_MUL_RDIV : thm\n    val REAL_MUL_DIV_ASSOC : thm\n    val IS_INT_FACT_DIV : thm\n    val SATURDAY_LEMMA : thm\n    val SHRIVER : thm\n    val IS_INT_SUM : thm\n    val ALL_IMP_EL : thm\n    val KEY_LEMMA : thm\n    val KEY_LEMMA2 : thm\n    val NOT_g_NIL : thm\n    val FACT_DIV_RCANCELS : thm\n    val PSUM_ITERATE : thm\n    val PLANETMATH_EQN_5_2 : thm\n    val PLANETMATH_DIVIDES_FACT_PRIME_1 : thm\n    val INT_OF_REAL_NEG_NUM : thm\n    val ABS_EQ_ONE : thm\n    val POW_NEG_1 : thm\n    val NUM_DIVIDES_INT_DIVIDES : thm\n    val SON_OF_A_GUN : thm\n    val MAY_LEMMA : thm\n    val PLANET_MATH_alpha_1 : thm\n    val PLANET_MATH_alpha_2 : thm\n    val INT_OF_REAL_NEG_INT_OF_NUM : thm\n    val PLANET_MATH_alpha_3 : thm\n    val PLANET_MATH_alpha : thm\n    val REAL_FACT_NZ : thm\n    val IS_INT_FACT_DIV_FACT_DIV_FACT : thm\n    val POLY_CMUL_EL : thm\n    val PDI_COEFF_FACT : thm\n    val POLY_DIVIDES_POLY_DIFF : thm\n    val POLY_DIVIDES_MUL : thm\n    val POLY_DIVIDES_MUL3 : thm\n    val POLY_DIVIDES_POLY_MUL_ITER : thm\n    val POLY_DIVIDES_POLY_EXP2 : thm\n    val POLY_EXP_ONE : thm\n    val POLY_DIVIDES_ROOT : thm\n    val POLY_DIVIDES_PDI : thm\n    val POLY_DIVIDES_PDI2 : thm\n    val TAIL_GUNNER : thm\n    val IS_INT_POLY : thm\n    val INV_POLY_CMUL : thm\n    val INV_POLY_CMUL2 : thm\n    val POLY_CMUL_EQUALS : thm\n    val PDI_LENGTH_THM : thm\n    val CAPTAINS_CLOTHES : thm\n    val MESSY_JESSE2 : thm\n    val INTEGER_PSUM : thm\n    val INT_DIVIDES_PSUM : thm\n    val PLANET_MATH_beta : thm\n    val JUNE_LEMMA : thm\n    val DIVIDES_SUM_NOT_ZERO : thm\n    val NUM_OF_INT_ABS : thm\n    val INT_DIVIDES_IMP_ABS_NUM_DIVIDES : thm\n    val INT_PRIME_NUM_PRIME : thm\n    val DIVIDES_INT_OF_REAL_ADD : thm\n    val ITCHY_LEMMA : thm\n    val GOTTA_DO_DISHES_LEMMA : thm\n    val RAINY_DAY : thm\n    val PLANET_MATH_gamma : thm\n   end" : IO Unit)
end Pm_eqn4_lhs

#eval phrase 33
namespace Finale
def IS_INT_NZ_ABS_GE_1 : thm := keep "IS_INT_NZ_ABS_GE_1" fun _ => (do
  let lemmy0 ← rr (← ExceptT.mk [[(x:real) < y <=> ~(y <= x)]])
  let lemmy1 ← HolLight.ONCE_REWRITE_RULE [lemmy0] REAL_NZ_IMP_LT
  let lemmy2 ← rr (← ExceptT.mk [[(real_neg x) = &0 <=> x = &0]])
  let lemmy3 ← rr (← ExceptT.mk [[&0 <= (real_neg x) <=> x <= &0]])
  let h1 ← tt (← ExceptT.mk [[(X /\ Y ==> Z) <=> (X ==> Y ==> Z)]])
  prove ([[!x. ((integer x) /\ ~(x = &0)) ==> ~(abs x < &1)]])
   ((ONCE_REWRITE_TAC [is_int]) THEN
      (ONCE_REWRITE_TAC [h1]) THEN
      STRIP_TAC THEN STRIP_TAC THENL
      [(ASM_REWRITE_TAC []) THEN (SIMP_TAC [REAL_ABS_NUM]) THEN
        (ONCE_REWRITE_TAC [REAL_OF_NUM_LT, REAL_OF_NUM_EQ]) THEN
        ARITH_TAC,
        (ASM_REWRITE_TAC []) THEN (ONCE_REWRITE_TAC [real_abs]) THEN
        (ONCE_REWRITE_TAC [lemmy2, lemmy3]) THEN
        (ONCE_REWRITE_TAC [REAL_OF_NUM_EQ]) THEN
        (SIMP_TAC [lemmy1, SessionLibrary.Analysis.REAL_NEG_NEG]) THEN
        (ONCE_REWRITE_TAC [REAL_OF_NUM_LT]) THEN ARITH_TAC])
  : ExceptT String IO thm).run
#eval replay IS_INT_NZ_ABS_GE_1

def PBR_LEMMA : thm := keep "PBR_LEMMA" fun _ => (do
  prove ([[!n1 n2 n3 p. p > MAX n1 (MAX n2 n3) ==> (p > n1 /\ p > n2 /\ p > n3)]])
   ((REWRITE_TAC [MAX]) THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval replay PBR_LEMMA

def BIGGER_PRIME_EXISTS : thm := keep "BIGGER_PRIME_EXISTS" fun _ => (do
  let lem0 ← prove ([[{x | prime x} = prime]])
     (SET_TAC [])
  let lem1 ← ar (← ExceptT.mk [[p > n <=> ~(p <= (n:num))]])
  prove ([[!(n:num). ?p. prime p /\ p > n]])
   (MESON_TAC [PRIMES_INFINITE, lem0, lem1, IN_ELIM_THM, num_FINITE, INFINITE])
  : ExceptT String IO thm).run
#eval replay BIGGER_PRIME_EXISTS

def BUD_LEMMA : thm := keep "BUD_LEMMA" fun _ => (do
  let amigo3 ← HolLight.SPECL [([[N:num]]), ([[n1:num]]), ([[n2:num]]), ([[p:num]])] PBR_LEMMA
  let amigo4 ← HolLight.UNDISCH amigo3
  let h1 ← tt (← ExceptT.mk [[(X /\ Y ==> Z) <=> (X ==> Y ==> Z)]])
  prove ([[!(f:num->bool) (n1:num) (n2:num).((?(N:num) . !(p:num).p > N ==> f p)
      ==> (? (p0:num).prime p0 /\ p0 > n1 /\ p0 > n2 /\ f p0))]])
   ((REPEAT STRIP_TAC) THEN
      (CHOOSE_TAC (← HolLight.SPEC ([[MAX N (MAX n1 n2)]]) BIGGER_PRIME_EXISTS)) THEN
      (EXISTS_TAC ([[p:num]])) THEN
      (UNDISCH_TAC ([[prime p /\ p > MAX N (MAX n1 n2)]])) THEN
      (ONCE_REWRITE_TAC [h1]) THEN
      (DISCH_TAC THEN DISCH_TAC) THEN
      (ASM_SIMP_TAC [amigo4]))
  : ExceptT String IO thm).run
#eval replay BUD_LEMMA

-- let ALL_IMP_EL = ... (rebinds ALL_IMP_EL)
def ALL_IMP_EL_2 : thm := keep "ALL_IMP_EL_2" fun _ => (do
  prove ([[! (l:(a)list) i P. (ALL P l) ==> (i < LENGTH l) ==> P (EL i l)]])
   (SIMP_TAC [(← HolLight.GSYM Session.listThms2.ALL_EL)])
  : ExceptT String IO thm).run
#eval replay ALL_IMP_EL_2

def HAMMS_LEMMA : thm := keep "HAMMS_LEMMA" fun _ => (do
  let erica0 ← HolLight.UNDISCH_ALL Pm_eqn4_lhs.PLANET_MATH_gamma
  let erica1 ← HolLight.MATCH_MP IS_INT_NZ_ABS_GE_1 erica0
  let erica2 := ASM_REWRITE_RULE [] erica1
  let erica3 ← HolLight.SPEC_ALL Pm_eqn4_rhs.LT_ONE
  let erica4 ← HolLight.MATCH_MP BUD_LEMMA erica3
  let erica5 ← HolLight.ADD_ASSUM ([[ALL integer c]]) erica4
  let erica8 ← ar (← ExceptT.mk [[(n = PRE (LENGTH (c:(real)list))) ==> n > 0 ==>
     0 < (LENGTH c) ]])
  let erica9 ← HolLight.UNDISCH (← HolLight.UNDISCH erica8)
  let erica10 ← HolLight.UNDISCH (← HolLight.ISPECL [([[c:(real)list]]), ([[0]]), ([[integer]])] ALL_IMP_EL_2)
  let erica11 ← HolLight.MP erica10 erica9
  let erica12 ← HolLight.ONCE_REWRITE_RULE [is_int] erica11
  let erica13 ← ar (← ExceptT.mk [[!n. ~(( -- (real_of_num n)) > &0)]])
  let erica14 ← prove ([[n = PRE (LENGTH c) ==>
          n > 0 ==>
          ALL integer c ==>
          (EL 0 c) > &0 ==>
          ?n. EL 0 c = &n]])
     (MESON_TAC [(← HolLight.DISCH_ALL erica12), erica13])
  let erica15 ← HolLight.UNDISCH_ALL erica14
  let sim0 ← HolLight.SELECT_RULE (← HolLight.ASSUME (concl erica15))
  let sim1 ← HolLight.DISCH (concl erica15) sim0
  let sim2 ← HolLight.MP sim1 erica15
  let erica18 ← HolLight.SPECL [([[n:num]]), ([[@n. EL 0 c = (real_of_num n)]])] erica5
  let erica19 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM REAL_OF_NUM_GT)] erica18
  let erica20 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM sim2)] erica19
  let erica21 ← HolLight.ONCE_REWRITE_RULE [REAL_OF_NUM_GT] erica20
  let erica22 ← HolLight.DISCH ([[(real_of_num p) > EL 0 c]]) erica2
  let erica23 ← HolLight.DISCH ([[(p:num) > n]]) erica22
  let erica24 ← HolLight.DISCH ([[prime (p:num)]]) erica23
  let erica25 ← HolLight.GEN ([[p:num]]) erica24
  let erica28 ← HolLight.UNDISCH (← ar (← ExceptT.mk [[n = PRE (LENGTH (c:(real)list)) ==> ((n > 0) <=> (LENGTH c) > 1)]]))
  let erica29 ← HolLight.UNDISCH (← HolLight.ONCE_REWRITE_RULE [erica28] (← HolLight.DISCH ([[n > 0]]) erica25))
  let erica30 ← HolLight.UNDISCH (← HolLight.ONCE_REWRITE_RULE [erica28] (← HolLight.DISCH ([[n > 0]]) erica21))
  prove ([[~(?c. ALL integer c /\
            LENGTH c > 1 /\
            EL 0 c > &0 /\
            (!f. LHS c f = RHS c f))]])
   ((CONV_TAC NNF_CONV) THEN
        (REPEAT STRIP_TAC) THEN
        (ASM_MESON_TAC [(← HolLight.DISCH_ALL erica29), (← HolLight.DISCH_ALL erica30)]))
  : ExceptT String IO thm).run
#eval replay HAMMS_LEMMA

def TRANSCENDENTAL_E : thm := keep "TRANSCENDENTAL_E" fun _ => (do
  prove ([[transcendental (exp (&1))]])
   (MESON_TAC [HAMMS_LEMMA, Pm_eqn4.PLANETMATH_EQN_4])
  : ExceptT String IO thm).run
#eval replay TRANSCENDENTAL_E

#eval (do
  replay IS_INT_NZ_ABS_GE_1
  replay PBR_LEMMA
  replay BIGGER_PRIME_EXISTS
  replay BUD_LEMMA
  replay ALL_IMP_EL_2
  replay HAMMS_LEMMA
  replay TRANSCENDENTAL_E
  IO.println "module Finale :\n  sig\n    val IS_INT_NZ_ABS_GE_1 : thm\n    val PBR_LEMMA : thm\n    val BIGGER_PRIME_EXISTS : thm\n    val BUD_LEMMA : thm\n    val ALL_IMP_EL : thm\n    val HAMMS_LEMMA : thm\n    val TRANSCENDENTAL_E : thm\n   end" : IO Unit)
end Finale

#eval phrase 34
#eval Finale.TRANSCENDENTAL_E

end Hol100.EIsTranscendental
