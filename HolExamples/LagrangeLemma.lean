/- File: HolExamples/LagrangeLemma.lean
Translation of HOL Light's Examples/lagrange_lemma.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
namespace HolExamples.LagrangeLemma

private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/-- lib.ml's `time` applied to `prove`, as the file uses it (`time prove`). -/
private unsafe def timeThm (f : Unit → ExceptT String IO thm) (x : Unit) : ExceptT String IO thm :=
  ExceptT.mk (HolCore.Lib.time (fun t => (f t).run) x)

/- Nice test for ring procedure and ordered rewriting: Lagrange lemma. -/

#eval phrase 1
#eval Session.prioritize_real

#eval phrase 2
-- Do the problems the (relatively) efficient way using the normalizer.
unsafe def LAGRANGE_4 : thm := keep "LAGRANGE_4" fun _ => (timeThm (fun _ => do
  prove ([[((x1 pow 2) + (x2 pow 2) + (x3 pow 2) + (x4 pow 2)) *
   ((y1 pow 2) + (y2 pow 2) + (y3 pow 2) + (y4 pow 2)) =
     (((((x1*y1) - (x2*y2)) - (x3*y3)) - (x4*y4)) pow 2)  +
     (((((x1*y2) + (x2*y1)) + (x3*y4)) - (x4*y3)) pow 2)  +
     (((((x1*y3) - (x2*y4)) + (x3*y1)) + (x4*y2)) pow 2)  +
     (((((x1*y4) + (x2*y3)) - (x3*y2)) + (x4*y1)) pow 2)]])
   (CONV_TAC REAL_RING)) ()).run
#eval LAGRANGE_4

#eval phrase 3
unsafe def LAGRANGE_8 : thm := keep "LAGRANGE_8" fun _ => (timeThm (fun _ => do
  prove ([[(p1 pow 2 + q1 pow 2 + r1 pow 2 + s1 pow 2 + t1 pow 2 + u1 pow 2 + v1 pow 2 + w1 pow 2) *
   (p2 pow 2 + q2 pow 2 + r2 pow 2 + s2 pow 2 + t2 pow 2 + u2 pow 2 + v2 pow 2 + w2 pow 2)
   = (p1 * p2 - q1 * q2 - r1 * r2 - s1 * s2 - t1 * t2 - u1 * u2 - v1 * v2 - w1 * w2) pow 2 +
     (p1 * q2 + q1 * p2 + r1 * s2 - s1 * r2 + t1 * u2 - u1 * t2 - v1 * w2 + w1 * v2) pow 2 +
     (p1 * r2 - q1 * s2 + r1 * p2 + s1 * q2 + t1 * v2 + u1 * w2 - v1 * t2 - w1 * u2) pow 2 +
     (p1 * s2 + q1 * r2 - r1 * q2 + s1 * p2 + t1 * w2 - u1 * v2 + v1 * u2 - w1 * t2) pow 2 +
     (p1 * t2 - q1 * u2 - r1 * v2 - s1 * w2 + t1 * p2 + u1 * q2 + v1 * r2 + w1 * s2) pow 2 +
     (p1 * u2 + q1 * t2 - r1 * w2 + s1 * v2 - t1 * q2 + u1 * p2 - v1 * s2 + w1 * r2) pow 2 +
     (p1 * v2 + q1 * w2 + r1 * t2 - s1 * u2 - t1 * r2 + u1 * s2 + v1 * p2 - w1 * q2) pow 2 +
     (p1 * w2 - q1 * v2 + r1 * u2 + s1 * t2 - t1 * s2 - u1 * r2 + v1 * q2 + w1 * p2) pow 2]])
   (CONV_TAC REAL_RING)) ()).run
#eval LAGRANGE_8

#eval phrase 4
-- Or we can just use REAL_ARITH, which is also reasonably fast.
unsafe def LAGRANGE_4_2 : thm := keep "LAGRANGE_4_2" fun _ => (timeThm (fun _ => do
  prove ([[((x1 pow 2) + (x2 pow 2) + (x3 pow 2) + (x4 pow 2)) *
   ((y1 pow 2) + (y2 pow 2) + (y3 pow 2) + (y4 pow 2)) =
     (((((x1*y1) - (x2*y2)) - (x3*y3)) - (x4*y4)) pow 2)  +
     (((((x1*y2) + (x2*y1)) + (x3*y4)) - (x4*y3)) pow 2)  +
     (((((x1*y3) - (x2*y4)) + (x3*y1)) + (x4*y2)) pow 2)  +
     (((((x1*y4) + (x2*y3)) - (x3*y2)) + (x4*y1)) pow 2)]])
   REAL_ARITH_TAC2) ()).run
#eval LAGRANGE_4_2

#eval phrase 5
unsafe def LAGRANGE_8_2 : thm := keep "LAGRANGE_8_2" fun _ => (timeThm (fun _ => do
  prove ([[(p1 pow 2 + q1 pow 2 + r1 pow 2 + s1 pow 2 + t1 pow 2 + u1 pow 2 + v1 pow 2 + w1 pow 2) *
   (p2 pow 2 + q2 pow 2 + r2 pow 2 + s2 pow 2 + t2 pow 2 + u2 pow 2 + v2 pow 2 + w2 pow 2)
   = (p1 * p2 - q1 * q2 - r1 * r2 - s1 * s2 - t1 * t2 - u1 * u2 - v1 * v2 - w1 * w2) pow 2 +
     (p1 * q2 + q1 * p2 + r1 * s2 - s1 * r2 + t1 * u2 - u1 * t2 - v1 * w2 + w1 * v2) pow 2 +
     (p1 * r2 - q1 * s2 + r1 * p2 + s1 * q2 + t1 * v2 + u1 * w2 - v1 * t2 - w1 * u2) pow 2 +
     (p1 * s2 + q1 * r2 - r1 * q2 + s1 * p2 + t1 * w2 - u1 * v2 + v1 * u2 - w1 * t2) pow 2 +
     (p1 * t2 - q1 * u2 - r1 * v2 - s1 * w2 + t1 * p2 + u1 * q2 + v1 * r2 + w1 * s2) pow 2 +
     (p1 * u2 + q1 * t2 - r1 * w2 + s1 * v2 - t1 * q2 + u1 * p2 - v1 * s2 + w1 * r2) pow 2 +
     (p1 * v2 + q1 * w2 + r1 * t2 - s1 * u2 - t1 * r2 + u1 * s2 + v1 * p2 - w1 * q2) pow 2 +
     (p1 * w2 - q1 * v2 + r1 * u2 + s1 * t2 - t1 * s2 - u1 * r2 + v1 * q2 + w1 * p2) pow 2]])
   REAL_ARITH_TAC2) ()).run
#eval LAGRANGE_8_2

#eval phrase 6
-- But they can be done (slowly) simply by ordered rewriting.
unsafe def LAGRANGE_4_3 : thm := keep "LAGRANGE_4_3" fun _ => (timeThm (fun _ => do
  prove ([[((x1 pow 2) + (x2 pow 2) + (x3 pow 2) + (x4 pow 2)) *
   ((y1 pow 2) + (y2 pow 2) + (y3 pow 2) + (y4 pow 2)) =
     (((((x1*y1) - (x2*y2)) - (x3*y3)) - (x4*y4)) pow 2)  +
     (((((x1*y2) + (x2*y1)) + (x3*y4)) - (x4*y3)) pow 2)  +
     (((((x1*y3) - (x2*y4)) + (x3*y1)) + (x4*y2)) pow 2)  +
     (((((x1*y4) + (x2*y3)) - (x3*y2)) + (x4*y1)) pow 2)]])
   (REWRITE_TAC [REAL_POW_2, REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB,
              REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB,
              (← Session.REAL_ARITH3 [[a + (b - c) = (a + b) - c]]),
              (← Session.REAL_ARITH3 [[a - (b - c) = a + (c - b)]]),
              (← Session.REAL_ARITH3 [[(a - b) + c = (a + c) - b]]),
              (← Session.REAL_ARITH3 [[(a - b) - c = a - (b + c)]]),
              (← Session.REAL_ARITH3 [[(a - b = c) = (a = b + c)]]),
              (← Session.REAL_ARITH3 [[(a = b - c) = (a + c = b)]]),
              REAL_ADD_AC, REAL_MUL_AC])) ()).run
#eval LAGRANGE_4_3

#eval phrase 7
unsafe def LAGRANGE_8_3 : thm := keep "LAGRANGE_8_3" fun _ => (timeThm (fun _ => do
  prove ([[(p1 pow 2 + q1 pow 2 + r1 pow 2 + s1 pow 2 + t1 pow 2 + u1 pow 2 + v1 pow 2 + w1 pow 2) *
   (p2 pow 2 + q2 pow 2 + r2 pow 2 + s2 pow 2 + t2 pow 2 + u2 pow 2 + v2 pow 2 + w2 pow 2)
   = (p1 * p2 - q1 * q2 - r1 * r2 - s1 * s2 - t1 * t2 - u1 * u2 - v1 * v2 - w1 * w2) pow 2 +
     (p1 * q2 + q1 * p2 + r1 * s2 - s1 * r2 + t1 * u2 - u1 * t2 - v1 * w2 + w1 * v2) pow 2 +
     (p1 * r2 - q1 * s2 + r1 * p2 + s1 * q2 + t1 * v2 + u1 * w2 - v1 * t2 - w1 * u2) pow 2 +
     (p1 * s2 + q1 * r2 - r1 * q2 + s1 * p2 + t1 * w2 - u1 * v2 + v1 * u2 - w1 * t2) pow 2 +
     (p1 * t2 - q1 * u2 - r1 * v2 - s1 * w2 + t1 * p2 + u1 * q2 + v1 * r2 + w1 * s2) pow 2 +
     (p1 * u2 + q1 * t2 - r1 * w2 + s1 * v2 - t1 * q2 + u1 * p2 - v1 * s2 + w1 * r2) pow 2 +
     (p1 * v2 + q1 * w2 + r1 * t2 - s1 * u2 - t1 * r2 + u1 * s2 + v1 * p2 - w1 * q2) pow 2 +
     (p1 * w2 - q1 * v2 + r1 * u2 + s1 * t2 - t1 * s2 - u1 * r2 + v1 * q2 + w1 * p2) pow 2]])
   (REWRITE_TAC [REAL_POW_2, REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB,
              REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB,
              (← Session.REAL_ARITH3 [[a + (b - c) = (a + b) - c]]),
              (← Session.REAL_ARITH3 [[a - (b - c) = a + (c - b)]]),
              (← Session.REAL_ARITH3 [[(a - b) + c = (a + c) - b]]),
              (← Session.REAL_ARITH3 [[(a - b) - c = a - (b + c)]]),
              (← Session.REAL_ARITH3 [[(a - b = c) = (a = b + c)]]),
              (← Session.REAL_ARITH3 [[(a = b - c) = (a + c = b)]]),
              REAL_ADD_AC, REAL_MUL_AC])) ()).run
#eval LAGRANGE_8_3

end HolExamples.LagrangeLemma
