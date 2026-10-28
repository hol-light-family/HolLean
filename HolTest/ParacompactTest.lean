/- File: HolTest/ParacompactTest.lean
Runtime test suite: Multivariate/paracompact.ml
(HolMultiLib/Paracompact.lean, wired by SessionMultiLib/Paracompact.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/paracompact.ml"`, then `string_of_thm`).  The whole file
is also compared with HOL Light by tools/pcdiff: all 40 exported theorems
structurally and by their printed forms.

The theorems chosen here are spread over the file: countable paracompactness
and Dowker's characterization, Nagata-Smirnov metrization, collectionwise
normality and Smirnov metrization, and Michael's characterization of
paracompactness with the closed map image theorem.

Loading paracompact.ml (`ensureParacompact`) builds every bundle in file
order; a proof that failed would stop the load, which the `make verify` gates
catch. -/

import HolTest.CommonTest
import SessionMultiLib.Paracompact

open HolCore.Kernel Session SessionMultiLib.Paracompact
open HolTest.CommonTest HolLight.Syntax

#eval ensureParacompact

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- Countably paracompact spaces and the Dowker characterization.          -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "paracompact.ml countably_paracompact_space" countably_paracompact_space
  "|- forall top.
          countably_paracompact_space top <=>
          (forall U.
               COUNTABLE U /\\
               (forall u. u IN U ==> open_in top u) /\\
               UNIONS U = topspace top
               ==> (exists V.
                        (forall v. v IN V ==> open_in top v) /\\
                        UNIONS V = topspace top /\\
                        (forall v. v IN V ==> (exists u. u IN U /\\ v SUBSET u)) /\\
                        locally_finite_in top V))"
#eval thmCheck "paracompact.ml METRIZABLE_IMP_COUNTABLY_PARACOMPACT_SPACE" METRIZABLE_IMP_COUNTABLY_PARACOMPACT_SPACE
  "|- forall top. metrizable_space top ==> countably_paracompact_space top"
#eval thmCheck "paracompact.ml NORMAL_COUNTABLY_PARACOMPACT_CHARACTERIZATION" NORMAL_COUNTABLY_PARACOMPACT_CHARACTERIZATION
  "|- forall top.
          normal_space top
          ==> (countably_paracompact_space top <=>
               (forall f.
                    (forall n. closed_in top (f n)) /\\
                    (forall n. f (SUC n) SUBSET f n) /\\
                    INTERS {f n | n IN (:num)} = {}
                    ==> (exists g.
                             (forall n. open_in top (g n)) /\\
                             (forall n. f n SUBSET g n) /\\
                             INTERS {g n | n IN (:num)} = {})))"
#eval thmCheck "paracompact.ml COUNTABLY_PARACOMPACT_SPACE_CLOSED_SUBSET" COUNTABLY_PARACOMPACT_SPACE_CLOSED_SUBSET
  "|- forall top s.
          countably_paracompact_space top /\\ closed_in top s
          ==> countably_paracompact_space (subtopology top s)"
#eval thmCheck "paracompact.ml COUNTABLY_PARACOMPACT_SPACE_PRODUCT_COMPACT" COUNTABLY_PARACOMPACT_SPACE_PRODUCT_COMPACT
  "|- forall top top'.
          countably_paracompact_space top /\\ compact_space top'
          ==> countably_paracompact_space (prod_topology top top')"

/- ---------------------------------------------------------------------- -/
/- Nagata-Smirnov metrization.                                            -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "paracompact.ml URYSOHN_FUNCTION_G_DELTA" URYSOHN_FUNCTION_G_DELTA
  "|- forall top A.
          normal_space top /\\ closed_in top A /\\ gdelta_in top A
          ==> (exists f.
                   continuous_map (top,euclideanreal) f /\\
                   (forall x. x IN topspace top ==> &0 <= f x /\\ f x <= &1) /\\
                   (forall x. x IN topspace top ==> (f x = &0 <=> x IN A)))"
#eval thmCheck "paracompact.ml NORMAL_SPACE_SIGMA_LOCALLY_FINITE_BASE" NORMAL_SPACE_SIGMA_LOCALLY_FINITE_BASE
  "|- forall top B.
          regular_space top /\\
          (forall b. b IN B ==> open_in top b) /\\
          (forall x u.
               open_in top u /\\ x IN u
               ==> (exists b. b IN B /\\ x IN b /\\ b SUBSET u)) /\\
          sigma_locally_finite_in top B
          ==> normal_space top"
#eval thmCheck "paracompact.ml URYSOHN_FUNCTION_CLOSED_GDELTA" URYSOHN_FUNCTION_CLOSED_GDELTA
  "|- forall top s.
          normal_space top /\\ closed_in top s /\\ gdelta_in top s
          ==> (exists f.
                   continuous_map (top,euclideanreal) f /\\
                   (forall x. x IN topspace top ==> &0 <= f x /\\ f x <= &1) /\\
                   (forall x. x IN s ==> f x = &0) /\\
                   (forall x. x IN topspace top DIFF s ==> &0 < f x))"
#eval thmCheck "paracompact.ml NAGATA_SMIRNOV_METRIZATION" NAGATA_SMIRNOV_METRIZATION
  "|- forall top.
          regular_space top /\\
          hausdorff_space top /\\
          (exists B.
               (forall b. b IN B ==> open_in top b) /\\
               (forall x u.
                    open_in top u /\\ x IN u
                    ==> (exists b. b IN B /\\ x IN b /\\ b SUBSET u)) /\\
               sigma_locally_finite_in top B)
          ==> metrizable_space top"
#eval thmCheck "paracompact.ml PARACOMPACT_LOCALLY_METRIZABLE_SIGMA_LF_BASE" PARACOMPACT_LOCALLY_METRIZABLE_SIGMA_LF_BASE
  "|- forall top.
          paracompact_space top /\\
          hausdorff_space top /\\
          (forall x.
               x IN topspace top
               ==> (exists u.
                        open_in top u /\\
                        x IN u /\\
                        metrizable_space (subtopology top u)))
          ==> (exists B.
                   (forall b. b IN B ==> open_in top b) /\\
                   (forall x u.
                        open_in top u /\\ x IN u
                        ==> (exists b. b IN B /\\ x IN b /\\ b SUBSET u)) /\\
                   sigma_locally_finite_in top B)"

/- ---------------------------------------------------------------------- -/
/- Collectionwise normality and Smirnov metrization.                      -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "paracompact.ml collectionwise_normal_space" collectionwise_normal_space
  "|- forall top.
          collectionwise_normal_space top <=>
          (forall F.
               (forall c. c IN F ==> closed_in top c) /\\
               pairwise DISJOINT F /\\
               locally_finite_in top F
               ==> (exists G.
                        (forall c. c IN F ==> open_in top (G c) /\\ c SUBSET G c) /\\
                        pairwise (\\c d. DISJOINT (G c) (G d)) F))"
#eval thmCheck "paracompact.ml PARACOMPACT_HAUSDORFF_IMP_COLLECTIONWISE_NORMAL" PARACOMPACT_HAUSDORFF_IMP_COLLECTIONWISE_NORMAL
  "|- forall top.
          paracompact_space top /\\ hausdorff_space top
          ==> collectionwise_normal_space top"
#eval thmCheck "paracompact.ml COLLECTIONWISE_NORMAL_SPACE_CLOSED_SUBSET" COLLECTIONWISE_NORMAL_SPACE_CLOSED_SUBSET
  "|- forall top s.
          collectionwise_normal_space top /\\ closed_in top s
          ==> collectionwise_normal_space (subtopology top s)"
#eval thmCheck "paracompact.ml SMIRNOV_METRIZATION" SMIRNOV_METRIZATION
  "|- forall top.
          metrizable_space top <=>
          paracompact_space top /\\
          hausdorff_space top /\\
          locally_metrizable_space top"

/- ---------------------------------------------------------------------- -/
/- Michael's characterization and closed map images.                      -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "paracompact.ml LOCALLY_FINITE_LEVEL_UNION_GEN" LOCALLY_FINITE_LEVEL_UNION_GEN
  "|- forall top A f.
          locally_finite_in top {A n | n IN (:num)} /\\
          (forall n. locally_finite_in top (f n)) /\\
          (forall n s. s IN f n ==> s SUBSET A n) /\\
          (forall m n. ~(m = n) ==> A m INTER A n = {})
          ==> locally_finite_in top (UNIONS {f n | n IN (:num)})"
#eval thmCheck "paracompact.ml CP_IMPLIES_NORMAL_SPACE" CP_IMPLIES_NORMAL_SPACE
  "|- forall top.
          (forall U.
               (forall u. u IN U ==> open_in top u) /\\ UNIONS U = topspace top
               ==> (exists V.
                        (forall v. v IN V ==> closed_in top v) /\\
                        UNIONS V = topspace top /\\
                        (forall v. v IN V ==> (exists u. u IN U /\\ v SUBSET u)) /\\
                        (forall W. W SUBSET V ==> closed_in top (UNIONS W))))
          ==> normal_space top"
#eval thmCheck "paracompact.ml DOWKER_DISCRETE_EXPANSION" DOWKER_DISCRETE_EXPANSION
  "|- forall top s f d.
          normal_space top /\\
          (forall k. k IN s ==> open_in top (f k)) /\\
          pairwise (\\a b. DISJOINT (f a) (f b)) s /\\
          (forall k. k IN s ==> d k SUBSET f k) /\\
          closed_in top (UNIONS {d k | k IN s})
          ==> (exists w.
                   (forall k. k IN s ==> open_in top (w k)) /\\
                   (forall k. k IN s ==> d k SUBSET w k) /\\
                   (forall k. k IN s ==> w k SUBSET f k) /\\
                   locally_finite_in top {w k | k IN s})"
#eval thmCheck "paracompact.ml MICHAEL_PARACOMPACT" MICHAEL_PARACOMPACT
  "|- forall top.
          regular_space top /\\
          (forall U.
               (forall u. u IN U ==> open_in top u) /\\ UNIONS U = topspace top
               ==> (exists V.
                        (forall v. v IN V ==> closed_in top v) /\\
                        UNIONS V = topspace top /\\
                        (forall v. v IN V ==> (exists u. u IN U /\\ v SUBSET u)) /\\
                        (forall W. W SUBSET V ==> closed_in top (UNIONS W))))
          ==> paracompact_space top"
#eval thmCheck "paracompact.ml MICHAEL_PARACOMPACT_EQ" MICHAEL_PARACOMPACT_EQ
  "|- forall top.
          regular_space top
          ==> (paracompact_space top <=>
               (forall U.
                    (forall u. u IN U ==> open_in top u) /\\
                    UNIONS U = topspace top
                    ==> (exists V.
                             (forall v. v IN V ==> closed_in top v) /\\
                             UNIONS V = topspace top /\\
                             (forall v.
                                  v IN V ==> (exists u. u IN U /\\ v SUBSET u)) /\\
                             (forall W. W SUBSET V ==> closed_in top (UNIONS W)))))"
#eval thmCheck "paracompact.ml PARACOMPACT_SPACE_CLOSED_MAP_IMAGE" PARACOMPACT_SPACE_CLOSED_MAP_IMAGE
  "|- forall top top' f.
          paracompact_space top /\\
          hausdorff_space top /\\
          continuous_map (top,top') f /\\
          closed_map (top,top') f /\\
          IMAGE f (topspace top) = topspace top'
          ==> paracompact_space top'"
