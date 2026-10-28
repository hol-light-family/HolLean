/- File: HolTest/HomologyTest.lean
Runtime test suite: Multivariate/homology.ml (HolMultiLib/Homology.lean, wired
by SessionMultiLib/Homology.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/homology.ml"`, then `string_of_thm`).  The whole file is
also compared with HOL Light by tools/homdiff: all 361 theorems
structurally and by their printed forms.

The theorems chosen here print without invented type variables, so their
printed forms do not depend on type-variable numbering.  They are spread over
the whole file, from the standard simplex at the start to invariance of domain
at the end.

Loading homology.ml (`ensureHomology`) builds every bundle in file order; a
proof that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Homology

open HolCore.Kernel Session SessionMultiLib.Homology
open HolTest.CommonTest HolLight.Syntax

#eval ensureHomology

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- Theorem statements (homology.ml), as HOL Light prints them.             -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "homology.ml standard_simplex" standard_simplex
  "|- forall p. standard_simplex p =
      {x | (forall i. &0 <= x i /\\ x i <= &1) /\\
           (forall i. p < i ==> x i = &0) /\\ sum (0..p) x = &1}"
#eval thmCheck "homology.ml CLOSED_IN_STANDARD_SIMPLEX" CLOSED_IN_STANDARD_SIMPLEX
  "|- forall p. closed_in (product_topology (:num) (\\i. euclideanreal)) (standard_simplex p)"
#eval thmCheck "homology.ml SINGULAR_SIMPLEX_EMPTY" SINGULAR_SIMPLEX_EMPTY
  "|- forall p top f. topspace top = {} ==> ~singular_simplex (p,top) f"
#eval thmCheck "homology.ml SINGULAR_CHAIN_MONO" SINGULAR_CHAIN_MONO
  "|- forall p top s t c. t SUBSET s /\\ singular_chain (p,subtopology top t) c
      ==> singular_chain (p,subtopology top s) c"
#eval thmCheck "homology.ml SINGULAR_CHAIN_SUB" SINGULAR_CHAIN_SUB
  "|- forall p top c1 c2. singular_chain (p,top) c1 /\\ singular_chain (p,top) c2
      ==> singular_chain (p,top) (frag_sub c1 c2)"
#eval thmCheck "homology.ml CHAIN_BOUNDARY_NEG" CHAIN_BOUNDARY_NEG
  "|- forall p c. chain_boundary p (frag_neg c) = frag_neg (chain_boundary p c)"
#eval thmCheck "homology.ml MOD_SUBSET_CMUL" MOD_SUBSET_CMUL
  "|- forall p top a c1 c2. (c1 == c2) (mod_subset (p,top))
      ==> (frag_cmul a c1 == frag_cmul a c2) (mod_subset (p,top))"
#eval thmCheck "homology.ml SINGULAR_RELCYCLE_NEG" SINGULAR_RELCYCLE_NEG
  "|- forall p top s c. singular_relcycle (p,top,s) (frag_neg c) <=>
      singular_relcycle (p,top,s) c"
#eval thmCheck "homology.ml SINGULAR_RELBOUNDARY_0" SINGULAR_RELBOUNDARY_0
  "|- forall p top s. singular_relboundary (p,top,s) frag_0"
#eval thmCheck "homology.ml HOMOLOGOUS_REL_RESTRICT" HOMOLOGOUS_REL_RESTRICT
  "|- forall p top s. homologous_rel (p,top,s) = homologous_rel (p,top,topspace top INTER s)"
#eval thmCheck "homology.ml CHAIN_BOUNDARY_BOUNDARY" CHAIN_BOUNDARY_BOUNDARY
  "|- forall p top c. singular_chain (p,top) c
      ==> chain_boundary (p - 1) (chain_boundary p c) = frag_0"
#eval thmCheck "homology.ml CHAIN_MAP_SUB" CHAIN_MAP_SUB
  "|- forall p g c1 c2. chain_map p g (frag_sub c1 c2) =
      frag_sub (chain_map p g c1) (chain_map p g c2)"
#eval thmCheck "homology.ml oriented_simplex" oriented_simplex
  "|- forall p l. oriented_simplex p l =
      RESTRICTION (standard_simplex p) (\\x i. sum (0..p) (\\j. l j i * x j))"
#eval thmCheck "homology.ml SIMPLICIAL_VERTEX_ORIENTED_SIMPLEX"
  SIMPLICIAL_VERTEX_ORIENTED_SIMPLEX
  "|- forall i p l. simplicial_vertex i (oriented_simplex p l) = (if i <= p then l i else ARB)"
#eval thmCheck "homology.ml NATURALITY_SINGULAR_SUBDIVISION" NATURALITY_SINGULAR_SUBDIVISION
  "|- forall p s g c. singular_chain (p,s) c
      ==> singular_subdivision p (chain_map p g c) = chain_map p g (singular_subdivision p c)"
#eval thmCheck "homology.ml ABELIAN_CHAIN_GROUP" ABELIAN_CHAIN_GROUP
  "|- forall p top. abelian_group (chain_group (p,top))"
#eval thmCheck "homology.ml RIGHT_COSET_SINGULAR_RELBOUNDARY" RIGHT_COSET_SINGULAR_RELBOUNDARY
  "|- forall p top s. right_coset (relcycle_group (p,top,s)) (singular_relboundary (p,top,s)) =
      homologous_rel (p,top,s)"
#eval thmCheck "homology.ml GROUP_HOMOMORPHISM_HOM_BOUNDARY" GROUP_HOMOMORPHISM_HOM_BOUNDARY
  "|- forall p top s. group_homomorphism
      (relative_homology_group (p,top,s), homology_group (p - &1,subtopology top s))
      (hom_boundary p (top,s))"
#eval thmCheck "homology.ml HOM_INDUCED_RESTRICT" HOM_INDUCED_RESTRICT
  "|- forall p top s top' t. hom_induced p (top,s) (top',t) =
      hom_induced p (top,topspace top INTER s) (top',topspace top' INTER t)"
#eval thmCheck "homology.ml HOM_INDUCED_ID" HOM_INDUCED_ID
  "|- forall p top s c. c IN group_carrier (relative_homology_group (p,top,s))
      ==> hom_induced p (top,s) (top,s) (\\x. x) c = c"
#eval thmCheck "homology.ml HOMOLOGY_EXACTNESS_AXIOM_1" HOMOLOGY_EXACTNESS_AXIOM_1
  "|- forall p top s. group_exactness
      (homology_group (p,top), relative_homology_group (p,top,s),
       homology_group (p - &1,subtopology top s))
      (hom_induced p (top,{}) (top,s) (\\x. x),hom_boundary p (top,s))"
#eval thmCheck "homology.ml HOMOLOGY_DIMENSION_AXIOM" HOMOLOGY_DIMENSION_AXIOM
  "|- forall p top a. topspace top = {a} /\\ ~(p = &0) ==> trivial_group (homology_group (p,top))"
#eval thmCheck "homology.ml HOMOLOGY_HOMOTOPY_AXIOM" HOMOLOGY_HOMOTOPY_AXIOM
  "|- forall p top s top' t f g. homotopic_with (\\h. IMAGE h s SUBSET t) (top,top') f g
      ==> hom_induced p (top,s) (top',t) f = hom_induced p (top,s) (top',t) g"
#eval thmCheck "homology.ml HOMOLOGY_COEFFICIENTS" HOMOLOGY_COEFFICIENTS
  "|- forall top a. topspace top = {a} ==> homology_group (&0,top) isomorphic_group integer_group"
#eval thmCheck "homology.ml ZEROTH_HOMOLOGY_GROUP" ZEROTH_HOMOLOGY_GROUP
  "|- forall top. homology_group (&0,top) isomorphic_group
      free_abelian_group (path_components_of top)"
#eval thmCheck "homology.ml TRIVIAL_HOMOLOGY_GROUP_EMPTY" TRIVIAL_HOMOLOGY_GROUP_EMPTY
  "|- forall p top. topspace top = {} ==> trivial_group (homology_group (p,top))"
#eval thmCheck "homology.ml HOM_RELBOUNDARY_EMPTY" HOM_RELBOUNDARY_EMPTY
  "|- forall p top s. hom_relboundary p (top,s,{}) = hom_boundary p (top,s)"
#eval thmCheck "homology.ml HOMOLOGY_EXACTNESS_TRIPLE_2" HOMOLOGY_EXACTNESS_TRIPLE_2
  "|- forall p top s t. t SUBSET s ==> group_exactness
      (relative_homology_group (p,top,s), relative_homology_group (p - &1,subtopology top s,t),
       relative_homology_group (p - &1,top,t))
      (hom_relboundary p (top,s,t), hom_induced (p - &1) (subtopology top s,t) (top,t) (\\x. x))"
#eval thmCheck "homology.ml UN_REDUCED_HOMOLOGY_GROUP" UN_REDUCED_HOMOLOGY_GROUP
  "|- forall p top. ~(p = &0) ==> reduced_homology_group (p,top) = homology_group (p,top)"
#eval thmCheck "homology.ml TRIVIAL_REDUCED_HOMOLOGY_GROUP_CONTRACTIBLE_SPACE"
  TRIVIAL_REDUCED_HOMOLOGY_GROUP_CONTRACTIBLE_SPACE
  "|- forall p top. contractible_space top ==> trivial_group (reduced_homology_group (p,top))"
#eval thmCheck "homology.ml HOMOLOGY_EXACTNESS_REDUCED_2" HOMOLOGY_EXACTNESS_REDUCED_2
  "|- forall p top s. group_exactness
      (relative_homology_group (p,top,s), reduced_homology_group (p - &1,subtopology top s),
       reduced_homology_group (p - &1,top))
      (hom_boundary p (top,s), hom_induced (p - &1) (subtopology top s,{}) (top,{}) (\\x. x))"
#eval thmCheck "homology.ml ISOMORPHIC_GROUP_REDUCED_HOMOLOGY_BY_SING"
  ISOMORPHIC_GROUP_REDUCED_HOMOLOGY_BY_SING
  "|- forall p top a. a IN topspace top ==> reduced_homology_group (p,top) isomorphic_group
      relative_homology_group (p,top,{a})"
#eval thmCheck "homology.ml REDUCED_HOMOLOGY_GROUP_PAIR" REDUCED_HOMOLOGY_GROUP_PAIR
  "|- forall p top a b. t1_space top /\\ a IN topspace top /\\ b IN topspace top /\\ ~(a = b)
      ==> reduced_homology_group (p,subtopology top {a, b}) isomorphic_group
          homology_group (p,subtopology top {a})"
#eval thmCheck "homology.ml REDUCED_HOMOLOGY_GROUP_NSPHERE" REDUCED_HOMOLOGY_GROUP_NSPHERE
  "|- (forall n. reduced_homology_group (&n,nsphere n) isomorphic_group integer_group) /\\
      (forall n p. ~(p = &n) ==> trivial_group (reduced_homology_group (p,nsphere n)))"
#eval thmCheck "homology.ml TRIVIAL_REDUCED_HOMOLOGY_GROUP_NSPHERE"
  TRIVIAL_REDUCED_HOMOLOGY_GROUP_NSPHERE
  "|- forall p n. trivial_group (reduced_homology_group (p,nsphere n)) <=> ~(p = &n)"
#eval thmCheck "homology.ml NON_CONTRACTIBLE_SPACE_NSPHERE" NON_CONTRACTIBLE_SPACE_NSPHERE
  "|- forall n. ~contractible_space (nsphere n)"
#eval thmCheck "homology.ml BROUWER_DEGREE2_ID" BROUWER_DEGREE2_ID
  "|- forall p. brouwer_degree2 p (\\x. x) = &1"
#eval thmCheck "homology.ml BROUWER_DEGREE2_COMPOSE" BROUWER_DEGREE2_COMPOSE
  "|- forall p f g. continuous_map (nsphere p,nsphere p) f /\\
      continuous_map (nsphere p,nsphere p) g
      ==> brouwer_degree2 p (g o f) = brouwer_degree2 p g * brouwer_degree2 p f"
#eval thmCheck "homology.ml BROUWER_DEGREE2_CONST" BROUWER_DEGREE2_CONST
  "|- forall p a. brouwer_degree2 p (\\x. a) = &0"
#eval thmCheck "homology.ml BROUWER_DEGREE2_REFLECTION" BROUWER_DEGREE2_REFLECTION
  "|- forall p. brouwer_degree2 p (\\x i. if i = 1 then --x i else x i) = -- &1"
#eval thmCheck "homology.ml BORSUK_ODD_MAPPING_DEGREE_STEP" BORSUK_ODD_MAPPING_DEGREE_STEP
  "|- forall f n. continuous_map (nsphere n,nsphere n) f /\\
      (forall x. x IN topspace (nsphere n) ==> (f o (\\x i. --x i)) x = ((\\x i. --x i) o f) x) /\\
      IMAGE f (topspace (nsphere (n - 1))) SUBSET topspace (nsphere (n - 1))
      ==> (brouwer_degree2 n f == brouwer_degree2 (n - 1) f) (mod &2)"
#eval thmCheck "homology.ml INVARIANCE_OF_DIMENSION_EUCLIDEAN_SPACE"
  INVARIANCE_OF_DIMENSION_EUCLIDEAN_SPACE
  "|- forall m n. euclidean_space m homeomorphic_space euclidean_space n <=> m = n"
#eval thmCheck "homology.ml INVARIANCE_OF_DOMAIN_EUCLIDEAN_SPACE"
  INVARIANCE_OF_DOMAIN_EUCLIDEAN_SPACE
  "|- forall n u f. open_in (euclidean_space n) u /\\
      continuous_map (subtopology (euclidean_space n) u,euclidean_space n) f /\\
      (forall x y. x IN u /\\ y IN u /\\ f x = f y ==> x = y)
      ==> open_in (euclidean_space n) (IMAGE f u)"
