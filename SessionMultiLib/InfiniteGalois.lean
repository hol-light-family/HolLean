/- ---------------------------------------------------------------------- -/
/- Session wiring for Multivariate/infinite_galois.ml.                    -/
/- ---------------------------------------------------------------------- -/
/- File: SessionMultiLib/InfiniteGalois.lean

  The session half of the infinite_galois.ml translation: it supplies
  HolMultiLib.InfiniteGalois's dependencies and exports every theorem by name.
  Importing this module is `needs "Multivariate/infinite_galois.ml"`: its own `needs` are
  its imports, and each bundle is built by `initialize` when the module is
  loaded, in file order.
-/

import SessionLibrary.Galois
import SessionMultiLib.ProfiniteGroups
import HolMultiLib.InfiniteGalois

open HolCore HolCore.Kernel

namespace SessionMultiLib.InfiniteGalois

/- The theorem groups (names only; each group's names come from one file). -/

open SessionMultiLib.ProfiniteGroups in
def qprofinitegroups : HolMultiLib.InfiniteGalois.QProfiniteGroupsThms :=
  { CLOSED_IN_POINTWISE_STABILIZER, OPEN_IN_POINTWISE_TOPOLOGY_SUBGROUP,
    POINTWISE_TOPOLOGY_FINITE, POINTWISE_TOPOLOGY_NEIGHBOURHOOD_STABILIZER,
    profinite_group, PROFINITE_GROUP_CONTINUOUS_EPIMORPHISM,
    PROFINITE_GROUP_POINTWISE_TOPOLOGY_LOCAL, TOPOLOGICAL_GROUP_POINTWISE_TOPOLOGY }

open SessionLibrary.Galois in
def qgalois : HolMultiLib.InfiniteGalois.QGaloisThms :=
  { FINITE_GALOIS_GROUP, FINITE_GALOIS_SUBFIELDS_ELEMENT,
    FINITE_GALOIS_SUBFIELDS_FINITE, FINITE_GALOIS_SUBFIELDS_UPPER_BOUND,
    FINITE_GALOIS_SUBFIELDS_UPPER_BOUNDS, FIXED_FIELD_ANTIMONO,
    FIXED_FIELD_GALOIS_GROUP_INTERMEDIATE, FIXED_FIELD_GALOIS_SUBSET,
    FIXED_FIELD_SUBGROUP_GENERATED, FIXED_FIELD_UNION, GALOIS_CORRESPONDENCE_INDEX,
    GALOIS_CORRESPONDENCE_NORMAL, GALOIS_EXTENSION_FIXED_FIELD_FINITE_ORBITS,
    GALOIS_EXTENSION_NORMAL_SUBGROUP, GALOIS_GROUP_COMPOSITUM, GALOIS_GROUP_EQ_IMAGE,
    GALOIS_GROUP_FIXED_FIELD, GALOIS_GROUP_FIXES, GALOIS_GROUP_I,
    GALOIS_GROUP_INTERMEDIATE_SUBGROUP, GALOIS_GROUP_LOCAL, GALOIS_GROUP_ORBIT_FINITE,
    GALOIS_GROUP_PERMUTES, GALOIS_GROUP_RESTRICTION,
    GALOIS_GROUP_RESTRICTION_HOMOMORPHISM, GALOIS_GROUP_RESTRICTION_NORMAL,
    GALOIS_GROUP_RING_AUTOMORPHISM, GALOIS_GROUP_RING_HOMOMORPHISM,
    GALOIS_GROUP_SUBGROUP, GALOIS_IMP_ALGEBRAIC_EXTENSION, GALOIS_IMP_FIELD_EXTENSION,
    GALOIS_IMP_NORMAL_EXTENSION, IN_FINITE_GALOIS_SUBFIELDS, IN_FIXED_FIELD,
    IN_GALOIS_GROUP, IN_GALOIS_GROUP_INTERMEDIATE, SUBFIELD_OF_FIXED_FIELD,
    SUBGROUP_GENERATED_GALOIS_GROUP, SUBGROUP_OF_GALOIS_GROUP,
    SUBSET_GALOIS_GROUP_FIXED_FIELD }

open SessionLibrary.FieldTheory in
def qfieldtheory : HolMultiLib.InfiniteGalois.QFieldTheoryThms :=
  { algebraic_extension, ALGEBRAIC_IMP_FIELD_EXTENSION,
    CARRIER_SUBFIELD_GENERATED_SUBFIELD, CARRIER_SUBFIELD_OF, field_extension,
    FIELD_SUBFIELD_GENERATED, FINITE_EXTENSION_SUBFIELD_GENERATED,
    FINITE_EXTENSION_SUBFIELD_GENERATORS, FINITE_FINITE_FIELD_EXTENSION,
    NORMAL_IMP_ALGEBRAIC_EXTENSION, RING_CARRIER_SUBFIELD_GENERATED_SUBSET,
    RING_ENDOMORPHISM_POW_CARD, RING_POW_FIXPOINTS_BOUND, RING_POW_SUBFIELD_GENERATED,
    SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED, SUBFIELD_GENERATED_IDEMPOT_GEN,
    SUBFIELD_GENERATED_MINIMAL, SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC,
    SUBFIELD_GENERATED_SUBFIELD_GENERATED, SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET,
    SUBFIELD_OF_IMP_SUBSET, SUBFIELD_OF_MONOMORPHIC_IMAGE,
    SUBFIELD_OF_SUBFIELD_GENERATED, SUBFIELD_SUBFIELD_GENERATED }

open SessionMultiLib.Metric in
def qmetric : HolMultiLib.InfiniteGalois.QMetricThms :=
  { CLOSED_IN_DISCRETE_TOPOLOGY, CLOSURE_OF_EQ, CLOSURE_OF_POINTWISE_TOPOLOGY }

open SessionLibrary.GroupTheory in
def qgrouptheory : HolMultiLib.InfiniteGalois.QGroupTheoryThms :=
  { CARD_EQ_GROUP_COSETS_PREIMAGE, FINITE_GROUP_COSETS, NORMAL_SUBGROUP_GROUP_KERNEL,
    SUBGROUP_OF_HOMOMORPHIC_IMAGE, SUBGROUP_SUBGROUP_GENERATED }

open SessionLibrary.RingTheory in
def qringtheory : HolMultiLib.InfiniteGalois.QRingTheoryThms :=
  { FIELD_HOMOMORPHISM_IMP_MONOMORPHISM, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_NONTRIVIAL,
    FINITE_FIELD_CARD_GE_2, RING_1, ring_automorphism, ring_endomorphism,
    ring_homomorphism, RING_HOMOMORPHISM_EQ, RING_HOMOMORPHISM_IN_CARRIER,
    RING_ISOMORPHISM, ring_monomorphism, RING_MONOMORPHISM_IMP_HOMOMORPHISM,
    RING_MONOMORPHISM_INJECTIVE_EQ, RING_POW, RING_POW_ONE }

open SessionLibrary.Card in
def qcard : HolMultiLib.InfiniteGalois.QCardThms :=
  { CARD_EQ_CARD_IMP }

open SessionLibrary.Permutations in
def qpermutations : HolMultiLib.InfiniteGalois.QPermutationsThms :=
  { PERMUTES_ALT }

open Session in
def qsession : HolMultiLib.InfiniteGalois.QSessionThms :=
  { CARD_IMAGE_INJ, CARD_SUBSET, CARD_SUBSET_EQ, EXP_1, IMAGE_I, LE_ANTISYM }

def deps : HolMultiLib.InfiniteGalois.InfiniteGaloisDeps where
  pg := SessionMultiLib.ProfiniteGroups.deps
  qprofinitegroups := qprofinitegroups
  qgalois := qgalois
  qfieldtheory := qfieldtheory
  qmetric := qmetric
  qgrouptheory := qgrouptheory
  qringtheory := qringtheory
  qcard := qcard
  qpermutations := qpermutations
  qsession := qsession

private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in infinite_galois.ml order. -/

initialize BIGA : HolMultiLib.InfiniteGalois.IGA ←
  ioB "setupIGA" (HolMultiLib.InfiniteGalois.setupIGA deps).run

-- IGA (infinite_galois.ml 96-413)
def TOPOLOGICAL_GROUP_GALOIS_GROUP : thm := BIGA.TOPOLOGICAL_GROUP_GALOIS_GROUP
def PROFINITE_GROUP_GALOIS_GROUP : thm := BIGA.PROFINITE_GROUP_GALOIS_GROUP
def OPEN_IN_GALOIS_GROUP_SUBGROUP : thm := BIGA.OPEN_IN_GALOIS_GROUP_SUBGROUP
def CLOSED_IN_GALOIS_GROUP_INTERMEDIATE : thm := BIGA.CLOSED_IN_GALOIS_GROUP_INTERMEDIATE
def POINTWISE_TOPOLOGY_GALOIS_GROUP_FINITE : thm := BIGA.POINTWISE_TOPOLOGY_GALOIS_GROUP_FINITE
def GALOIS_GROUP_NEIGHBOURHOOD_BASE : thm := BIGA.GALOIS_GROUP_NEIGHBOURHOOD_BASE
def CLOSURE_OF_GALOIS_GROUP_SUBGROUP_GALOIS : thm := BIGA.CLOSURE_OF_GALOIS_GROUP_SUBGROUP_GALOIS
def ARTIN_FIXED_FIELD_FINITE_ORBITS : thm := BIGA.ARTIN_FIXED_FIELD_FINITE_ORBITS
def CLOSURE_OF_GALOIS_GROUP_SUBGROUP : thm := BIGA.CLOSURE_OF_GALOIS_GROUP_SUBGROUP
def CLOSED_IN_GALOIS_GROUP_SUBGROUP : thm := BIGA.CLOSED_IN_GALOIS_GROUP_SUBGROUP
def INFINITE_GALOIS_CORRESPONDENCE : thm := BIGA.INFINITE_GALOIS_CORRESPONDENCE

initialize BIGB : HolMultiLib.InfiniteGalois.IGB ←
  ioB "setupIGB" (HolMultiLib.InfiniteGalois.setupIGB deps BIGA).run

-- IGB (infinite_galois.ml 415-611)
def OPEN_IN_GALOIS_GROUP_INTERMEDIATE : thm := BIGB.OPEN_IN_GALOIS_GROUP_INTERMEDIATE
def INFINITE_GALOIS_CORRESPONDENCE_NORMAL : thm := BIGB.INFINITE_GALOIS_CORRESPONDENCE_NORMAL
def GALOIS_GROUP_INTER_CLOSURE : thm := BIGB.GALOIS_GROUP_INTER_CLOSURE
def FIXED_FIELD_INTER_CLOSED : thm := BIGB.FIXED_FIELD_INTER_CLOSED

initialize BIGC : HolMultiLib.InfiniteGalois.IGC ←
  ioB "setupIGC" (HolMultiLib.InfiniteGalois.setupIGC deps BIGA BIGB).run

-- IGC (infinite_galois.ml 613-822)
def CONTINUOUS_MAP_GALOIS_GROUP_RESTRICTION : thm := BIGC.CONTINUOUS_MAP_GALOIS_GROUP_RESTRICTION
def GALOIS_GROUP_RESTRICTION_QUOTIENT_MAP : thm := BIGC.GALOIS_GROUP_RESTRICTION_QUOTIENT_MAP
def CONTINUOUS_MAP_GALOIS_GROUP_RESTRICTION_FINITE : thm := BIGC.CONTINUOUS_MAP_GALOIS_GROUP_RESTRICTION_FINITE
def GALOIS_GROUP_RESTRICTION_FINITE_GALOIS : thm := BIGC.GALOIS_GROUP_RESTRICTION_FINITE_GALOIS
def INFINITE_GALOIS_CORRESPONDENCE_INDEX : thm := BIGC.INFINITE_GALOIS_CORRESPONDENCE_INDEX

initialize BIGD : HolMultiLib.InfiniteGalois.IGD ←
  ioB "setupIGD" (HolMultiLib.InfiniteGalois.setupIGD deps BIGA BIGC).run

-- IGD (infinite_galois.ml 824-926)
def GALOIS_GROUP_COMPATIBLE_RESTRICTIONS : thm := BIGD.GALOIS_GROUP_COMPATIBLE_RESTRICTIONS

initialize BIGE : HolMultiLib.InfiniteGalois.IGE ←
  ioB "setupIGE" (HolMultiLib.InfiniteGalois.setupIGE deps BIGA BIGC).run

-- IGE (infinite_galois.ml 928-1264)
def GALOIS_GROUP_INVERSE_LIMIT : thm := BIGE.GALOIS_GROUP_INVERSE_LIMIT

initialize BIGF : HolMultiLib.InfiniteGalois.IGF ←
  ioB "setupIGF" (HolMultiLib.InfiniteGalois.setupIGF deps BIGA).run

-- IGF (infinite_galois.ml 1278-1433)
def GALOIS_GROUP_FROBENIUS_DENSE : thm := BIGF.GALOIS_GROUP_FROBENIUS_DENSE

-- @@WIRING-END

/-- `needs "Multivariate/infinite_galois.ml"`: importing this module has built every
    bundle; this is a no-op kept for symmetry with the other wiring files. -/
def ensureInfiniteGalois : IO Unit := pure ()

end SessionMultiLib.InfiniteGalois
