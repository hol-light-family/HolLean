/- ---------------------------------------------------------------------- -/
/- Session wiring for Multivariate/geom.ml.                               -/
/- ---------------------------------------------------------------------- -/
/- File: SessionMultiLib/Geom.lean

  The session half of the geom.ml translation: it supplies
  HolMultiLib.Geom's dependencies and exports every theorem by name.
  Importing this module is `needs "Multivariate/geom.ml"`: its own `needs` are
  its imports, and each bundle is built by `initialize` when the module is
  loaded, in file order.
-/

import SessionMultiLib.RealAnalysis
import HolMultiLib.Geom

open HolCore HolCore.Kernel

namespace SessionMultiLib.Geom

/- The theorem groups (names only; each group's names come from one file). -/

open SessionMultiLib.Vectors in
def qvectors : HolMultiLib.Geom.QVectorsThms :=
  { BETWEEN_REFL_EQ, COLLINEAR_3, DIST_EQ, DIST_TRIANGLE_EQ, DOT_3, FORALL_VECTOR_3,
    NORM_CAUCHY_SCHWARZ_ABS_EQ, NORM_CAUCHY_SCHWARZ_DIV, NORM_CAUCHY_SCHWARZ_EQ,
    NORM_CAUCHY_SCHWARZ_EQUAL, NORM_CROSS_MULTIPLY, NORM_TRIANGLE_EQ,
    PRESERVES_NORM_PRESERVES_DOT }

open SessionMultiLib.Topology in
def qtopology : HolMultiLib.Geom.QTopologyThms :=
  { CONTINUOUS_TRANSFORM_AT, SETDIST_CLOSEST_POINT }

open SessionMultiLib.Determinants in
def qdeterminants : HolMultiLib.Geom.QDeterminantsThms :=
  { ORTHOGONALITY_PRESERVING_EQ_SIMILARITY }

open Session in
def qsession : HolMultiLib.Geom.QSessionThms :=
  { REAL_POW_EQ }

open SessionMultiLib.Convex in
def qconvex : HolMultiLib.Geom.QConvexThms :=
  { AFFINE_HULL_2, CLOSEST_POINT_AFFINE_ORTHOGONAL }

open SessionMultiLib.Measure in
def qmeasure : HolMultiLib.Geom.QMeasureThms :=
  { MEASURE_TRIANGLE }

def deps : HolMultiLib.Geom.GeomDeps where
  ra := SessionMultiLib.RealAnalysis.deps
  prioritize_vector := SessionMultiLib.Vectors.prioritize_vector
  invariant_under_linear := SessionMultiLib.Vectors.invariant_under_linear
  rza := SessionMultiLib.RealAnalysis.BRZA
  rzb := SessionMultiLib.RealAnalysis.BRZB
  rzc := SessionMultiLib.RealAnalysis.BRZC
  rzd := SessionMultiLib.RealAnalysis.BRZD
  rze := SessionMultiLib.RealAnalysis.BRZE
  rzf := SessionMultiLib.RealAnalysis.BRZF
  rzg := SessionMultiLib.RealAnalysis.BRZG
  rzh := SessionMultiLib.RealAnalysis.BRZH
  rzi := SessionMultiLib.RealAnalysis.BRZI
  rzj := SessionMultiLib.RealAnalysis.BRZJ
  rzk := SessionMultiLib.RealAnalysis.BRZK
  rzl := SessionMultiLib.RealAnalysis.BRZL
  rzm := SessionMultiLib.RealAnalysis.BRZM
  rzn := SessionMultiLib.RealAnalysis.BRZN
  rzo := SessionMultiLib.RealAnalysis.BRZO
  rzp := SessionMultiLib.RealAnalysis.BRZP
  rzq := SessionMultiLib.RealAnalysis.BRZQ
  rzr := SessionMultiLib.RealAnalysis.BRZR
  rzs := SessionMultiLib.RealAnalysis.BRZS
  rzt := SessionMultiLib.RealAnalysis.BRZT
  rzu := SessionMultiLib.RealAnalysis.BRZU
  rzv := SessionMultiLib.RealAnalysis.BRZV
  rzw := SessionMultiLib.RealAnalysis.BRZW
  rzx := SessionMultiLib.RealAnalysis.BRZX
  rzy := SessionMultiLib.RealAnalysis.BRZY
  rzz := SessionMultiLib.RealAnalysis.BRZZ
  rzaa := SessionMultiLib.RealAnalysis.BRZAA
  rzab := SessionMultiLib.RealAnalysis.BRZAB
  rzac := SessionMultiLib.RealAnalysis.BRZAC
  rzad := SessionMultiLib.RealAnalysis.BRZAD
  rzae := SessionMultiLib.RealAnalysis.BRZAE
  rzaf := SessionMultiLib.RealAnalysis.BRZAF
  rzag := SessionMultiLib.RealAnalysis.BRZAG
  rzah := SessionMultiLib.RealAnalysis.BRZAH
  rzai := SessionMultiLib.RealAnalysis.BRZAI
  rzaj := SessionMultiLib.RealAnalysis.BRZAJ
  rzak := SessionMultiLib.RealAnalysis.BRZAK
  rzal := SessionMultiLib.RealAnalysis.BRZAL
  rzam := SessionMultiLib.RealAnalysis.BRZAM
  rzan := SessionMultiLib.RealAnalysis.BRZAN
  rzao := SessionMultiLib.RealAnalysis.BRZAO
  rzap := SessionMultiLib.RealAnalysis.BRZAP
  rzaq := SessionMultiLib.RealAnalysis.BRZAQ
  rzar := SessionMultiLib.RealAnalysis.BRZAR
  rzas := SessionMultiLib.RealAnalysis.BRZAS
  rzat := SessionMultiLib.RealAnalysis.BRZAT
  rzau := SessionMultiLib.RealAnalysis.BRZAU
  rzav := SessionMultiLib.RealAnalysis.BRZAV
  rzaw := SessionMultiLib.RealAnalysis.BRZAW
  rzax := SessionMultiLib.RealAnalysis.BRZAX
  rzay := SessionMultiLib.RealAnalysis.BRZAY
  rzaz := SessionMultiLib.RealAnalysis.BRZAZ
  rzba := SessionMultiLib.RealAnalysis.BRZBA
  rzbb := SessionMultiLib.RealAnalysis.BRZBB
  rzbc := SessionMultiLib.RealAnalysis.BRZBC
  rzbd := SessionMultiLib.RealAnalysis.BRZBD
  rzbe := SessionMultiLib.RealAnalysis.BRZBE
  rzbf := SessionMultiLib.RealAnalysis.BRZBF
  rzbg := SessionMultiLib.RealAnalysis.BRZBG
  rzbh := SessionMultiLib.RealAnalysis.BRZBH
  rzbi := SessionMultiLib.RealAnalysis.BRZBI
  rzbj := SessionMultiLib.RealAnalysis.BRZBJ
  rzbk := SessionMultiLib.RealAnalysis.BRZBK
  rzbl := SessionMultiLib.RealAnalysis.BRZBL
  rzbm := SessionMultiLib.RealAnalysis.BRZBM
  rzbn := SessionMultiLib.RealAnalysis.BRZBN
  rzbo := SessionMultiLib.RealAnalysis.BRZBO
  rzbp := SessionMultiLib.RealAnalysis.BRZBP
  rzbq := SessionMultiLib.RealAnalysis.BRZBQ
  rzbr := SessionMultiLib.RealAnalysis.BRZBR
  rzbs := SessionMultiLib.RealAnalysis.BRZBS
  rzbt := SessionMultiLib.RealAnalysis.BRZBT
  rzbu := SessionMultiLib.RealAnalysis.BRZBU
  rzbv := SessionMultiLib.RealAnalysis.BRZBV
  rzbw := SessionMultiLib.RealAnalysis.BRZBW
  rzbx := SessionMultiLib.RealAnalysis.BRZBX
  rzby := SessionMultiLib.RealAnalysis.BRZBY
  rzbz := SessionMultiLib.RealAnalysis.BRZBZ
  rzca := SessionMultiLib.RealAnalysis.BRZCA
  rzcb := SessionMultiLib.RealAnalysis.BRZCB
  rzcc := SessionMultiLib.RealAnalysis.BRZCC
  rzcd := SessionMultiLib.RealAnalysis.BRZCD
  qvectors := qvectors
  qtopology := qtopology
  qdeterminants := qdeterminants
  qsession := qsession
  qconvex := qconvex
  qmeasure := qmeasure

private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in geom.ml order. -/

initialize BGEA : HolMultiLib.Geom.GEA ←
  ioB "setupGEA" (HolMultiLib.Geom.setupGEA deps).run

-- GEA (geom.ml 1-214)
def PYTHAGORAS : thm := BGEA.PYTHAGORAS
def vector_angle : thm := BGEA.vector_angle
def VECTOR_ANGLE_LINEAR_IMAGE_EQ : thm := BGEA.VECTOR_ANGLE_LINEAR_IMAGE_EQ
def VECTOR_ANGLE_ORTHOGONAL_TRANSFORMATION : thm := BGEA.VECTOR_ANGLE_ORTHOGONAL_TRANSFORMATION
def VECTOR_ANGLE_REFL : thm := BGEA.VECTOR_ANGLE_REFL
def VECTOR_ANGLE_SYM : thm := BGEA.VECTOR_ANGLE_SYM
def VECTOR_ANGLE_LMUL : thm := BGEA.VECTOR_ANGLE_LMUL
def VECTOR_ANGLE_RMUL : thm := BGEA.VECTOR_ANGLE_RMUL
def VECTOR_ANGLE_LNEG : thm := BGEA.VECTOR_ANGLE_LNEG
def VECTOR_ANGLE_RNEG : thm := BGEA.VECTOR_ANGLE_RNEG
def VECTOR_ANGLE_NEG2 : thm := BGEA.VECTOR_ANGLE_NEG2
def SIN_VECTOR_ANGLE_LMUL : thm := BGEA.SIN_VECTOR_ANGLE_LMUL
def SIN_VECTOR_ANGLE_RMUL : thm := BGEA.SIN_VECTOR_ANGLE_RMUL
def VECTOR_ANGLE : thm := BGEA.VECTOR_ANGLE
def VECTOR_ANGLE_RANGE : thm := BGEA.VECTOR_ANGLE_RANGE
def ORTHOGONAL_VECTOR_ANGLE : thm := BGEA.ORTHOGONAL_VECTOR_ANGLE
def VECTOR_ANGLE_EQ_0 : thm := BGEA.VECTOR_ANGLE_EQ_0
def VECTOR_ANGLE_EQ_PI : thm := BGEA.VECTOR_ANGLE_EQ_PI
def VECTOR_ANGLE_EQ_0_DIST : thm := BGEA.VECTOR_ANGLE_EQ_0_DIST
def VECTOR_ANGLE_EQ_PI_DIST : thm := BGEA.VECTOR_ANGLE_EQ_PI_DIST
def SIN_VECTOR_ANGLE_POS : thm := BGEA.SIN_VECTOR_ANGLE_POS
def SIN_VECTOR_ANGLE_EQ_0 : thm := BGEA.SIN_VECTOR_ANGLE_EQ_0
def ASN_SIN_VECTOR_ANGLE : thm := BGEA.ASN_SIN_VECTOR_ANGLE
def SIN_VECTOR_ANGLE_EQ : thm := BGEA.SIN_VECTOR_ANGLE_EQ

initialize BGEB : HolMultiLib.Geom.GEB ←
  ioB "setupGEB" (HolMultiLib.Geom.setupGEB deps BGEA).run

-- GEB (geom.ml 215-501)
def CONTINUOUS_WITHIN_CX_VECTOR_ANGLE_COMPOSE : thm := BGEB.CONTINUOUS_WITHIN_CX_VECTOR_ANGLE_COMPOSE
def CONTINUOUS_AT_CX_VECTOR_ANGLE : thm := BGEB.CONTINUOUS_AT_CX_VECTOR_ANGLE
def CONTINUOUS_WITHIN_CX_VECTOR_ANGLE : thm := BGEB.CONTINUOUS_WITHIN_CX_VECTOR_ANGLE
def REAL_CONTINUOUS_AT_VECTOR_ANGLE : thm := BGEB.REAL_CONTINUOUS_AT_VECTOR_ANGLE
def REAL_CONTINUOUS_WITHIN_VECTOR_ANGLE : thm := BGEB.REAL_CONTINUOUS_WITHIN_VECTOR_ANGLE
def CONTINUOUS_ON_CX_VECTOR_ANGLE : thm := BGEB.CONTINUOUS_ON_CX_VECTOR_ANGLE
def VECTOR_ANGLE_EQ : thm := BGEB.VECTOR_ANGLE_EQ
def COS_VECTOR_ANGLE_EQ : thm := BGEB.COS_VECTOR_ANGLE_EQ
def COLLINEAR_VECTOR_ANGLE : thm := BGEB.COLLINEAR_VECTOR_ANGLE
def COLLINEAR_SIN_VECTOR_ANGLE : thm := BGEB.COLLINEAR_SIN_VECTOR_ANGLE
def COLLINEAR_SIN_VECTOR_ANGLE_IMP : thm := BGEB.COLLINEAR_SIN_VECTOR_ANGLE_IMP
def VECTOR_ANGLE_EQ_0_RIGHT : thm := BGEB.VECTOR_ANGLE_EQ_0_RIGHT
def VECTOR_ANGLE_EQ_0_LEFT : thm := BGEB.VECTOR_ANGLE_EQ_0_LEFT
def VECTOR_ANGLE_EQ_PI_RIGHT : thm := BGEB.VECTOR_ANGLE_EQ_PI_RIGHT
def VECTOR_ANGLE_EQ_PI_LEFT : thm := BGEB.VECTOR_ANGLE_EQ_PI_LEFT
def COS_VECTOR_ANGLE : thm := BGEB.COS_VECTOR_ANGLE
def SIN_VECTOR_ANGLE : thm := BGEB.SIN_VECTOR_ANGLE
def SIN_SQUARED_VECTOR_ANGLE : thm := BGEB.SIN_SQUARED_VECTOR_ANGLE
def VECTOR_ANGLE_COMPLEX_LMUL : thm := BGEB.VECTOR_ANGLE_COMPLEX_LMUL
def VECTOR_ANGLE_1 : thm := BGEB.VECTOR_ANGLE_1
def ARG_EQ_VECTOR_ANGLE_1 : thm := BGEB.ARG_EQ_VECTOR_ANGLE_1
def VECTOR_ANGLE_ARG : thm := BGEB.VECTOR_ANGLE_ARG
def VECTOR_ANGLE_PRESERVING_EQ_SIMILARITY : thm := BGEB.VECTOR_ANGLE_PRESERVING_EQ_SIMILARITY
def VECTOR_ANGLE_PRESERVING_EQ_SIMILARITY_ALT : thm := BGEB.VECTOR_ANGLE_PRESERVING_EQ_SIMILARITY_ALT

initialize BGEC : HolMultiLib.Geom.GEC ←
  ioB "setupGEC" (HolMultiLib.Geom.setupGEC deps BGEA BGEB).run

-- GEC (geom.ml 502-751)
def angle : thm := BGEC.angle
def ANGLE_LINEAR_IMAGE_EQ : thm := BGEC.ANGLE_LINEAR_IMAGE_EQ
def ANGLE_TRANSLATION_EQ : thm := BGEC.ANGLE_TRANSLATION_EQ
def VECTOR_ANGLE_ANGLE : thm := BGEC.VECTOR_ANGLE_ANGLE
def ANGLE_EQ_PI_DIST : thm := BGEC.ANGLE_EQ_PI_DIST
def SIN_ANGLE_POS : thm := BGEC.SIN_ANGLE_POS
def ANGLE : thm := BGEC.ANGLE
def ANGLE_REFL : thm := BGEC.ANGLE_REFL
def ANGLE_REFL_MID : thm := BGEC.ANGLE_REFL_MID
def ANGLE_SYM : thm := BGEC.ANGLE_SYM
def ANGLE_RANGE : thm := BGEC.ANGLE_RANGE
def COS_ANGLE_EQ : thm := BGEC.COS_ANGLE_EQ
def ANGLE_EQ : thm := BGEC.ANGLE_EQ
def SIN_ANGLE_EQ_0 : thm := BGEC.SIN_ANGLE_EQ_0
def SIN_ANGLE_EQ : thm := BGEC.SIN_ANGLE_EQ
def COLLINEAR_ANGLE : thm := BGEC.COLLINEAR_ANGLE
def COLLINEAR_SIN_ANGLE : thm := BGEC.COLLINEAR_SIN_ANGLE
def COLLINEAR_SIN_ANGLE_IMP : thm := BGEC.COLLINEAR_SIN_ANGLE_IMP
def ANGLE_EQ_0_RIGHT : thm := BGEC.ANGLE_EQ_0_RIGHT
def ANGLE_EQ_0_LEFT : thm := BGEC.ANGLE_EQ_0_LEFT
def ANGLE_EQ_PI_RIGHT : thm := BGEC.ANGLE_EQ_PI_RIGHT
def ANGLE_EQ_PI_LEFT : thm := BGEC.ANGLE_EQ_PI_LEFT
def COS_ANGLE : thm := BGEC.COS_ANGLE
def SIN_ANGLE : thm := BGEC.SIN_ANGLE
def SIN_SQUARED_ANGLE : thm := BGEC.SIN_SQUARED_ANGLE
def COS_ADJACENT_HYPOTENUSE : thm := BGEC.COS_ADJACENT_HYPOTENUSE
def COS_ADJACENT_OVER_HYPOTENUSE : thm := BGEC.COS_ADJACENT_OVER_HYPOTENUSE
def SIN_OPPOSITE_HYPOTENUSE : thm := BGEC.SIN_OPPOSITE_HYPOTENUSE
def SIN_OPPOSITE_OVER_HYPOTENUSE : thm := BGEC.SIN_OPPOSITE_OVER_HYPOTENUSE
def TAN_OPPOSITE_ADJACENT : thm := BGEC.TAN_OPPOSITE_ADJACENT
def TAN_OPPOSITE_OVER_ADJACENT : thm := BGEC.TAN_OPPOSITE_OVER_ADJACENT
def LAW_OF_COSINES : thm := BGEC.LAW_OF_COSINES
def LAW_OF_SINES : thm := BGEC.LAW_OF_SINES

initialize BGED : HolMultiLib.Geom.GED ←
  ioB "setupGED" (HolMultiLib.Geom.setupGED deps BGEA BGEC).run

-- GED (geom.ml 757-961)
def TRIANGLE_ANGLE_SUM_LEMMA : thm := BGED.TRIANGLE_ANGLE_SUM_LEMMA
def COS_MINUS1_LEMMA : thm := BGED.COS_MINUS1_LEMMA
def TRIANGLE_ANGLE_SUM : thm := BGED.TRIANGLE_ANGLE_SUM
def ANGLE_EQ_PI_OTHERS : thm := BGED.ANGLE_EQ_PI_OTHERS
def ANGLE_EQ_0_DIST : thm := BGED.ANGLE_EQ_0_DIST
def ANGLE_EQ_0_DIST_ABS : thm := BGED.ANGLE_EQ_0_DIST_ABS
def CONGRUENT_TRIANGLES_SSS : thm := BGED.CONGRUENT_TRIANGLES_SSS
def CONGRUENT_TRIANGLES_SAS : thm := BGED.CONGRUENT_TRIANGLES_SAS
def CONGRUENT_TRIANGLES_AAS : thm := BGED.CONGRUENT_TRIANGLES_AAS
def CONGRUENT_TRIANGLES_ASA : thm := BGED.CONGRUENT_TRIANGLES_ASA

initialize BGEE : HolMultiLib.Geom.GEE ←
  ioB "setupGEE" (HolMultiLib.Geom.setupGEE deps BGEA BGEB BGEC BGED).run

-- GEE (geom.ml 962-1249)
def CONGRUENT_TRIANGLES_SSS_FULL : thm := BGEE.CONGRUENT_TRIANGLES_SSS_FULL
def CONGRUENT_TRIANGLES_SAS_FULL : thm := BGEE.CONGRUENT_TRIANGLES_SAS_FULL
def CONGRUENT_TRIANGLES_AAS_FULL : thm := BGEE.CONGRUENT_TRIANGLES_AAS_FULL
def CONGRUENT_TRIANGLES_ASA_FULL : thm := BGEE.CONGRUENT_TRIANGLES_ASA_FULL
def ANGLE_BETWEEN : thm := BGEE.ANGLE_BETWEEN
def BETWEEN_ANGLE : thm := BGEE.BETWEEN_ANGLE
def ANGLES_ALONG_LINE : thm := BGEE.ANGLES_ALONG_LINE
def ANGLES_ADD_BETWEEN : thm := BGEE.ANGLES_ADD_BETWEEN
def SETDIST_POINT_LINE : thm := BGEE.SETDIST_POINT_LINE
def AREA_TRIANGLE_SIN : thm := BGEE.AREA_TRIANGLE_SIN
def ANGLE_TRIANGLE_LAW : thm := BGEE.ANGLE_TRIANGLE_LAW
def VECTOR_ANGLE_TRIANGLE_LAW : thm := BGEE.VECTOR_ANGLE_TRIANGLE_LAW

-- @@WIRING-END

/-- `needs "Multivariate/geom.ml"`: importing this module has built every
    bundle; this is a no-op kept for symmetry with the other wiring files. -/
def ensureGeom : IO Unit := pure ()

end SessionMultiLib.Geom
