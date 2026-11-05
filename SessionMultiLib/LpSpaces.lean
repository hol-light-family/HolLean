/- ---------------------------------------------------------------------- -/
/- Session wiring for Multivariate/lpspaces.ml.                           -/
/- ---------------------------------------------------------------------- -/
/- File: SessionMultiLib/LpSpaces.lean

  The session half of the lpspaces.ml translation: it supplies
  HolMultiLib.LpSpaces's dependencies and exports every theorem by name.
  Importing this module is `needs "Multivariate/lpspaces.ml"`: its own `needs` are
  its imports, and each bundle is built by `initialize` when the module is
  loaded, in file order.
-/

import SessionMultiLib.RealAnalysis
import HolMultiLib.LpSpaces

open HolCore HolCore.Kernel

namespace SessionMultiLib.LpSpaces

/- The theorem groups (names only; each group's names come from one file). -/

open SessionMultiLib.Measure in
def qmeasure : HolMultiLib.LpSpaces.QMeasureThms :=
  { ABSOLUTELY_INTEGRABLE_MEASURABLE,
    ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET, INTEGRABLE_ON_CONST,
    INTEGRAL_CONST_GEN, INTEGRAL_DROP_LE_MEASURABLE, MEASURABLE_ON_LIFT_MUL,
    MEASURABLE_ON_VSUM }

open SessionMultiLib.Topology in
def qtopology : HolMultiLib.LpSpaces.QTopologyThms :=
  { SERIES_LIFT_ABSCONV_IMP_CONV }

def deps : HolMultiLib.LpSpaces.LpSpacesDeps where
  ra := SessionMultiLib.RealAnalysis.deps
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
  qmeasure := qmeasure
  qtopology := qtopology

private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in lpspaces.ml order. -/

initialize BLSA : HolMultiLib.LpSpaces.LSA ←
  ioB "setupLSA" (HolMultiLib.LpSpaces.setupLSA deps).run

-- LSA (lpspaces.ml 1-297)
def lspace : thm := BLSA.lspace
def LSPACE_ALT : thm := BLSA.LSPACE_ALT
def LSPACE_ZERO : thm := BLSA.LSPACE_ZERO
def LSPACE_CONST : thm := BLSA.LSPACE_CONST
def LSPACE_0 : thm := BLSA.LSPACE_0
def LSPACE_CMUL : thm := BLSA.LSPACE_CMUL
def LSPACE_NEG : thm := BLSA.LSPACE_NEG
def LSPACE_ADD : thm := BLSA.LSPACE_ADD
def LSPACE_SUB : thm := BLSA.LSPACE_SUB
def LSPACE_IMP_INTEGRABLE : thm := BLSA.LSPACE_IMP_INTEGRABLE
def LSPACE_NORM : thm := BLSA.LSPACE_NORM
def LSPACE_VSUM : thm := BLSA.LSPACE_VSUM
def LSPACE_MAX : thm := BLSA.LSPACE_MAX
def LSPACE_MIN : thm := BLSA.LSPACE_MIN
def LSPACE_BOUNDED_MEASURABLE : thm := BLSA.LSPACE_BOUNDED_MEASURABLE
def LSPACE_BOUNDED_MEASURABLE_SIMPLE : thm := BLSA.LSPACE_BOUNDED_MEASURABLE_SIMPLE
def LSPACE_INTEGRABLE_PRODUCT : thm := BLSA.LSPACE_INTEGRABLE_PRODUCT
def LSPACE_1 : thm := BLSA.LSPACE_1
def LSPACE_MONO : thm := BLSA.LSPACE_MONO
def LSPACE_INCLUSION : thm := BLSA.LSPACE_INCLUSION
def LSPACE_SUBSET : thm := BLSA.LSPACE_SUBSET

initialize BLSB : HolMultiLib.LpSpaces.LSB ←
  ioB "setupLSB" (HolMultiLib.LpSpaces.setupLSB deps BLSA).run

-- LSB (lpspaces.ml 298-458)
def lnorm : thm := BLSB.lnorm
def LNORM_0 : thm := BLSB.LNORM_0
def LNORM_CONST : thm := BLSB.LNORM_CONST
def LNORM_MONO : thm := BLSB.LNORM_MONO
def LNORM_NEG : thm := BLSB.LNORM_NEG
def LNORM_MUL : thm := BLSB.LNORM_MUL
def LNORM_EQ_0 : thm := BLSB.LNORM_EQ_0
def LNORM_POS_LE : thm := BLSB.LNORM_POS_LE
def LNORM_NORM : thm := BLSB.LNORM_NORM
def LNORM_RPOW : thm := BLSB.LNORM_RPOW
def INTEGRAL_LNORM_RPOW : thm := BLSB.INTEGRAL_LNORM_RPOW
def HOELDER_INEQUALITY : thm := BLSB.HOELDER_INEQUALITY
def HOELDER_INEQUALITY_FULL : thm := BLSB.HOELDER_INEQUALITY_FULL

initialize BLSC : HolMultiLib.LpSpaces.LSC ←
  ioB "setupLSC" (HolMultiLib.LpSpaces.setupLSC deps BLSA BLSB).run

-- LSC (lpspaces.ml 459-620)
def LNORM_TRIANGLE : thm := BLSC.LNORM_TRIANGLE
def VSUM_LNORM : thm := BLSC.VSUM_LNORM
def HOELDER_BOUND : thm := BLSC.HOELDER_BOUND

initialize BLSD : HolMultiLib.LpSpaces.LSD ←
  ioB "setupLSD" (HolMultiLib.LpSpaces.setupLSD deps BLSA BLSB).run

-- LSD (lpspaces.ml 621-878)
def lproduct : thm := BLSD.lproduct
def LPRODUCT_SYM : thm := BLSD.LPRODUCT_SYM
def CXDROP_LINEAR : thm := BLSD.CXDROP_LINEAR
def CX_DROP_INTEGRAL : thm := BLSD.CX_DROP_INTEGRAL
def LPRODUCT_SELF : thm := BLSD.LPRODUCT_SELF
def LPRODUCT_SELF_LNORM : thm := BLSD.LPRODUCT_SELF_LNORM
def LPRODUCT_CAUCHY_SCHWARZ : thm := BLSD.LPRODUCT_CAUCHY_SCHWARZ
def LPRODUCT_RMUL : thm := BLSD.LPRODUCT_RMUL
def LPRODUCT_RSUM : thm := BLSD.LPRODUCT_RSUM
def LPRODUCT_LMUL : thm := BLSD.LPRODUCT_LMUL
def LPRODUCT_LSUM : thm := BLSD.LPRODUCT_LSUM
def LSPACE_COMPLEX_LMUL : thm := BLSD.LSPACE_COMPLEX_LMUL
def MEASURABLE_ON_CNJ : thm := BLSD.MEASURABLE_ON_CNJ
def L2_CNJ_PRODUCT_INTEGRABLE : thm := BLSD.L2_CNJ_PRODUCT_INTEGRABLE
def LSPACE_CNJ : thm := BLSD.LSPACE_CNJ
def LPRODUCT_LSUB : thm := BLSD.LPRODUCT_LSUB

initialize BLSE : HolMultiLib.LpSpaces.LSE ←
  ioB "setupLSE" (HolMultiLib.LpSpaces.setupLSE deps BLSA BLSB BLSD).run

-- LSE (lpspaces.ml 879-966)
def LPRODUCT_L2LIM : thm := BLSE.LPRODUCT_L2LIM
def LPRODUCT_L2LIM_RSLOT : thm := BLSE.LPRODUCT_L2LIM_RSLOT

initialize BLSF : HolMultiLib.LpSpaces.LSF ←
  ioB "setupLSF" (HolMultiLib.LpSpaces.setupLSF deps BLSA BLSB BLSC).run

-- LSF (lpspaces.ml 967-1224)
def LSPACE_SUMMABLE_UNIV : thm := BLSF.LSPACE_SUMMABLE_UNIV

initialize BLSG : HolMultiLib.LpSpaces.LSG ←
  ioB "setupLSG" (HolMultiLib.LpSpaces.setupLSG deps BLSA BLSB BLSC BLSF).run

-- LSG (lpspaces.ml 1225-1343)
def LSPACE_SUMMABLE : thm := BLSG.LSPACE_SUMMABLE
def RIESZ_FISCHER : thm := BLSG.RIESZ_FISCHER

initialize BLSH : HolMultiLib.LpSpaces.LSH ←
  ioB "setupLSH" (HolMultiLib.LpSpaces.setupLSH deps BLSA BLSB).run

-- LSH (lpspaces.ml 1344-1477)
def LSPACE_DOMINATED_CONVERGENCE : thm := BLSH.LSPACE_DOMINATED_CONVERGENCE

initialize BLSI : HolMultiLib.LpSpaces.LSI ←
  ioB "setupLSI" (HolMultiLib.LpSpaces.setupLSI deps BLSA BLSB BLSC BLSH).run

-- LSI (lpspaces.ml 1478-1724)
def LSPACE_APPROXIMATE_BOUNDED : thm := BLSI.LSPACE_APPROXIMATE_BOUNDED
def LSPACE_APPROXIMATE_CONTINUOUS : thm := BLSI.LSPACE_APPROXIMATE_CONTINUOUS
def LSPACE_APPROXIMATE_VECTOR_POLYNOMIAL_FUNCTION : thm := BLSI.LSPACE_APPROXIMATE_VECTOR_POLYNOMIAL_FUNCTION

-- @@WIRING-END

/-- `needs "Multivariate/lpspaces.ml"`: importing this module has built every
    bundle; this is a no-op kept for symmetry with the other wiring files. -/
def ensureLpSpaces : IO Unit := pure ()

end SessionMultiLib.LpSpaces
