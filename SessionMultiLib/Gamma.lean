/- ---------------------------------------------------------------------- -/
/- Session wiring for Multivariate/gamma.ml.                              -/
/- ---------------------------------------------------------------------- -/
/- File: SessionMultiLib/Gamma.lean

  The session half of the gamma.ml translation: it supplies
  HolMultiLib.Gamma's dependencies and exports every theorem by name.
  Importing this module is `needs "Multivariate/gamma.ml"`: its own `needs` are
  its imports, and each bundle is built by `initialize` when the module is
  loaded, in file order.
-/

import SessionMultiLib.Cauchy
import HolMultiLib.Gamma

open HolCore HolCore.Kernel

namespace SessionMultiLib.Gamma

/- The theorem groups (names only; each group's names come from one file). -/

open Session in
def qsession : HolMultiLib.Gamma.QSessionThms :=
  { MULT_AC, REAL_DIV_POW2_ALT, REAL_LET_ADD, REAL_POW_LT_1, SUM_COMBINE_R }

open SessionMultiLib.Topology in
def qtopology : HolMultiLib.Gamma.QTopologyThms :=
  { CLOSURE_INTERIOR, DISCRETE_IMP_CLOSED, lim, TRIVIAL_LIMIT_AT_POSINFINITY,
    UNIFORMLY_CONVERGENT_EQ_CAUCHY_ALT }

open SessionLibrary.Products in
def qproducts : HolMultiLib.Gamma.QProductsThms :=
  { NPRODUCT_FACT, PRODUCT_CLAUSES_RIGHT, REAL_OF_NUM_NPRODUCT }

open SessionLibrary.Floor in
def qfloor : HolMultiLib.Gamma.QFloorThms :=
  { REAL_EQ_INTEGERS_IMP }

open SessionMultiLib.Paths in
def qpaths : HolMultiLib.Gamma.QPathsThms :=
  { COUNTABLE_EMPTY_INTERIOR }

open SessionMultiLib.Integration in
def qintegration : HolMultiLib.Gamma.QIntegrationThms :=
  { HAS_INTEGRAL_LIM_AT_POSINFINITY, HAS_INTEGRAL_LIM_SEQUENTIALLY,
    HAS_INTEGRAL_RESTRICT_INTER, HAS_INTEGRAL_SUBSTITUTION_STRONG, INTEGRABLE_ON_NULL,
    INTEGRAL_NORM_BOUND_INTEGRAL_COMPONENT }

open SessionMultiLib.Measure in
def qmeasure : HolMultiLib.Gamma.QMeasureThms :=
  { MEASURABLE_BOUNDED_AE_BY_INTEGRABLE_IMP_INTEGRABLE }

open SessionMultiLib.Vectors in
def qvectors : HolMultiLib.Gamma.QVectorsThms :=
  { VSUM_OFFSET }

def deps : HolMultiLib.Gamma.GammaDeps where
  ky := SessionMultiLib.Cauchy.deps
  kya := SessionMultiLib.Cauchy.BKYA
  kyb := SessionMultiLib.Cauchy.BKYB
  kyc := SessionMultiLib.Cauchy.BKYC
  kyd := SessionMultiLib.Cauchy.BKYD
  kye := SessionMultiLib.Cauchy.BKYE
  kyf := SessionMultiLib.Cauchy.BKYF
  kyg := SessionMultiLib.Cauchy.BKYG
  kyh := SessionMultiLib.Cauchy.BKYH
  kyi := SessionMultiLib.Cauchy.BKYI
  kyj := SessionMultiLib.Cauchy.BKYJ
  kyk := SessionMultiLib.Cauchy.BKYK
  kyl := SessionMultiLib.Cauchy.BKYL
  kym := SessionMultiLib.Cauchy.BKYM
  kyn := SessionMultiLib.Cauchy.BKYN
  kyo := SessionMultiLib.Cauchy.BKYO
  kyp := SessionMultiLib.Cauchy.BKYP
  kyq := SessionMultiLib.Cauchy.BKYQ
  kyr := SessionMultiLib.Cauchy.BKYR
  kys := SessionMultiLib.Cauchy.BKYS
  kyt := SessionMultiLib.Cauchy.BKYT
  kyu := SessionMultiLib.Cauchy.BKYU
  kyv := SessionMultiLib.Cauchy.BKYV
  kyw := SessionMultiLib.Cauchy.BKYW
  kyx := SessionMultiLib.Cauchy.BKYX
  kyy := SessionMultiLib.Cauchy.BKYY
  kyz := SessionMultiLib.Cauchy.BKYZ
  kyaa := SessionMultiLib.Cauchy.BKYAA
  kyab := SessionMultiLib.Cauchy.BKYAB
  kyac := SessionMultiLib.Cauchy.BKYAC
  kyad := SessionMultiLib.Cauchy.BKYAD
  kyae := SessionMultiLib.Cauchy.BKYAE
  kyaf := SessionMultiLib.Cauchy.BKYAF
  kyag := SessionMultiLib.Cauchy.BKYAG
  kyah := SessionMultiLib.Cauchy.BKYAH
  kyai := SessionMultiLib.Cauchy.BKYAI
  kyaj := SessionMultiLib.Cauchy.BKYAJ
  kyak := SessionMultiLib.Cauchy.BKYAK
  kyal := SessionMultiLib.Cauchy.BKYAL
  kyam := SessionMultiLib.Cauchy.BKYAM
  kyan := SessionMultiLib.Cauchy.BKYAN
  kyao := SessionMultiLib.Cauchy.BKYAO
  kyap := SessionMultiLib.Cauchy.BKYAP
  kyaq := SessionMultiLib.Cauchy.BKYAQ
  kyar := SessionMultiLib.Cauchy.BKYAR
  kyas := SessionMultiLib.Cauchy.BKYAS
  kyat := SessionMultiLib.Cauchy.BKYAT
  kyau := SessionMultiLib.Cauchy.BKYAU
  kyav := SessionMultiLib.Cauchy.BKYAV
  kyaw := SessionMultiLib.Cauchy.BKYAW
  kyax := SessionMultiLib.Cauchy.BKYAX
  kyay := SessionMultiLib.Cauchy.BKYAY
  kyaz := SessionMultiLib.Cauchy.BKYAZ
  kyba := SessionMultiLib.Cauchy.BKYBA
  kybb := SessionMultiLib.Cauchy.BKYBB
  kybc := SessionMultiLib.Cauchy.BKYBC
  kybd := SessionMultiLib.Cauchy.BKYBD
  kybe := SessionMultiLib.Cauchy.BKYBE
  kybf := SessionMultiLib.Cauchy.BKYBF
  kybg := SessionMultiLib.Cauchy.BKYBG
  kybh := SessionMultiLib.Cauchy.BKYBH
  kybi := SessionMultiLib.Cauchy.BKYBI
  kybj := SessionMultiLib.Cauchy.BKYBJ
  kybk := SessionMultiLib.Cauchy.BKYBK
  kybl := SessionMultiLib.Cauchy.BKYBL
  kybm := SessionMultiLib.Cauchy.BKYBM
  kybn := SessionMultiLib.Cauchy.BKYBN
  kybo := SessionMultiLib.Cauchy.BKYBO
  kybp := SessionMultiLib.Cauchy.BKYBP
  kybq := SessionMultiLib.Cauchy.BKYBQ
  kybr := SessionMultiLib.Cauchy.BKYBR
  kybs := SessionMultiLib.Cauchy.BKYBS
  kybt := SessionMultiLib.Cauchy.BKYBT
  kybu := SessionMultiLib.Cauchy.BKYBU
  kybv := SessionMultiLib.Cauchy.BKYBV
  kybw := SessionMultiLib.Cauchy.BKYBW
  kybx := SessionMultiLib.Cauchy.BKYBX
  kyby := SessionMultiLib.Cauchy.BKYBY
  kybz := SessionMultiLib.Cauchy.BKYBZ
  kyca := SessionMultiLib.Cauchy.BKYCA
  kycb := SessionMultiLib.Cauchy.BKYCB
  kycc := SessionMultiLib.Cauchy.BKYCC
  kycd := SessionMultiLib.Cauchy.BKYCD
  kyce := SessionMultiLib.Cauchy.BKYCE
  kycf := SessionMultiLib.Cauchy.BKYCF
  kycg := SessionMultiLib.Cauchy.BKYCG
  qsession := qsession
  qtopology := qtopology
  qproducts := qproducts
  qfloor := qfloor
  qpaths := qpaths
  qintegration := qintegration
  qmeasure := qmeasure
  qvectors := qvectors

private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in gamma.ml order. -/

initialize BGMA : HolMultiLib.Gamma.GMA ←
  ioB "setupGMA" (HolMultiLib.Gamma.setupGMA deps).run

-- GMA (gamma.ml 1-279)
def euler_mascheroni : thm := BGMA.euler_mascheroni
def EULER_MASCHERONI : thm := BGMA.EULER_MASCHERONI
def LOG2_APPROX_40 : thm := BGMA.LOG2_APPROX_40
def EULER_MASCHERONI_APPROX_32 : thm := BGMA.EULER_MASCHERONI_APPROX_32

initialize BGMB : HolMultiLib.Gamma.GMB ←
  ioB "setupGMB" (HolMultiLib.Gamma.setupGMB deps).run

-- GMB (gamma.ml 280-640)
def lgamma : thm := BGMB.lgamma
def LGAMMA : thm := BGMB.LGAMMA
def COMPLEX_DIFFERENTIABLE_AT_LGAMMA : thm := BGMB.COMPLEX_DIFFERENTIABLE_AT_LGAMMA
def LGAMMA_ALT : thm := BGMB.LGAMMA_ALT
def LGAMMA_ALT2 : thm := BGMB.LGAMMA_ALT2

initialize BGMC : HolMultiLib.Gamma.GMC ←
  ioB "setupGMC" (HolMultiLib.Gamma.setupGMC deps BGMB).run

-- GMC (gamma.ml 641-1035)
def cgamma : thm := BGMC.cgamma
def CGAMMA : thm := BGMC.CGAMMA
def CGAMMA_EQ_0 : thm := BGMC.CGAMMA_EQ_0
def CGAMMA_LGAMMA : thm := BGMC.CGAMMA_LGAMMA
def CGAMMA_RECURRENCE_ALT : thm := BGMC.CGAMMA_RECURRENCE_ALT
def CGAMMA_1 : thm := BGMC.CGAMMA_1
def CGAMMA_RECURRENCE : thm := BGMC.CGAMMA_RECURRENCE
def CGAMMA_FACT : thm := BGMC.CGAMMA_FACT
def CGAMMA_POLES : thm := BGMC.CGAMMA_POLES
def COMPLEX_DIFFERENTIABLE_AT_CGAMMA : thm := BGMC.COMPLEX_DIFFERENTIABLE_AT_CGAMMA
def COMPLEX_DIFFERENTIABLE_WITHIN_CGAMMA : thm := BGMC.COMPLEX_DIFFERENTIABLE_WITHIN_CGAMMA
def HOLOMORPHIC_ON_CGAMMA : thm := BGMC.HOLOMORPHIC_ON_CGAMMA
def CONTINUOUS_AT_CGAMMA : thm := BGMC.CONTINUOUS_AT_CGAMMA
def CONTINUOUS_WITHIN_CGAMMA : thm := BGMC.CONTINUOUS_WITHIN_CGAMMA
def CONTINUOUS_ON_CGAMMA : thm := BGMC.CONTINUOUS_ON_CGAMMA
def CGAMMA_SIMPLE_POLES : thm := BGMC.CGAMMA_SIMPLE_POLES
def CNJ_CGAMMA : thm := BGMC.CNJ_CGAMMA
def REAL_GAMMA : thm := BGMC.REAL_GAMMA
def RE_POS_CGAMMA_REAL : thm := BGMC.RE_POS_CGAMMA_REAL

initialize BGMD : HolMultiLib.Gamma.GMD ←
  ioB "setupGMD" (HolMultiLib.Gamma.setupGMD deps BGMC).run

-- GMD (gamma.ml 1036-1550)
def CGAMMA_LEGENDRE_ALT : thm := BGMD.CGAMMA_LEGENDRE_ALT
def CGAMMA_REFLECTION : thm := BGMD.CGAMMA_REFLECTION
def CGAMMA_HALF : thm := BGMD.CGAMMA_HALF
def CGAMMA_LEGENDRE : thm := BGMD.CGAMMA_LEGENDRE

initialize BGME : HolMultiLib.Gamma.GME ←
  ioB "setupGME" (HolMultiLib.Gamma.setupGME deps BGMA BGMC).run

-- GME (gamma.ml 1551-1707)
def CGAMMA_WEIERSTRASS : thm := BGME.CGAMMA_WEIERSTRASS
def COMPLEX_DIFFERENTIABLE_AT_RECIP_CGAMMA : thm := BGME.COMPLEX_DIFFERENTIABLE_AT_RECIP_CGAMMA
def COMPLEX_DIFFERENTIABLE_WITHIN_RECIP_CGAMMA : thm := BGME.COMPLEX_DIFFERENTIABLE_WITHIN_RECIP_CGAMMA
def HOLOMORPHIC_ON_RECIP_CGAMMA : thm := BGME.HOLOMORPHIC_ON_RECIP_CGAMMA
def CONTINUOUS_AT_RECIP_CGAMMA : thm := BGME.CONTINUOUS_AT_RECIP_CGAMMA
def CONTINUOUS_WITHIN_RECIP_CGAMMA : thm := BGME.CONTINUOUS_WITHIN_RECIP_CGAMMA
def CONTINUOUS_ON_RECIP_CGAMMA : thm := BGME.CONTINUOUS_ON_RECIP_CGAMMA
def RECIP_CGAMMA : thm := BGME.RECIP_CGAMMA
def RECIP_CGAMMA_WEIERSTRASS : thm := BGME.RECIP_CGAMMA_WEIERSTRASS

initialize BGMF : HolMultiLib.Gamma.GMF ←
  ioB "setupGMF" (HolMultiLib.Gamma.setupGMF deps BGMC BGMD BGME).run

-- GMF (gamma.ml 1708-1895)
def gamma : thm := BGMF.gamma
def CX_GAMMA : thm := BGMF.CX_GAMMA
def GAMMA : thm := BGMF.GAMMA
def GAMMA_EQ_0 : thm := BGMF.GAMMA_EQ_0
def REAL_DIFFERENTIABLE_AT_GAMMA : thm := BGMF.REAL_DIFFERENTIABLE_AT_GAMMA
def REAL_DIFFERENTIABLE_WITHIN_GAMMA : thm := BGMF.REAL_DIFFERENTIABLE_WITHIN_GAMMA
def REAL_DIFFERENTIABLE_ON_GAMMA : thm := BGMF.REAL_DIFFERENTIABLE_ON_GAMMA
def REAL_CONTINUOUS_ATREAL_GAMMA : thm := BGMF.REAL_CONTINUOUS_ATREAL_GAMMA
def REAL_CONTINUOUS_WITHIN_GAMMA : thm := BGMF.REAL_CONTINUOUS_WITHIN_GAMMA
def REAL_CONTINUOUS_ON_GAMMA : thm := BGMF.REAL_CONTINUOUS_ON_GAMMA
def REAL_DIFFERENTIABLE_ATREAL_RECIP_GAMMA : thm := BGMF.REAL_DIFFERENTIABLE_ATREAL_RECIP_GAMMA
def REAL_DIFFERENTIABLE_WITHIN_RECIP_GAMMA : thm := BGMF.REAL_DIFFERENTIABLE_WITHIN_RECIP_GAMMA
def REAL_DIFFERENTIABLE_ON_RECIP_GAMMA : thm := BGMF.REAL_DIFFERENTIABLE_ON_RECIP_GAMMA
def REAL_CONTINUOUS_ATREAL_RECIP_GAMMA : thm := BGMF.REAL_CONTINUOUS_ATREAL_RECIP_GAMMA
def REAL_CONTINUOUS_WITHINREAL_RECIP_GAMMA : thm := BGMF.REAL_CONTINUOUS_WITHINREAL_RECIP_GAMMA
def REAL_CONTINUOUS_ON_RECIP_GAMMA : thm := BGMF.REAL_CONTINUOUS_ON_RECIP_GAMMA
def GAMMA_RECURRENCE_ALT : thm := BGMF.GAMMA_RECURRENCE_ALT
def GAMMA_1 : thm := BGMF.GAMMA_1
def GAMMA_RECURRENCE : thm := BGMF.GAMMA_RECURRENCE
def GAMMA_FACT : thm := BGMF.GAMMA_FACT
def GAMMA_POLES : thm := BGMF.GAMMA_POLES
def GAMMA_SIMPLE_POLES : thm := BGMF.GAMMA_SIMPLE_POLES
def GAMMA_POS_LE : thm := BGMF.GAMMA_POS_LE
def GAMMA_POS_LT : thm := BGMF.GAMMA_POS_LT
def GAMMA_LEGENDRE_ALT : thm := BGMF.GAMMA_LEGENDRE_ALT
def GAMMA_REFLECTION : thm := BGMF.GAMMA_REFLECTION
def GAMMA_HALF : thm := BGMF.GAMMA_HALF
def GAMMA_LEGENDRE : thm := BGMF.GAMMA_LEGENDRE
def GAMMA_WEIERSTRASS : thm := BGMF.GAMMA_WEIERSTRASS

initialize BGMG : HolMultiLib.Gamma.GMG ←
  ioB "setupGMG" (HolMultiLib.Gamma.setupGMG deps BGMF).run

-- GMG (gamma.ml 1896-2098)
def REAL_LOG_CONVEX_GAMMA : thm := BGMG.REAL_LOG_CONVEX_GAMMA
def GAMMA_REAL_LOG_CONVEX_UNIQUE : thm := BGMG.GAMMA_REAL_LOG_CONVEX_UNIQUE

initialize BGMH : HolMultiLib.Gamma.GMH ←
  ioB "setupGMH" (HolMultiLib.Gamma.setupGMH deps BGMC).run

-- GMH (gamma.ml 2099-2385)
def EULER_HAS_INTEGRAL_CGAMMA : thm := BGMH.EULER_HAS_INTEGRAL_CGAMMA

initialize BGMI : HolMultiLib.Gamma.GMI ←
  ioB "setupGMI" (HolMultiLib.Gamma.setupGMI deps BGMF BGMH).run

-- GMI (gamma.ml 2386-2796)
def EULER_INTEGRAL : thm := BGMI.EULER_INTEGRAL
def EULER_INTEGRABLE : thm := BGMI.EULER_INTEGRABLE
def EULER_HAS_REAL_INTEGRAL_GAMMA : thm := BGMI.EULER_HAS_REAL_INTEGRAL_GAMMA
def EULER_REAL_INTEGRAL : thm := BGMI.EULER_REAL_INTEGRAL
def EULER_REAL_INTEGRABLE : thm := BGMI.EULER_REAL_INTEGRABLE
def EULER_ORIGINAL_REAL_INTEGRABLE : thm := BGMI.EULER_ORIGINAL_REAL_INTEGRABLE
def EULER_ORIGINAL_INTEGRABLE : thm := BGMI.EULER_ORIGINAL_INTEGRABLE
def EULER_ORIGINAL_HAS_INTEGRAL_CGAMMA : thm := BGMI.EULER_ORIGINAL_HAS_INTEGRAL_CGAMMA
def EULER_ORIGINAL_INTEGRAL : thm := BGMI.EULER_ORIGINAL_INTEGRAL
def EULER_ORIGINAL_HAS_REAL_INTEGRAL_GAMMA : thm := BGMI.EULER_ORIGINAL_HAS_REAL_INTEGRAL_GAMMA
def EULER_ORIGINAL_REAL_INTEGRAL : thm := BGMI.EULER_ORIGINAL_REAL_INTEGRAL

initialize BGMJ : HolMultiLib.Gamma.GMJ ←
  ioB "setupGMJ" (HolMultiLib.Gamma.setupGMJ deps BGMB BGMC BGMD).run

-- GMJ (gamma.ml 2797-3492)
def LGAMMA_STIRLING_INTEGRALS_EXIST : thm := BGMJ.LGAMMA_STIRLING_INTEGRALS_EXIST
def LGAMMA_STIRLING : thm := BGMJ.LGAMMA_STIRLING

initialize BGMK : HolMultiLib.Gamma.GMK ←
  ioB "setupGMK" (HolMultiLib.Gamma.setupGMK deps BGMC BGMD BGME BGMF BGMI BGMJ).run

-- GMK (gamma.ml 3493-3779)
def LOG_GAMMA_STIRLING : thm := BGMK.LOG_GAMMA_STIRLING
def CSIN_PRODUCT : thm := BGMK.CSIN_PRODUCT
def SIN_PRODUCT : thm := BGMK.SIN_PRODUCT
def WALLIS_ALT : thm := BGMK.WALLIS_ALT
def WALLIS : thm := BGMK.WALLIS
def GAUSSIAN_INTEGRAL : thm := BGMK.GAUSSIAN_INTEGRAL

-- @@WIRING-END

/-- `needs "Multivariate/gamma.ml"`: importing this module has built every
    bundle; this is a no-op kept for symmetry with the other wiring files. -/
def ensureGamma : IO Unit := pure ()

end SessionMultiLib.Gamma
