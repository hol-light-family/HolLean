/- HolExamples: translations of files of HOL Light's Examples/ (see HolExamples/Common.lean).
   Each module is a toplevel session; building it runs it.
   HolExamples/BitBlast.lean is not imported here, so `make examples` and
   `make check` do not build it (it takes about 45 minutes); build it with
   `lake build HolExamples.BitBlast`. -/
import HolExamples.BddExamples
import HolExamples.BitBlastGeneric
import HolExamples.Bondy
import HolExamples.Combin
import HolExamples.Cong
import HolExamples.Cooper
import HolExamples.Dickson
import HolExamples.DLO
import HolExamples.Doomsday
import HolExamples.Forster
import HolExamples.GcdRecurrence
import HolExamples.HarmonicSum
import HolExamples.Hol88
import HolExamples.Holby
import HolExamples.Kb
import HolExamples.LagrangeLemma
import HolExamples.Machin
import HolExamples.McCarthy
import HolExamples.MillerRabin
import HolExamples.Mizar
import HolExamples.MultiWf
import HolExamples.Pell
import HolExamples.PolyLog
import HolExamples.Prog
import HolExamples.PseudoPrime
import HolExamples.RecTypes
import HolExamples.Reduct
import HolExamples.SafetyLiveness
import HolExamples.STE
import HolExamples.Zolotarev
