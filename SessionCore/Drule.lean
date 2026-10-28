/- File: SessionCore/Drule.lean
drule.ml's rules as top-level names, closed over the bool.ml bundle `B`.
-/
import SessionCore.Bool
import HolCore.Drule

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Theorems HolCore.Classic
open HolCore.Trivia HolCore.Printer

namespace Session

/- Drule rules. The `B`-parameterized ones are closed over `B`; the standalone
   ones are re-exported. -/
def mk_thm := Drule.mk_thm B
def MP_CONV := Drule.MP_CONV B
def INSTANTIATE_ALL := Drule.INSTANTIATE_ALL B
def PART_MATCH := Drule.PART_MATCH B
def GEN_PART_MATCH := Drule.GEN_PART_MATCH B
def MATCH_MP := Drule.MATCH_MP B
def HIGHER_REWRITE_CONV := Drule.HIGHER_REWRITE_CONV B
-- standalone (no B):
export Drule (MK_CONJ MK_DISJ MK_FORALL MK_EXISTS BETAS_CONV instantiate
  INSTANTIATE type_unify term_unify term_type_unify deep_alpha term_match)


end Session
