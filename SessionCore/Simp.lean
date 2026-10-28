/- File: SessionCore/Simp.lean
simp.ml: rewriting and simplification, as top-level names closed over the
bool.ml bundle `B`.
-/
import SessionCore.Itab
import HolCore.Simp

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Theorems HolCore.Classic
open HolCore.Trivia HolCore.Printer

namespace Session

/- Simp: rewriting and simplification. B-closed aliases. -/
def REWR_CONV := Simp.REWR_CONV B
def IMP_REWR_CONV := Simp.IMP_REWR_CONV B
def net_of_thm := Simp.net_of_thm B
def net_of_cong := Simp.net_of_cong B
def mk_rewrites := Simp.mk_rewrites B
def GEN_REWRITE_CONV := Simp.GEN_REWRITE_CONV' B
def PURE_REWRITE_CONV := Simp.PURE_REWRITE_CONV' B
def REWRITE_CONV := Simp.REWRITE_CONV' B
/-- `ORDERED_REWR_CONV ord th` (simp.ml 31): `REWR_CONV th`, failing unless
    the result `l = r` has `ord l r`. -/
def ORDERED_REWR_CONV := Simp.ORDERED_REWR_CONV B
def PURE_ONCE_REWRITE_CONV := Simp.PURE_ONCE_REWRITE_CONV' B
def ONCE_REWRITE_CONV := Simp.ONCE_REWRITE_CONV' B
def REWRITE_RULE := Simp.REWRITE_RULE B
def PURE_REWRITE_RULE := Simp.PURE_REWRITE_RULE B
def GEN_REWRITE_RULE := Simp.GEN_REWRITE_RULE B
def ONCE_REWRITE_RULE := Simp.ONCE_REWRITE_RULE B
def PURE_ONCE_REWRITE_RULE := Simp.PURE_ONCE_REWRITE_RULE B
def ASM_REWRITE_RULE := Simp.ASM_REWRITE_RULE B
def PURE_ASM_REWRITE_RULE := Simp.PURE_ASM_REWRITE_RULE B
def PURE_ONCE_ASM_REWRITE_RULE := Simp.PURE_ONCE_ASM_REWRITE_RULE B
def ONCE_ASM_REWRITE_RULE := Simp.ONCE_ASM_REWRITE_RULE B
def REWRITE_TAC := Simp.REWRITE_TAC B
def PURE_REWRITE_TAC := Simp.PURE_REWRITE_TAC B
def ONCE_REWRITE_TAC := Simp.ONCE_REWRITE_TAC B
def GEN_REWRITE_TAC := Simp.GEN_REWRITE_TAC B
def PURE_ONCE_REWRITE_TAC := Simp.PURE_ONCE_REWRITE_TAC B
def ASM_REWRITE_TAC := Simp.ASM_REWRITE_TAC B
def PURE_ASM_REWRITE_TAC := Simp.PURE_ASM_REWRITE_TAC B
def ONCE_ASM_REWRITE_TAC := Simp.ONCE_ASM_REWRITE_TAC B
def SIMP_CONV := Simp.SIMP_CONV' B
def PURE_SIMP_CONV := Simp.PURE_SIMP_CONV' B
def ONCE_SIMP_CONV := Simp.ONCE_SIMP_CONV' B
def SIMP_RULE := Simp.SIMP_RULE B
def PURE_SIMP_RULE := Simp.PURE_SIMP_RULE B
def ONCE_SIMP_RULE := Simp.ONCE_SIMP_RULE B
def SIMP_TAC := Simp.SIMP_TAC B
def PURE_SIMP_TAC := Simp.PURE_SIMP_TAC B
def ONCE_SIMP_TAC := Simp.ONCE_SIMP_TAC B
def ASM_SIMP_TAC := Simp.ASM_SIMP_TAC B
def PURE_ASM_SIMP_TAC := Simp.PURE_ASM_SIMP_TAC B
def ONCE_ASM_SIMP_TAC := Simp.ONCE_ASM_SIMP_TAC B
def empty_ss := Simp.empty_ss B
/-- `ss_of_thms thms ss` (simp.ml 240): add rewrites to a simpset. -/
def ss_of_thms := Simp.ss_of_thms B
/-- `ss_of_conv keytm conv ss` (simp.ml 245): add a conversion to a simpset. -/
def ss_of_conv := Simp.ss_of_conv
def basic_ss := Simp.basic_ss B
def set_basic_rewrites := Simp.set_basic_rewrites B
def extend_basic_rewrites := Simp.extend_basic_rewrites B
def basic_rewrites := Simp.basic_rewrites
def set_basic_convs := Simp.set_basic_convs B
def extend_basic_convs := Simp.extend_basic_convs B
def basic_convs := Simp.basic_convs
def basic_net := Simp.basic_net
def set_basic_congs := Simp.set_basic_congs
def extend_basic_congs := Simp.extend_basic_congs
def basic_congs := Simp.basic_congs
def AUGMENT_SIMPSET := Simp.AUGMENT_SIMPSET B
def ABBREV_TAC := Simp.ABBREV_TAC B
def EXPAND_TAC := Simp.EXPAND_TAC B
export Simp (gconv term_order REWRITES_CONV net_of_conv ss_of_thms ss_of_conv
  ss_of_congs ss_of_prover ss_of_provers ss_of_maker mk_prover augment apply_prover
  ONCE_DEPTH_SQCONV DEPTH_SQCONV REDEPTH_SQCONV TOP_DEPTH_SQCONV TOP_SWEEP_SQCONV)

end Session
