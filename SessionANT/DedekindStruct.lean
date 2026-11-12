/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/dedekind_struct.ml                            . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/DedekindStruct.lean

  The session half of the dedekind_struct.ml translation: it supplies HolANT.DedekindStruct's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/dedekind_struct.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.DedekindStruct
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionANT.IdealArith
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionLibrary.Matroids
import SessionLibrary.FieldTheory
import SessionANT.Integral
import SessionANT.Dedekind

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.DedekindStruct

/-- The core theorems dedekind_struct.ml uses. -/
def core1 : HolANT.DedekindStruct.CoreThms1 where
  CHINESE_REMAINDER_IDEALS := SessionANT.IdealArith.«CHINESE_REMAINDER_IDEALS»
  COMAXIMAL_IDEAL_POW := SessionANT.IdealArith.«COMAXIMAL_IDEAL_POW»
  CONJ_ASSOC := Session.CONJ_ASSOC
  DEDEKIND_IDEAL_EQ_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_EQ_VALUATION»
  DEDEKIND_IDEAL_FACTORIZATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_FACTORIZATION»
  DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE := SessionANT.Dedekind.«DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE»
  DEDEKIND_IDEAL_POW_SUBSET := SessionANT.Dedekind.«DEDEKIND_IDEAL_POW_SUBSET»
  DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES»
  DEDEKIND_IDEAL_SUBSET_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_VALUATION»
  DEDEKIND_IMP_INTEGRAL_DOMAIN := SessionANT.Dedekind.«DEDEKIND_IMP_INTEGRAL_DOMAIN»
  DEDEKIND_KRULL_DIMENSION_ONE := SessionANT.Dedekind.«DEDEKIND_KRULL_DIMENSION_ONE»
  DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL := SessionANT.Dedekind.«DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL»
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  EXISTS_UNIQUE_DEF := Session.EXISTS_UNIQUE_DEF
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXTENSION := Session.EXTENSION
  FIELD_EQ_TRIVIAL_IDEALS := SessionLibrary.RingTheory.«FIELD_EQ_TRIVIAL_IDEALS»
  FINITE_UNION := Session.FINITE_UNION
  IDEAL_GENERATED_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_0»
  IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE := SessionLibrary.RingTheory.«IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE»
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IDEAL_GENERATED_INC_GEN := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC_GEN»
  IDEAL_GENERATED_INSERT_ZERO := SessionLibrary.RingTheory.«IDEAL_GENERATED_INSERT_ZERO»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_GENERATED_MINIMAL_EQ := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL_EQ»
  IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0 := SessionANT.IdealArith.«IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0»
  IDEAL_GENERATED_RING_IDEAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_RING_IDEAL»
  IDEAL_GENERATED_SUBSET := SessionLibrary.RingTheory.«IDEAL_GENERATED_SUBSET»
  IDEAL_GENERATED_UNION := SessionLibrary.RingTheory.«IDEAL_GENERATED_UNION»
  IDEAL_POW_0 := SessionANT.IdealArith.«IDEAL_POW_0»
  IDEAL_POW_1 := SessionANT.IdealArith.«IDEAL_POW_1»
  IDEAL_POW_ANTIMONO := SessionANT.IdealArith.«IDEAL_POW_ANTIMONO»
  IDEAL_POW_EQ_ZERO := SessionANT.IdealArith.«IDEAL_POW_EQ_ZERO»
  IDEAL_POW_PRINCIPAL := SessionANT.IdealArith.«IDEAL_POW_PRINCIPAL»
  IDEAL_POW_SUBSET_PRIME_IDEAL := SessionANT.IdealArith.«IDEAL_POW_SUBSET_PRIME_IDEAL»
  IDEAL_PROD_AC := SessionANT.IdealArith.«IDEAL_PROD_AC»
  IDEAL_PROD_CARRIER := SessionANT.IdealArith.«IDEAL_PROD_CARRIER»
  IDEAL_PROD_EPIMORPHIC_IMAGE := SessionANT.IdealArith.«IDEAL_PROD_EPIMORPHIC_IMAGE»
  IDEAL_PROD_EQ_ZERO := SessionANT.IdealArith.«IDEAL_PROD_EQ_ZERO»
  IDEAL_PROD_PRINCIPAL := SessionANT.IdealArith.«IDEAL_PROD_PRINCIPAL»
  IDEAL_PROD_PRINCIPAL_CANCEL := SessionANT.IdealArith.«IDEAL_PROD_PRINCIPAL_CANCEL»
  IDEAL_PROD_RZERO := SessionANT.IdealArith.«IDEAL_PROD_RZERO»
  IDEAL_PROD_SCALE := SessionANT.IdealArith.«IDEAL_PROD_SCALE»
  IDEAL_VALUATION_EQ_0 := SessionANT.Dedekind.«IDEAL_VALUATION_EQ_0»
  IDEAL_VALUATION_FINITE_SUPPORT := SessionANT.Dedekind.«IDEAL_VALUATION_FINITE_SUPPORT»
  IDEAL_VALUATION_IDEAL_POW := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_POW»
  IDEAL_VALUATION_IDEAL_PROD := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_PROD»
  IDEAL_VALUATION_PRIME := SessionANT.Dedekind.«IDEAL_VALUATION_PRIME»
  IDEAL_VALUATION_SETADD := SessionANT.Dedekind.«IDEAL_VALUATION_SETADD»
  IDEAL_VALUATION_UNIQUE := SessionANT.Dedekind.«IDEAL_VALUATION_UNIQUE»
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  INSERT_INSERT := Session.INSERT_INSERT
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SELF := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SELF»
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_ADD := SessionLibrary.RingTheory.«IN_RING_IDEAL_ADD»
  IN_RING_IDEAL_SUB := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUB»
  IN_SING := Session.IN_SING
  IN_UNION := Session.IN_UNION
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_0 := Session.LE_0
  LE_CASES := Session.LE_CASES
  LE_REFL := Session.LE_REFL
  MAXIMAL_IDEAL_0 := SessionLibrary.RingTheory.«MAXIMAL_IDEAL_0»
  MAXIMAL_IDEAL_COMAXIMAL := SessionANT.IdealArith.«MAXIMAL_IDEAL_COMAXIMAL»
  MAXIMAL_IDEAL_CORRESPONDENCE := SessionLibrary.RingTheory.«MAXIMAL_IDEAL_CORRESPONDENCE»
  MAXIMAL_IDEAL_EXISTS := SessionLibrary.RingTheory.«MAXIMAL_IDEAL_EXISTS»
  MAXIMAL_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«MAXIMAL_IDEAL_IMP_SUBSET»
  MAXIMAL_IMP_PRIME_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PRIME_IDEAL»
  MAXIMAL_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PROPER_IDEAL»
  MAXIMAL_IMP_RING_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_RING_IDEAL»
  MAXIMAL_SUPERIDEAL_EXISTS := SessionLibrary.RingTheory.«MAXIMAL_SUPERIDEAL_EXISTS»
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  PID := SessionLibrary.RingTheory.«PID»
  PID_EQ_NOETHERIAN_BEZOUT_DOMAIN := SessionLibrary.RingTheory.«PID_EQ_NOETHERIAN_BEZOUT_DOMAIN»
  PID_EQ_UFD_PRIME_MAXIMAL := SessionLibrary.RingTheory.«PID_EQ_UFD_PRIME_MAXIMAL»
  PID_IMP_DEDEKIND := SessionANT.Dedekind.«PID_IMP_DEDEKIND»
  PRIME_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_PROPER_IDEAL»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRINCIPAL_IDEAL_0 := SessionLibrary.RingTheory.«PRINCIPAL_IDEAL_0»
  PRINCIPAL_IDEAL_CARRIER := SessionLibrary.RingTheory.«PRINCIPAL_IDEAL_CARRIER»
  PRINCIPAL_IDEAL_IDEAL_GENERATED_SING := SessionLibrary.RingTheory.«PRINCIPAL_IDEAL_IDEAL_GENERATED_SING»
  PROPER_IDEAL := SessionLibrary.RingTheory.«PROPER_IDEAL»
  PROPER_IDEAL_ALT := SessionLibrary.RingTheory.«PROPER_IDEAL_ALT»
  PSUBSET := Session.PSUBSET
  QUOTIENT_RING_0 := SessionLibrary.RingTheory.«QUOTIENT_RING_0»
  QUOTIENT_RING_IDEAL_CORRESPONDENCE := SessionLibrary.RingTheory.«QUOTIENT_RING_IDEAL_CORRESPONDENCE»
  RIGHT_EXISTS_IMP_THM := Session.RIGHT_EXISTS_IMP_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_COSET_EQ_IDEAL := SessionLibrary.RingTheory.«RING_COSET_EQ_IDEAL»
  RING_EPIMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_EPIMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_IDEAL_CARRIER := SessionLibrary.RingTheory.«RING_IDEAL_CARRIER»
  RING_IDEAL_EPIMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_IDEAL_EPIMORPHIC_IMAGE»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IDEAL_PROD := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PROD»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_IDEAL_SETADD := SessionLibrary.RingTheory.«RING_IDEAL_SETADD»
  RING_ISOMORPHISM_IMP_EPIMORPHISM := SessionLibrary.RingTheory.«RING_ISOMORPHISM_IMP_EPIMORPHISM»
  RING_ISOMORPHISM_IMP_MONOMORPHISM := SessionLibrary.RingTheory.«RING_ISOMORPHISM_IMP_MONOMORPHISM»
  RING_MONOMORPHISM_EQ_0 := SessionLibrary.RingTheory.«RING_MONOMORPHISM_EQ_0»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_SETADD_SUPERSET_LEFT := SessionLibrary.RingTheory.«RING_SETADD_SUPERSET_LEFT»
  RING_SETADD_SUPERSET_RIGHT := SessionLibrary.RingTheory.«RING_SETADD_SUPERSET_RIGHT»
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_REFL := Session.SUBSET_REFL
  SUBSET_TRANS := Session.SUBSET_TRANS
  TRIVIAL_QUOTIENT_RING := SessionLibrary.RingTheory.«TRIVIAL_QUOTIENT_RING»
  TRIVIAL_RING_10 := SessionLibrary.RingTheory.«TRIVIAL_RING_10»
  dedekind_domain := SessionANT.Dedekind.«dedekind_domain»
  integral_domain := SessionLibrary.RingTheory.«integral_domain»
  local_ring := SessionLibrary.RingTheory.«local_ring»
  maximal_ideal := SessionLibrary.RingTheory.«maximal_ideal»
  pairwise := Session.pairwise
  principal_ideal := SessionLibrary.RingTheory.«principal_ideal»
  proper_ideal := SessionLibrary.RingTheory.«proper_ideal»
  trivial_ring := SessionLibrary.RingTheory.«trivial_ring»

/-- What dedekind_struct.ml uses from Session. -/
def deps : HolANT.DedekindStruct.DedekindStructDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  define s := do ExceptT.mk (Session.define (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  new_recursive_definition ax s := do
    ExceptT.mk (Session.new_recursive_definition ax (← HolLight.q s))
  LIST_INDUCT_TAC := Session.LIST_INDUCT_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  METIS_TAC := Session.METIS_TAC
  ASM_METIS_TAC := Session.ASM_METIS_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  TAUT t := ExceptT.mk (Session.TAUT t)
  ITAUT t := ExceptT.mk (Session.ITAUT t)
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH t)
  REAL_FIELD t := ExceptT.mk (Session.REAL_FIELD t)
  REAL_ARITH_TAC := Session.REAL_ARITH_TAC
  ASM_REAL_ARITH_TAC := Session.ASM_REAL_ARITH_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  INT_ARITH t := ExceptT.mk (Session.INT_ARITH t)
  INT_ARITH_TAC := Session.INT_ARITH_TAC
  ASM_INT_ARITH_TAC := Session.ASM_INT_ARITH_TAC
  INTEGER_RULE t := ExceptT.mk (Session.INTEGER_RULE t)
  INTEGER_TAC := Session.INTEGER_TAC
  NUMBER_RULE := Session.NUMBER_RULE
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  INT_REDUCE_CONV := Session.INT_REDUCE_CONV
  INT_RED_CONV := Session.INT_RED_CONV
  INT_REM_DOWN_CONV := Session.INT_REM_DOWN_CONV
  HAS_SIZE_CONV := Session.HAS_SIZE_CONV
  let_CONV := Session.let_CONV
  num_CONV := Session.num_CONV
  mk_numeral := Session.mk_numeral
  PRIME_CONV t := ExceptT.mk (SessionLibrary.Pocklington.PRIME_CONV t)
  PRIME_RULE := SessionLibrary.Pocklington.PRIME_RULE
  RING_RULE t := ExceptT.mk (SessionLibrary.RingTheory.RING_RULE t)
  INTEGRAL_DOMAIN_RULE t := ExceptT.mk (SessionLibrary.RingTheory.INTEGRAL_DOMAIN_RULE t)
  FIELD_TAC := SessionLibrary.RingTheory.FIELD_TAC
  RING_CARRIER_TAC := SessionLibrary.RingTheory.RING_CARRIER_TAC
  RING_TAC := SessionLibrary.RingTheory.RING_TAC
  RING_PULL_DIV_TAC := SessionLibrary.RingTheory.RING_PULL_DIV_TAC
  LET_TAC := Session.LET_TAC
  basic_ss := Session.basic_ss
  INTEGER_MOD_RING_RED_CONV := SessionLibrary.RingTheory.INTEGER_MOD_RING_RED_CONV
  NUM_SUB_CONV := Session.NUM_SUB_CONV
  REAL_RAT_REDUCE_CONV := Session.REAL_RAT_REDUCE_CONV
  NUM_EQ_CONV := Session.NUM_EQ_CONV
  NUM_DIV_CONV := Session.NUM_DIV_CONV
  EXP_MOD_CONV := Session.EXP_MOD_CONV
  EXPAND_CASES_CONV := Session.EXPAND_CASES_CONV
  DIVIDES_CONV := SessionLibrary.Prime.DIVIDES_CONV
  COPRIME_CONV := SessionLibrary.Prime.COPRIME_CONV
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in dedekind_struct.ml order. -/
initialize BDedekindStruct : HolANT.DedekindStruct.DedekindStruct ←
  ioB "setupDedekindStruct" (HolANT.DedekindStruct.setupDedekindStruct deps).run

-- DedekindStruct
def DVR : thm := BDedekindStruct.DVR
def DVR_IMP_DEDEKIND : thm := BDedekindStruct.DVR_IMP_DEDEKIND
def DEDEKIND_LOCAL_IDEAL_MAXIMAL_POW : thm := BDedekindStruct.DEDEKIND_LOCAL_IDEAL_MAXIMAL_POW
def DVR_IFF_LOCAL_DEDEKIND : thm := BDedekindStruct.DVR_IFF_LOCAL_DEDEKIND
def DVR_IDEAL_MAXIMAL_POW : thm := BDedekindStruct.DVR_IDEAL_MAXIMAL_POW
def DVR_IDEALS_TOTALLY_ORDERED : thm := BDedekindStruct.DVR_IDEALS_TOTALLY_ORDERED
def DEDEKIND_WEAK_APPROXIMATION : thm := BDedekindStruct.DEDEKIND_WEAK_APPROXIMATION
def DEDEKIND_IDEAL_WEAK_APPROXIMATION : thm := BDedekindStruct.DEDEKIND_IDEAL_WEAK_APPROXIMATION
def DEDEKIND_TWO_GENERATORS_STRONG : thm := BDedekindStruct.DEDEKIND_TWO_GENERATORS_STRONG
def DEDEKIND_TWO_GENERATORS : thm := BDedekindStruct.DEDEKIND_TWO_GENERATORS
def DEDEKIND_QUOTIENT_PRINCIPAL : thm := BDedekindStruct.DEDEKIND_QUOTIENT_PRINCIPAL
def DEDEKIND_LOCAL_QUOTIENT_PRIME_POW : thm := BDedekindStruct.DEDEKIND_LOCAL_QUOTIENT_PRIME_POW
def DEDEKIND_UFD_IFF_PID : thm := BDedekindStruct.DEDEKIND_UFD_IFF_PID
def DEDEKIND_BEZOUT_IFF_PID : thm := BDedekindStruct.DEDEKIND_BEZOUT_IFF_PID
def ideal_class : thm := BDedekindStruct.ideal_class
def IN_IDEAL_CLASS : thm := BDedekindStruct.IN_IDEAL_CLASS
def IDEAL_CLASS_REFL : thm := BDedekindStruct.IDEAL_CLASS_REFL
def IDEAL_CLASS_SYM : thm := BDedekindStruct.IDEAL_CLASS_SYM
def IDEAL_CLASS_TRANS : thm := BDedekindStruct.IDEAL_CLASS_TRANS
def IDEAL_CLASS_MUL : thm := BDedekindStruct.IDEAL_CLASS_MUL
def IN_IDEAL_CLASS_ISOMORPHIC_IMAGE : thm := BDedekindStruct.IN_IDEAL_CLASS_ISOMORPHIC_IMAGE
def IDEAL_CLASS_PRINCIPAL : thm := BDedekindStruct.IDEAL_CLASS_PRINCIPAL
def PRINCIPAL_IDEAL_CLASS : thm := BDedekindStruct.PRINCIPAL_IDEAL_CLASS
def DEDEKIND_IDEAL_CLASS_INVERSE : thm := BDedekindStruct.DEDEKIND_IDEAL_CLASS_INVERSE
def DEDEKIND_PID_IFF_TRIVIAL_CLASS_GROUP : thm := BDedekindStruct.DEDEKIND_PID_IFF_TRIVIAL_CLASS_GROUP
def DEDEKIND_IDEAL_CLASS_COPRIME : thm := BDedekindStruct.DEDEKIND_IDEAL_CLASS_COPRIME

/-- `needs "ANT/dedekind_struct.ml"`: already done by importing this module. -/
def ensureDedekindStruct : IO Unit := pure ()

end SessionANT.DedekindStruct
