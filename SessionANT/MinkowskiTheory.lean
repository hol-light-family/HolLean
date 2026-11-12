/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/minkowski_theory.ml                           . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/MinkowskiTheory.lean

  The session half of the minkowski_theory.ml translation: it supplies HolANT.MinkowskiTheory's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/minkowski_theory.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.MinkowskiTheory
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Matroids
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionLibrary.FieldTheory
import SessionLibrary.Isum
import SessionLibrary.Products
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionANT.Algmisc
import SessionANT.IdealArith
import SessionANT.Integral
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.LinearForms
import SessionANT.Numfield
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Classgroup
import SessionANT.ClassgroupGroup
import SessionANT.PrimeSplit
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.Quadratic
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.NfValuation
import SessionANT.RelativeSplit
import SessionANT.Integrality
import SessionLibrary.RingGroups
import SessionANT.FingenGroup
import SessionMultiLib.Misc
import SessionMultiLib.Metric
import SessionMultiLib.Homology
import SessionMultiLib.Vectors
import SessionMultiLib.Determinants
import SessionMultiLib.Topology
import SessionMultiLib.Convex
import SessionMultiLib.Paths
import SessionMultiLib.Polytope
import SessionMultiLib.Degree
import SessionMultiLib.Derivatives
import SessionMultiLib.Integration
import SessionMultiLib.Measure
import SessionMultiLib.ComplexAlgebra
import SessionMultiLib.Complexes
import SessionMultiLib.Canal
import SessionMultiLib.Transcendentals
import SessionMultiLib.RealAnalysis
import SessionMultiLib.MoreTop
import SessionMultiLib.Cauchy
import SessionMultiLib.ComplexRing
import SessionMultiLib.ComplexField
import SessionANT.ComplexEmbeddings
import SessionANT.PowerBasis
import SessionANT.InfinitePlaces

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.MinkowskiTheory

/-- The core theorems minkowski_theory.ml uses. -/
def core1 : HolANT.MinkowskiTheory.CoreThms1 where
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_LE_2 := Session.CARD_LE_2
  CARD_SUBSET := Session.CARD_SUBSET
  CLASS_GROUP := SessionANT.ClassgroupGroup.«CLASS_GROUP»
  CLASS_GROUP_MUL := SessionANT.ClassgroupGroup.«CLASS_GROUP_MUL»
  CNJ_ADD := SessionMultiLib.ComplexAlgebra.«CNJ_ADD»
  CNJ_CX := SessionMultiLib.ComplexAlgebra.«CNJ_CX»
  CNJ_II := SessionMultiLib.ComplexAlgebra.«CNJ_II»
  CNJ_MUL := SessionMultiLib.ComplexAlgebra.«CNJ_MUL»
  CNJ_SUB := SessionMultiLib.ComplexAlgebra.«CNJ_SUB»
  CNJ_VSUM := SessionMultiLib.ComplexAlgebra.«CNJ_VSUM»
  COMPLEX_ADD_RDISTRIB := SessionMultiLib.ComplexAlgebra.«COMPLEX_ADD_RDISTRIB»
  COMPLEX_EMBEDDINGS_CNJ := SessionANT.InfinitePlaces.«COMPLEX_EMBEDDINGS_CNJ»
  COMPLEX_EMBEDDINGS_CNJ_CNJ := SessionANT.InfinitePlaces.«COMPLEX_EMBEDDINGS_CNJ_CNJ»
  COMPLEX_EMBEDDINGS_HAS_SIZE := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_HAS_SIZE»
  COMPLEX_EMBEDDINGS_NONEMPTY := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_NONEMPTY»
  COMPLEX_EMBEDDINGS_NORM_EQ := SessionANT.InfinitePlaces.«COMPLEX_EMBEDDINGS_NORM_EQ»
  COMPLEX_EQ := SessionMultiLib.ComplexAlgebra.«COMPLEX_EQ»
  COMPLEX_MUL_CNJ := SessionMultiLib.ComplexAlgebra.«COMPLEX_MUL_CNJ»
  COMPLEX_MUL_LZERO := SessionMultiLib.ComplexAlgebra.«COMPLEX_MUL_LZERO»
  COMPLEX_NORM_CNJ := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_CNJ»
  COMPLEX_NORM_CX := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_CX»
  COMPLEX_NORM_LE_RE_IM := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_LE_RE_IM»
  COMPLEX_NORM_MUL := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_MUL»
  COMPLEX_NORM_POW := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_POW»
  COMPLEX_POW_II_2 := SessionMultiLib.ComplexAlgebra.«COMPLEX_POW_II_2»
  COMPLEX_POW_ONE := SessionMultiLib.ComplexAlgebra.«COMPLEX_POW_ONE»
  COMPLEX_RING_CLAUSES := SessionMultiLib.ComplexRing.«COMPLEX_RING_CLAUSES»
  COMPLEX_RING_OF_INT := SessionMultiLib.ComplexRing.«COMPLEX_RING_OF_INT»
  COMPLEX_RING_SUM := SessionMultiLib.ComplexRing.«COMPLEX_RING_SUM»
  COMPLEX_VEC_0 := SessionMultiLib.ComplexAlgebra.«COMPLEX_VEC_0»
  CX_ADD := SessionMultiLib.ComplexAlgebra.«CX_ADD»
  CX_INJ := SessionMultiLib.ComplexAlgebra.«CX_INJ»
  CX_MUL := SessionMultiLib.ComplexAlgebra.«CX_MUL»
  CX_NEG := SessionMultiLib.ComplexAlgebra.«CX_NEG»
  CX_POW := SessionMultiLib.ComplexAlgebra.«CX_POW»
  DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE := SessionANT.Dedekind.«DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE»
  DEDEKIND_IDEAL_PROD_CANCEL := SessionANT.Dedekind.«DEDEKIND_IDEAL_PROD_CANCEL»
  DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES»
  DEDEKIND_IMP_INTEGRAL_DOMAIN := SessionANT.Dedekind.«DEDEKIND_IMP_INTEGRAL_DOMAIN»
  DEDEKIND_IMP_NOETHERIAN := SessionANT.Dedekind.«DEDEKIND_IMP_NOETHERIAN»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  DIVIDES_0 := SessionLibrary.Prime.«DIVIDES_0»
  DIVIDES_LE := Session.DIVIDES_LE
  EQ_SYM_EQ := Session.EQ_SYM_EQ
  EQ_TRANS := Session.EQ_TRANS
  ETA_AX := Session.ETA_AX
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXTENSION := Session.EXTENSION
  FINITE_COMPLEX_EMBEDDINGS := SessionANT.ComplexEmbeddings.«FINITE_COMPLEX_EMBEDDINGS»
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_IMAGE_INJ_EQ := Session.FINITE_IMAGE_INJ_EQ
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_AND_THM := Session.FORALL_AND_THM
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
  FREE_BASIS_IN_CARRIER := SessionLibrary.RingDet.«FREE_BASIS_IN_CARRIER»
  FREE_BASIS_QUOTIENT_RING_HAS_SIZE := SessionANT.RingOfIntegers.«FREE_BASIS_QUOTIENT_RING_HAS_SIZE»
  GROUP_ID_SUBGROUP := SessionLibrary.GroupTheory.«GROUP_ID_SUBGROUP»
  GROUP_MUL_SUBGROUP := SessionLibrary.GroupTheory.«GROUP_MUL_SUBGROUP»
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_INDEX := Session.HAS_SIZE_INDEX
  IDEAL_CLASS_EQ := SessionANT.Classgroup.«IDEAL_CLASS_EQ»
  IDEAL_CLASS_EQ_ID := SessionANT.ClassgroupGroup.«IDEAL_CLASS_EQ_ID»
  IDEAL_CLASS_IN_CLASS_GROUP := SessionANT.ClassgroupGroup.«IDEAL_CLASS_IN_CLASS_GROUP»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_NORM_CARRIER := SessionANT.IdealNorm.«IDEAL_NORM_CARRIER»
  IDEAL_NORM_IN_IDEAL := SessionANT.IdealNorm.«IDEAL_NORM_IN_IDEAL»
  IDEAL_NORM_POS := SessionANT.IdealNorm.«IDEAL_NORM_POS»
  IDEAL_NORM_SUBSET_DIVIDES := SessionANT.IdealNorm.«IDEAL_NORM_SUBSET_DIVIDES»
  IDEAL_PROD_ASSOC := SessionANT.IdealArith.«IDEAL_PROD_ASSOC»
  IDEAL_PROD_CARRIER := SessionANT.IdealArith.«IDEAL_PROD_CARRIER»
  IDEAL_PROD_COMM := SessionANT.IdealArith.«IDEAL_PROD_COMM»
  IDEAL_PROD_EQ_ZERO := SessionANT.IdealArith.«IDEAL_PROD_EQ_ZERO»
  IDEAL_PROD_SUBSET_RIGHT := SessionANT.IdealArith.«IDEAL_PROD_SUBSET_RIGHT»
  IM := SessionMultiLib.ComplexAlgebra.«IM»
  IMP_CONJ := Session.IMP_CONJ
  IM_ADD := SessionMultiLib.ComplexAlgebra.«IM_ADD»
  IM_CNJ := SessionMultiLib.ComplexAlgebra.«IM_CNJ»
  IM_CX := SessionMultiLib.ComplexAlgebra.«IM_CX»
  IM_II := SessionMultiLib.ComplexAlgebra.«IM_II»
  IM_MUL_CX := SessionMultiLib.ComplexAlgebra.«IM_MUL_CX»
  IM_SUB := SessionMultiLib.ComplexAlgebra.«IM_SUB»
  IM_VSUM := SessionMultiLib.ComplexAlgebra.«IM_VSUM»
  INFINITE := Session.INFINITE
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGRAL_DOMAIN_RING_OF_INTEGERS := SessionANT.Numfield.«INTEGRAL_DOMAIN_RING_OF_INTEGERS»
  INTEGRAL_DOMAIN_UNIT_IDEAL := SessionANT.Classgroup.«INTEGRAL_DOMAIN_UNIT_IDEAL»
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_ABS_POS := Session.INT_ABS_POS
  INT_COSETS_MATRIX_IMAGE := SessionANT.Zlattice.«INT_COSETS_MATRIX_IMAGE»
  INT_DIVIDES_RABS := Session.INT_DIVIDES_RABS
  INT_LATTICE_FULL_RANK := SessionANT.Zlattice.«INT_LATTICE_FULL_RANK»
  INT_LATTICE_MATRIX_IMAGE := SessionANT.Zlattice.«INT_LATTICE_MATRIX_IMAGE»
  INT_MATRIX_IMAGE_IN := SessionANT.Zlattice.«INT_MATRIX_IMAGE_IN»
  INT_MATRIX_IMAGE_INJECTIVE := SessionANT.Zlattice.«INT_MATRIX_IMAGE_INJECTIVE»
  INT_MUL_RZERO := Session.INT_MUL_RZERO
  INT_NOT_LE := Session.INT_NOT_LE
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_REM_EQ := Session.INT_REM_EQ
  INT_SUB_REFL := Session.INT_SUB_REFL
  IN_DELETE := Session.IN_DELETE
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_CLASS := SessionANT.DedekindStruct.«IN_IDEAL_CLASS»
  IN_IDEAL_GENERATED_SELF := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SELF»
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_RMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_RMUL»
  IN_RING_IDEAL_SUB := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUB»
  IN_SING := Session.IN_SING
  IN_SUBRING_MUL := SessionLibrary.RingTheory.«IN_SUBRING_MUL»
  IN_UNIV := Session.IN_UNIV
  ISUM_0 := SessionLibrary.Isum.«ISUM_0»
  LE_1 := Session.LE_1
  MAXIMAL_IMP_PRIME_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PRIME_IDEAL»
  MAXIMAL_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PROPER_IDEAL»
  MAXIMAL_IMP_RING_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_RING_IDEAL»
  MAXIMAL_SUPERIDEAL_EXISTS := SessionLibrary.RingTheory.«MAXIMAL_SUPERIDEAL_EXISTS»
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MINKOWSKI_LINEAR_FORMS := SessionANT.LinearForms.«MINKOWSKI_LINEAR_FORMS»
  MONO_EXISTS := Session.MONO_EXISTS
  NOETHERIAN_RING_INDUCT := SessionANT.IdealArith.«NOETHERIAN_RING_INDUCT»
  NORM_POS_LE := SessionMultiLib.Vectors.«NORM_POS_LE»
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NUMBER_FIELD_DEGREE_EQ_1 := SessionANT.Numfield.«NUMBER_FIELD_DEGREE_EQ_1»
  NUMBER_FIELD_DEGREE_POS := SessionANT.Numfield.«NUMBER_FIELD_DEGREE_POS»
  NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS := SessionANT.InfinitePlaces.«NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS»
  NUMBER_FIELD_DISCRIMINANT_NONZERO := SessionANT.Discriminant.«NUMBER_FIELD_DISCRIMINANT_NONZERO»
  NUMBER_FIELD_IDEAL_NORM_MUL_Q := SessionANT.NormIndex.«NUMBER_FIELD_IDEAL_NORM_MUL_Q»
  NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS := SessionANT.InfinitePlaces.«NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_RAMIFIED_DISCRIMINANT := SessionANT.Ramification.«NUMBER_FIELD_RAMIFIED_DISCRIMINANT»
  NUM_OF_INT_OF_NUM := Session.NUM_OF_INT_OF_NUM
  PRIME_FACTOR := SessionLibrary.Prime.«PRIME_FACTOR»
/-- The core theorems minkowski_theory.ml uses. -/
def core2 : HolANT.MinkowskiTheory.CoreThms2 where
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRODUCT_CONST := SessionLibrary.Products.«PRODUCT_CONST»
  PRODUCT_DELETE := SessionLibrary.Products.«PRODUCT_DELETE»
  PRODUCT_IMAGE := SessionLibrary.Products.«PRODUCT_IMAGE»
  PRODUCT_LE := SessionLibrary.Products.«PRODUCT_LE»
  PRODUCT_MUL := SessionLibrary.Products.«PRODUCT_MUL»
  PRODUCT_POS_LT := SessionLibrary.Products.«PRODUCT_POS_LT»
  PRODUCT_RESTRICT_SET := SessionLibrary.Products.«PRODUCT_RESTRICT_SET»
  PROPER_IDEAL_ALT := SessionLibrary.RingTheory.«PROPER_IDEAL_ALT»
  PSUBSET := Session.PSUBSET
  QUADRATIC_FIELD_DISCRIMINANT := SessionANT.Quadratic.«QUADRATIC_FIELD_DISCRIMINANT»
  QUADRATIC_FIELD_SQRT := SessionANT.Quadratic.«QUADRATIC_FIELD_SQRT»
  RE := SessionMultiLib.ComplexAlgebra.«RE»
  REAL_ABS_MUL := Session.REAL_ABS_MUL
  REAL_ABS_NZ := Session.REAL_ABS_NZ
  REAL_ADD_LDISTRIB := Session.REAL_ADD_LDISTRIB
  REAL_EQ_ADD_LCANCEL := Session.REAL_EQ_ADD_LCANCEL
  REAL_EQ_ADD_RCANCEL := Session.REAL_EQ_ADD_RCANCEL
  REAL_EQ_INV2 := Session.REAL_EQ_INV2
  REAL_INV_LE_1 := Session.REAL_INV_LE_1
  REAL_LET_TRANS := Session.REAL_LET_TRANS
  REAL_LE_ADD := Session.REAL_LE_ADD
  REAL_LE_ANTISYM := Session.REAL_LE_ANTISYM
  REAL_LE_INV := Session.REAL_LE_INV
  REAL_LE_INV_EQ := Session.REAL_LE_INV_EQ
  REAL_LE_LMUL := Session.REAL_LE_LMUL
  REAL_LE_LMUL_EQ := Session.REAL_LE_LMUL_EQ
  REAL_LE_MUL2 := Session.REAL_LE_MUL2
  REAL_LE_POW2 := Session.REAL_LE_POW2
  REAL_LE_REFL := Session.REAL_LE_REFL
  REAL_LE_TRANS := Session.REAL_LE_TRANS
  REAL_LT_IMP_LE := Session.REAL_LT_IMP_LE
  REAL_LT_INV_EQ := Session.REAL_LT_INV_EQ
  REAL_LT_MUL := Session.REAL_LT_MUL
  REAL_LT_RMUL := Session.REAL_LT_RMUL
  REAL_MUL_AC := Session.REAL_MUL_AC
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_RID := Session.REAL_MUL_RID
  REAL_MUL_RINV := Session.REAL_MUL_RINV
  REAL_MUL_SYM := Session.REAL_MUL_SYM
  REAL_NOT_LE := Session.REAL_NOT_LE
  REAL_NOT_LT := Session.REAL_NOT_LT
  REAL_OF_INT_CLAUSES := Session.REAL_OF_INT_CLAUSES
  REAL_OF_NUM_EQ := Session.REAL_OF_NUM_EQ
  REAL_OF_NUM_LE := Session.REAL_OF_NUM_LE
  REAL_OF_NUM_LT := Session.REAL_OF_NUM_LT
  REAL_OF_NUM_MUL := Session.REAL_OF_NUM_MUL
  REAL_POS := Session.REAL_POS
  REAL_POW_EQ := Session.REAL_POW_EQ
  REAL_POW_INV := Session.REAL_POW_INV
  REAL_POW_LE := Session.REAL_POW_LE
  REAL_POW_LE2 := Session.REAL_POW_LE2
  REAL_POW_LE_1 := Session.REAL_POW_LE_1
  REAL_POW_LT := Session.REAL_POW_LT
  REAL_POW_NZ := Session.REAL_POW_NZ
  REAL_POW_ONE := Session.REAL_POW_ONE
  REAL_POW_POW := Session.REAL_POW_POW
  REAL_POW_ROOT := SessionMultiLib.Transcendentals.«REAL_POW_ROOT»
  REAL_RING_CLAUSES := SessionLibrary.RingTheory.«REAL_RING_CLAUSES»
  REAL_RING_OF_INT := SessionLibrary.RingTheory.«REAL_RING_OF_INT»
  REAL_RING_SUM := SessionLibrary.RingTheory.«REAL_RING_SUM»
  RESTRICTION := Session.RESTRICTION
  RE_ADD := SessionMultiLib.ComplexAlgebra.«RE_ADD»
  RE_CNJ := SessionMultiLib.ComplexAlgebra.«RE_CNJ»
  RE_CX := SessionMultiLib.ComplexAlgebra.«RE_CX»
  RE_II := SessionMultiLib.ComplexAlgebra.«RE_II»
  RE_MUL_CX := SessionMultiLib.ComplexAlgebra.«RE_MUL_CX»
  RE_SUB := SessionMultiLib.ComplexAlgebra.«RE_SUB»
  RE_VSUM := SessionMultiLib.ComplexAlgebra.«RE_VSUM»
  RIGHT_EXISTS_IMP_THM := Session.RIGHT_EXISTS_IMP_THM
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RING_DET_EQ := SessionLibrary.RingDet.«RING_DET_EQ»
  RING_DET_HOMOMORPHISM := SessionLibrary.RingDet.«RING_DET_HOMOMORPHISM»
  RING_DET_I := SessionLibrary.RingDet.«RING_DET_I»
  RING_DET_MUL := SessionLibrary.RingDet.«RING_DET_MUL»
  RING_DET_SING := SessionLibrary.RingDet.«RING_DET_SING»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_CNJ := SessionMultiLib.ComplexRing.«RING_HOMOMORPHISM_CNJ»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_SUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM»
  RING_IDEAL_CARRIER := SessionLibrary.RingTheory.«RING_IDEAL_CARRIER»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_PROD := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PROD»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_INT_LINCOMB := SessionANT.Numfield.«RING_INT_LINCOMB»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE := SessionANT.ComplexEmbeddings.«RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_FREE := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE»
  RING_OF_INTEGERS_PRIME_SUBFIELD := SessionANT.Numfield.«RING_OF_INTEGERS_PRIME_SUBFIELD»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_1 := SessionLibrary.RingTheory.«RING_OF_INT_1»
  RING_OF_INT_EQ_0_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0_CHAR_0»
  RING_OF_INT_IN_RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INT_IN_RING_OF_INTEGERS»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_SUM_RING_OF_INTEGERS»
  RING_SUM_SING := SessionLibrary.RingTheory.«RING_SUM_SING»
  ROOT_POS_LT := SessionMultiLib.Transcendentals.«ROOT_POS_LT»
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SQRT_1 := Session.SQRT_1
  SQRT_POS_LT := Session.SQRT_POS_LT
  SQRT_UNIQUE := Session.SQRT_UNIQUE
  SUBGROUP_GENERATED_INC := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_INC»
  SUBGROUP_GENERATED_MONO := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_MONO»
  SUBGROUP_GENERATED_SUPERSET := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_SUPERSET»
  SUBSET := Session.SUBSET
  SUBSET_UNIV := Session.SUBSET_UNIV
  SUM_ADD := Session.SUM_ADD
  SUM_EQ := Session.SUM_EQ
  SUM_RMUL := Session.SUM_RMUL
  SUM_SWAP := Session.SUM_SWAP
  TRIVIAL_CLASS_GROUP := SessionANT.ClassgroupGroup.«TRIVIAL_CLASS_GROUP»
  TRIVIAL_GROUP_SUBGROUP_GENERATED_TRIVIAL := SessionLibrary.GroupTheory.«TRIVIAL_GROUP_SUBGROUP_GENERATED_TRIVIAL»
  VSUM_ADD := SessionMultiLib.Vectors.«VSUM_ADD»
  VSUM_COMPLEX_LMUL := SessionMultiLib.ComplexAlgebra.«VSUM_COMPLEX_LMUL»
  VSUM_COMPLEX_RMUL := SessionMultiLib.ComplexAlgebra.«VSUM_COMPLEX_RMUL»
  VSUM_DELTA := SessionMultiLib.Vectors.«VSUM_DELTA»
  VSUM_EQ := SessionMultiLib.Vectors.«VSUM_EQ»
  complex_embeddings := SessionANT.ComplexEmbeddings.«complex_embeddings»
  complex_mul := SessionMultiLib.ComplexAlgebra.«complex_mul»
  free_basis := SessionLibrary.RingDet.«free_basis»
  ideal_classes := SessionANT.Classgroup.«ideal_classes»
  ideal_norm := SessionANT.IdealNorm.«ideal_norm»
  int_isum := SessionLibrary.Isum.«int_isum»
  int_lattice := SessionANT.Zlattice.«int_lattice»
  int_mul_th := Session.int_mul_th
  num_INFINITE := Session.num_INFINITE
  num_divides := Session.num_divides
  number_field := SessionANT.Numfield.«number_field»
  o_THM := Session.o_THM
  principal_ideal := SessionLibrary.RingTheory.«principal_ideal»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_ideal := SessionLibrary.RingTheory.«ring_ideal»
  squarefree := SessionLibrary.Pocklington.«squarefree»

/-- What minkowski_theory.ml uses from Session. -/
def deps : HolANT.MinkowskiTheory.MinkowskiTheoryDeps where
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
  GROUP_RULE t := ExceptT.mk (SessionLibrary.GroupTheory.GROUP_RULE t)
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
  REAL_RING t := ExceptT.mk (Session.REAL_RING t)
  COMPLEX_RING t := ExceptT.mk (SessionMultiLib.ComplexAlgebra.COMPLEX_RING t)
  core1 := core1
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in minkowski_theory.ml order. -/
initialize BMinkowskiTheory01 : HolANT.MinkowskiTheory.MinkowskiTheory01 ←
  ioB "setupMinkowskiTheory01" (HolANT.MinkowskiTheory.setupMinkowskiTheory01 deps).run
initialize BMinkowskiTheory02 : HolANT.MinkowskiTheory.MinkowskiTheory02 ←
  ioB "setupMinkowskiTheory02" (HolANT.MinkowskiTheory.setupMinkowskiTheory02 deps BMinkowskiTheory01).run

-- MinkowskiTheory01
def NUMBER_FIELD_IDEAL_MINKOWSKI_LINEAR_FORMS : thm := BMinkowskiTheory01.NUMBER_FIELD_IDEAL_MINKOWSKI_LINEAR_FORMS
def NUMBER_FIELD_IDEAL_MINKOWSKI : thm := BMinkowskiTheory01.NUMBER_FIELD_IDEAL_MINKOWSKI
def NUMBER_FIELD_IDEAL_MINKOWSKI_NORM : thm := BMinkowskiTheory01.NUMBER_FIELD_IDEAL_MINKOWSKI_NORM
def NUMBER_FIELD_IDEAL_CLASS_MINKOWSKI : thm := BMinkowskiTheory01.NUMBER_FIELD_IDEAL_CLASS_MINKOWSKI

-- MinkowskiTheory02
def NUMBER_FIELD_CLASS_GROUP_MINKOWSKI : thm := BMinkowskiTheory02.NUMBER_FIELD_CLASS_GROUP_MINKOWSKI
def NUMBER_FIELD_PID_MINKOWSKI : thm := BMinkowskiTheory02.NUMBER_FIELD_PID_MINKOWSKI
def NUMBER_FIELD_DISCRIMINANT_DEGREE_1 : thm := BMinkowskiTheory02.NUMBER_FIELD_DISCRIMINANT_DEGREE_1
def NUMBER_FIELD_DISCRIMINANT_ABS_GT_1 : thm := BMinkowskiTheory02.NUMBER_FIELD_DISCRIMINANT_ABS_GT_1
def NUMBER_FIELD_RAMIFIED_PRIME_EXISTS : thm := BMinkowskiTheory02.NUMBER_FIELD_RAMIFIED_PRIME_EXISTS
def COMPLEX_NORM_POW_2_VSUM_FORM : thm := BMinkowskiTheory02.COMPLEX_NORM_POW_2_VSUM_FORM

/-- `needs "ANT/minkowski_theory.ml"`: already done by importing this module. -/
def ensureMinkowskiTheory : IO Unit := pure ()

end SessionANT.MinkowskiTheory
