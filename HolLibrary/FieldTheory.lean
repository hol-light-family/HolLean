/- ========================================================================= -/
/- Basic field theory, in particular some properties of field extensions.    -/
/- ========================================================================= -/
/- File: HolLibrary/FieldTheory.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/fieldtheory.ml`, by hand, in file
  order, in the style of HolLibrary/RingTheory.lean (see there and
  HolMath/Base.lean for the conventions).  fieldtheory.ml begins with
  `needs "Library/matroids.ml"` and `needs "Library/ringtheory.ml"`; the
  theorems it uses from them (and from the files they need) and from the core
  library are supplied via the CoreThms structures (SessionLibrary.FieldTheory
  fills them), and ringtheory.ml's RING_RULE, RING_TAC and FIELD_TAC via
  FieldTheoryDeps.  Each section, or part of a long section, is a bundle (a
  `structure`) built by a `setup` function; SessionLibrary/FieldTheory.lean
  builds the bundles in order and exports every name under its HOL Light
  name.  `ring_span` is made with `new_inductive_set`; RingTheory's `wPart`
  is the `W(MP_TAC o PART_MATCH ...)` idiom.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first (`let ... in` lemmas first, in text order).  Where one
  proof applies two or more rules that print or use counters (MESON,
  ARITH_RULE, SET_RULE, TAUT, RING_RULE) they are bound first, in OCaml's
  order.
-/

import HolLibrary.Matroids
import HolLibrary.RingTheory

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

open HolLibrary.RingTheory (wPart)

set_option maxRecDepth 8000

namespace HolLibrary.FieldTheory

-- @@COREFILL BEGIN
/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (AND_FORALL_THM ARITH_EQ CANTOR_THM_UNIV CARD_ADD_CONG CARD_DIFF_ABSORB
   CARD_DISJOINT_UNION CARD_EQ_IMAGE CARD_EQ_IMP_LE CARD_EQ_POLY_RING_FINITE
   CARD_EQ_REFL CARD_EQ_REFL_IMP CARD_EQ_SYM CARD_EQ_TRANS CARD_FINITE_CONG
   CARD_IMAGE_INJ CARD_LET_TRANS CARD_LE_ADDL CARD_LE_ADDR CARD_LE_ANTISYM
   CARD_LE_FINITE CARD_LE_FINITE_INFINITE CARD_LE_IMAGE CARD_LE_MUL
   CARD_LE_REFL CARD_LE_SUBSET CARD_LE_TRANS CARD_LE_UNIONS CARD_LE_UNIV
   CARD_LT_IMP_LE CARD_MUL2_ABSORB_LE CARD_MUL_FINITE CARD_MUL_FINITE_EQ
   CARD_MUL_LID CARD_MUL_LT_INFINITE CARD_MUL_RID CARD_NUMSEG CARD_NUMSEG_1
   CARD_PRIME_SUBRING CARD_PSUBSET CARD_SING_LE
   CARRIER_SUBRING_GENERATED_SUBRING CARRIER_SUBRING_OF COND_ID COND_RAND
   COND_RATOR CONJ_ACI CONJ_ASSOC CONJ_SYM CONTRAPOS_THM CROSS DELETE
   DE_MORGAN_THM DISJOINT EMPTY_SUBSET EMPTY_UNION EQ_IMP EQ_SYM_EQ ETA_AX
   ETA_ONE EXISTS_FINITE_SUBSET_IMAGE EXISTS_IN_GSPEC EXISTS_IN_IMAGE
   EXISTS_IN_INSERT EXISTS_IN_UNIONS EXISTS_PAIR_THM EXISTS_SUBSET_UNION EXP
   EXTENSION FIELD_EQ_ALL_UNITS FIELD_HOMOMORPHISM_DIV : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (FIELD_HOMOMORPHISM_INV FIELD_IMP_INTEGRAL_DOMAIN FIELD_IMP_NONTRIVIAL_RING
   FIELD_MUL_EQ_0 FIELD_MUL_LINV FIELD_MUL_RINV FIELD_NONTRIVIAL
   FIELD_POLY_RING FIELD_PRIME_SUBRING FIELD_QUOTIENT_RING
   FIELD_RING_HOMOMORPHISM_MONOMORPHISM FIELD_UNIT FINITE_1 FINITE_CROSS_EQ
   FINITE_DELETE FINITE_DIFF FINITE_EMPTY FINITE_HAS_SIZE FINITE_IMAGE
   FINITE_IMAGE_INJ_EQ FINITE_INDUCT_STRONG FINITE_INSERT
   FINITE_INTEGRAL_DOMAIN_EQ_FIELD FINITE_INTER FINITE_MONOMIAL_VARS_1
   FINITE_NUMSEG FINITE_NUMSEG_LE FINITE_NUMSEG_LT FINITE_PRIME_SUBRING
   FINITE_PRODUCT_DEPENDENT FINITE_RESTRICT FINITE_SING FINITE_SUBSET
   FINITE_SUBSET_NUMSEG FINITE_UNION FINITE_UNIONS
   FIRST_RING_ISOMORPHISM_THEOREM FORALL_AND_THM FORALL_FINITE_SUBSET_IMAGE
   FORALL_FUN_FROM_1 FORALL_IN_CROSS FORALL_IN_GSPEC FORALL_IN_IMAGE
   FORALL_IN_INSERT FORALL_IN_UNION FORALL_IN_UNIONS FORALL_PAIR_THM
   FORALL_UNWIND_THM1 FORALL_UNWIND_THM2 FROBENIUS_FIXED FST FUN_EQ_THM
   FUN_IN_IMAGE HAS_SIZE HAS_SIZE_FUNSPACE HAS_SIZE_IMAGE_INJ
   IDEAL_GENERATED_0 IDEAL_GENERATED_MINIMAL IDEAL_GENERATED_SING_EQ_CARRIER
   IMAGE_CLAUSES IMAGE_EQ_EMPTY IMAGE_I IMAGE_ID IMAGE_POLY_EVAL
   IMAGE_POLY_EXTEND IMAGE_POLY_EXTEND_1 IMAGE_SUBSET IMAGE_UNION
   IMAGE_UNIONS IMAGE_o : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms3 where
  (IMP_CONJ IMP_CONJ_ALT IMP_IMP INFINITE INFINITE_CARD_LE INJECTIVE_ON_ALT
   INJECTIVE_ON_LEFT_INVERSE INSERT_SUBSET INTEGRAL_DOMAIN_CHAR
   INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING INTEGRAL_DOMAIN_MUL_EQ_0
   INTEGRAL_DOMAIN_MUL_LCANCEL INTEGRAL_DOMAIN_MUL_RCANCEL
   INTEGRAL_DOMAIN_NONTRIVIAL INTEGRAL_DOMAIN_POLY_RING
   INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE INTEGRAL_DOMAIN_PRODUCT_EQ_0
   INTERS_2 INTERS_ANTIMONO INTERS_ANTIMONO_GEN INTERS_GSPEC INTER_SUBSET
   IN_CROSS IN_DELETE IN_DIFF IN_ELIM_THM IN_FLD IN_IDEAL_GENERATED_SING
   IN_IMAGE IN_INSERT IN_INTER IN_INTERS IN_NUMSEG IN_POLY_RING_CARRIER
   IN_POLY_RING_SUBRING_GENERATED_FINITARY IN_RING_POLYNOMIAL_CARRIER_COMPOSE
   IN_SING IN_SUBRING_0 IN_SUBRING_1 IN_SUBRING_ADD
   IN_SUBRING_GENERATED_FINITARY IN_SUBRING_MUL IN_SUBRING_NEG IN_SUBRING_POW
   IN_SUBRING_PRODUCT IN_SUBRING_SUB IN_SUBRING_SUM IN_UNION IN_UNIONS
   IN_UNIV ISOMORPHIC_RING_CARD_EQ ISOMORPHIC_RING_FIELDNESS
   ISOMORPHIC_SUBCOPY_OF_RING ISOMORPHIC_TRANSPORT_OF_RING I_DEF I_O_ID I_THM
   LAMBDA_PAIR_THM LEFT_AND_EXISTS_THM LEFT_IMP_EXISTS_THM LE_0 LE_REFL
   LE_SUC_LT LT LT_CASES MATROID_BASES_CARD_EQ MATROID_BASIS_EXISTS
   MATROID_DIMENSION_GE_FINITE_CARD MATROID_FINITE_DIMENSIONAL_ANY
   MATROID_INDEPENDENT_CARD_LE_SPANNING : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms4 where
  (MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE MATROID_INDEPENDENT_FINITARY
   MATROID_INDEPENDENT_INSERT MATROID_INDEPENDENT_MONO
   MATROID_MINIMALLY_DEPENDENT_SUBSET MATROID_SPANNING_ALT
   MATROID_SPANNING_CONTAINS_BASIS MATROID_SPAN_UNION_LEFT MAXIMAL_IDEAL_SING
   MAXIMAL_IMP_PRIME_IDEAL MAXIMAL_IMP_RING_IDEAL MEMBER_NOT_EMPTY
   MONOMIAL_DEG_LE_POLY_DEG MONOMIAL_DEG_UNIVARIATE MONOMIAL_VARS_UNIVARIATE
   MONO_AND MONO_EXISTS MONO_FORALL MONO_OR MUL_C_UNIV
   NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS NOT_EXISTS_THM NOT_FORALL_THM
   NOT_IMP NOT_INSERT_EMPTY NOT_IN_EMPTY NOT_LE NOT_LT NUMSEG_CLAUSES_LT
   PAIR_EQ PID PID_IMP_BEZOUT_RING PID_IMP_UFD PID_MAXIMAL_EQ_PRIME_IDEAL
   PID_POLY_RING POLY_0 POLY_CLAUSES POLY_COMPOSE_HOMOMORPHISM_CONST
   POLY_COMPOSE_HOMOMORPHISM_MUL POLY_COMPOSE_HOMOMORPHISM_SUB
   POLY_COMPOSE_HOMOMORPHISM_VAR POLY_CONST POLY_CONST_0 POLY_CONST_1
   POLY_CONST_EQ POLY_CONST_EQ_0 POLY_CONST_SUBRING_GENERATED POLY_DEG_0
   POLY_DEG_1 POLY_DEG_1_IMP_IRREDUCIBLE POLY_DEG_1_ROOT POLY_DEG_ADD
   POLY_DEG_CONST POLY_DEG_EQ_0 POLY_DEG_GE_EQ POLY_DEG_LE_EQ
   POLY_DEG_MONOMORPHIC_IMAGE POLY_DEG_MUL_X_MINUS_A POLY_DEG_UNIT
   POLY_DEG_X_MINUS_A POLY_DIVIDES_X_MINUS_ROOT POLY_DIVISION
   POLY_EQ_0_MONOMORPHIC_IMAGE POLY_EVAL POLY_EVAL_0 POLY_EVAL_1
   POLY_EVAL_ADD POLY_EVAL_CONST POLY_EVAL_HOMOMORPHIC_IMAGE POLY_EVAL_MUL : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms5 where
  (POLY_EVAL_RING_PRODUCT POLY_EVAL_SUB POLY_EVAL_VAR POLY_EXTEND
   POLY_EXTEND_1 POLY_EXTEND_ADD POLY_EXTEND_CONST POLY_EXTEND_EQ
   POLY_EXTEND_EVALUATE POLY_EXTEND_EXTEND POLY_EXTEND_FROM_SUBRING_GENERATED
   POLY_EXTEND_HOMOMORPHIC_IMAGE POLY_EXTEND_ID
   POLY_EXTEND_INTO_SUBRING_GENERATED POLY_EXTEND_MUL POLY_EXTEND_REINDEX
   POLY_EXTEND_SUB POLY_EXTEND_UNIVARIATE POLY_EXTEND_VAR
   POLY_MONOMIAL_IN_CARRIER POLY_MUL_0 POLY_MUL_CONST POLY_MUL_RID POLY_RING
   POLY_RING_CLAUSES POLY_RING_IN_FINITE_VARIABLES POLY_RING_MONO
   POLY_ROOT_BOUND POLY_ROOT_COUNT_IMP_SQUAREFREE POLY_SUBRING_GENERATED_1
   POLY_SUBRING_GENERATED_CLAUSES POLY_VAR_EQ_CONST POLY_VAR_UNIV
   POLY_X_MINUS_A_IN_CARRIER POLY_X_MINUS_A_NONZERO PRIME_SUBRING PSUBSET
   PSUBSET_ALT PSUBSET_TRANS QOSET_FLD QOSET_RESTRICT QUOTIENT_RING
   QUOTIENT_RING_0 RESTRICTION RIGHT_AND_EXISTS_THM RIGHT_AND_FORALL_THM
   RIGHT_EXISTS_AND_THM RIGHT_FORALL_IMP_THM RIGHT_IMP_FORALL_THM RINGS_EQ
   RING_0 RING_0_IN_SUBRING_GENERATED RING_1 RING_1_IN_SUBRING_GENERATED
   RING_ADD RING_ADD_ASSOC RING_ADD_IN_SUBRING_GENERATED RING_ADD_LDISTRIB
   RING_ADD_LNEG RING_ADD_LZERO RING_ADD_RNEG RING_ADD_RZERO RING_ADD_SYM
   RING_CARRIER_NONEMPTY RING_CARRIER_POLY_SUBRING_GENERATED
   RING_CARRIER_POLY_SUBRING_GENERATED_MONO RING_CARRIER_SUBRING_GENERATED_0
   RING_CARRIER_SUBRING_GENERATED_SUBSET RING_CHAR_FINITE RING_CHAR_UNIQUE : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms6 where
  (RING_COPRIME_00 RING_COPRIME_HOMOMORPHIC_IMAGE RING_COSET_EQ
   RING_COSET_EQ_IDEAL RING_DIRECT_LIMIT RING_DIV
   RING_DIVIDES_HOMOMORPHIC_IMAGE RING_DIVIDES_LMUL RING_DIVIDES_LMUL2
   RING_DIVIDES_REFL RING_DIVIDES_RMUL RING_DIVIDES_ZERO RING_DIV_1
   RING_EPIMORPHISM_RING_COSET RING_HOMOMORPHISM_0 RING_HOMOMORPHISM_1
   RING_HOMOMORPHISM_ADD RING_HOMOMORPHISM_BETWEEN_SUBRINGS
   RING_HOMOMORPHISM_COMPOSE RING_HOMOMORPHISM_EPIMORPHISM_FACTOR
   RING_HOMOMORPHISM_EQ RING_HOMOMORPHISM_ID
   RING_HOMOMORPHISM_IMAGE_PREIMAGE_EQ RING_HOMOMORPHISM_INCLUSION
   RING_HOMOMORPHISM_INTO_SUBRING RING_HOMOMORPHISM_INTO_SUBRING_EQ_GEN
   RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_NEG RING_HOMOMORPHISM_POLY_CONST
   RING_HOMOMORPHISM_POLY_EVAL RING_HOMOMORPHISM_POLY_EXTEND
   RING_HOMOMORPHISM_POLY_RINGS RING_HOMOMORPHISM_RING_COSET
   RING_HOMOMORPHISM_SUB RING_HOMOMORPHISM_SUM RING_IDEAL_RING_KERNEL
   RING_INV RING_INV_0 RING_INV_MUL RING_IRREDUCIBLE_IN_CARRIER
   RING_ISOMORPHISM RING_ISOMORPHISMS_ISOMORPHISM
   RING_ISOMORPHISMS_POLY_POLY_RING RING_ISOMORPHISMS_POLY_REINDEX
   RING_ISOMORPHISM_I RING_ISOMORPHISM_IMP_EPIMORPHISM
   RING_ISOMORPHISM_IMP_HOMOMORPHISM RING_ISOMORPHISM_IMP_ISOMORPHIC
   RING_ISOMORPHISM_IMP_MONOMORPHISM RING_ISOMORPHISM_MONOMORPHISM_ALT
   RING_ISOMORPHISM_ONTO_IMAGE RING_ISOMORPHISM_POLY_RING_TRIVIAL
   RING_KERNEL_0 RING_KERNEL_TO_SUBRING_GENERATED RING_LINV_UNIQUE
   RING_MONOMORPHISM RING_MONOMORPHISM_ALT RING_MONOMORPHISM_ALT_EQ
   RING_MONOMORPHISM_BETWEEN_SUBRINGS RING_MONOMORPHISM_COMPOSE
   RING_MONOMORPHISM_EQ RING_MONOMORPHISM_EQ_0 RING_MONOMORPHISM_FROBENIUS
   RING_MONOMORPHISM_FROM_SUBRING_GENERATED RING_MONOMORPHISM_I
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MONOMORPHISM_INCLUSION
   RING_MONOMORPHISM_INTO_SUBRING RING_MONOMORPHISM_POLY_RINGS RING_MUL : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms7 where
  (RING_MUL_ASSOC RING_MUL_IN_SUBRING_GENERATED RING_MUL_LID RING_MUL_LNEG
   RING_MUL_LZERO RING_MUL_RID RING_MUL_RINV RING_MUL_RZERO RING_MUL_SYM
   RING_NEG RING_NEG_EQ_0 RING_NEG_IN_SUBRING_GENERATED RING_OF_NUM_EQ_0
   RING_POLYNOMIAL RING_POLYNOMIAL_1 RING_POLYNOMIAL_ADD
   RING_POLYNOMIAL_COMPOSE RING_POLYNOMIAL_CONST
   RING_POLYNOMIAL_IMP_POWERSERIES RING_POLYNOMIAL_MUL RING_POLYNOMIAL_SUB
   RING_POLYNOMIAL_VAR RING_POW RING_POWERSERIES_CONST RING_POWERSERIES_SUB
   RING_POWERSERIES_VAR RING_POW_2 RING_POW_IN_SUBRING_GENERATED
   RING_POW_SUBRING_GENERATED RING_PRODUCT RING_PRODUCT_CLAUSES
   RING_PRODUCT_CLAUSES_NUMSEG RING_PRODUCT_CLAUSES_NUMSEG_ALT
   RING_PRODUCT_EQ RING_RINV_UNIQUE RING_SQUAREFREE_IMP_NONZERO
   RING_SQUAREFREE_IN_CARRIER RING_SUB RING_SUB_EQ_0 RING_SUB_RDISTRIB
   RING_SUB_REFL RING_SUB_RZERO RING_SUM RING_SUM_CASES RING_SUM_CLAUSES
   RING_SUM_CLOSED RING_SUM_EQ RING_SUM_EQ_0 RING_SUM_IMAGE RING_SUM_LMUL
   RING_SUM_RESTRICT_SET RING_SUM_RMUL RING_SUM_SING RING_SUM_SUB
   RING_SUM_SUM_PRODUCT RING_SUM_SUPERSET RING_UNIT_0
   RING_UNIT_NOT_IN_PRIME_IDEAL RING_UNIT_POLY_CONST RING_UNIT_POLY_DOMAIN
   SELECT_UNIQUE SIMPLE_IMAGE SIMPLE_IMAGE_GEN SING_SUBSET SKOLEM_THM SND
   SUBRING_GENERATED SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE
   SUBRING_GENERATED_BY_SUBRING_GENERATED SUBRING_GENERATED_EQ : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms8 where
  (SUBRING_GENERATED_IDEMPOT SUBRING_GENERATED_INC SUBRING_GENERATED_INC_GEN
   SUBRING_GENERATED_MINIMAL SUBRING_GENERATED_MONO
   SUBRING_GENERATED_RESTRICT SUBRING_GENERATED_RING_CARRIER
   SUBRING_GENERATED_SUBSET_CARRIER SUBRING_GENERATED_SUBSET_CARRIER_SUBSET
   SUBRING_GENERATED_UNION_LEFT SUBRING_GENERATED_UNION_RIGHT
   SUBRING_OF_HOMOMORPHIC_EQUALITIES SUBRING_OF_HOMOMORPHIC_IMAGE
   SUBRING_OF_HOMOMORPHIC_PREIMAGE SUBRING_OF_IMP_SUBSET SUBRING_OF_INTER
   SUBRING_OF_INTERS SUBRING_OF_UNIONS SUBRING_SUBRING_GENERATED SUBSET
   SUBSET_ANTISYM SUBSET_ANTISYM_EQ SUBSET_INTER SUBSET_REFL SUBSET_RESTRICT
   SUBSET_TRANS SUBSET_UNION SUBSET_UNIV SURJECTIVE_IFF_INJECTIVE
   SWAP_EXISTS_THM SWAP_FORALL_THM TRANSITIVE_STEPWISE_LT TRIVIAL_POLY_RING
   TRIVIAL_RING_10 TRIVIAL_RING_HAS_SIZE_1 TRIVIAL_RING_MONOMORPHIC_IMAGE_EQ
   TRIVIAL_RING_SUBRING_GENERATED UFD_PRIME_FACTOR_EXISTS UNIONS_GSPEC
   UNIONS_SUBSET UNION_ASSOC UNION_COMM UNION_EMPTY UNION_OVER_INTER
   UNION_SUBSET UNIV_1 UNIV_NOT_EMPTY WF_REC WF_num WLOG_LT ZL_STRONG
   ZL_SUBSETS_UNIONS_NONEMPTY chain coeff field integral_domain
   isomorphic_ring le_c matroid_basis matroid_dependent
   matroid_finite_dimensional matroid_independent matroid_set matroid_span
   matroid_spanning matroid_tybij mul_c num_INDUCTION num_INFINITE num_WF : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms9 where
  (num_WOP o_ASSOC o_DEF o_THM one poly_0 poly_const poly_eval poly_evaluate
   poly_vars prime_ideal principal_ideal proper_ideal qoset ring_0 ring_1
   ring_add ring_automorphism ring_carrier ring_div ring_divides
   ring_endomorphism ring_epimorphism ring_homomorphism ring_image
   ring_irreducible ring_isomorphism ring_isomorphisms ring_kernel
   ring_monomorphism ring_mul ring_neg ring_of_int ring_of_num
   ring_polynomial ring_pow ring_powerseries ring_prime ring_squarefree
   ring_sub ring_tybij ring_unit subring_of trivial_ring : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms10 where
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms11 where
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms12 where
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms13 where
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms14 where
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms15 where
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms16 where
  deriving Inhabited

-- @@COREFILL END

/-- What fieldtheory.ml uses from Session besides theorems. -/
structure FieldTheoryDeps where
  -- definitions and parser state
  new_definition : String → ExceptT String IO thm
  define : String → ExceptT String IO thm
  parse_as_infix : String × (Int × String) → IO Unit
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  ASM_METIS_TAC : List thm → tactic         -- meson.ml's ASM_METIS_TAC
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  INDUCT_TAC : tactic
  RING_TAC : tactic                         -- ringtheory.ml's RING_TAC (from RingTheory's RingRule bundle)
  -- ringtheory.ml's ring/field normalization tactics (SessionLibrary.RingTheory)
  FIELD_TAC : tactic
  -- inductive RELATION, returning (rules, induct, cases))
  new_inductive_set : term → IO (Except String (thm × thm × thm))
  -- `basic_ss` simpset builder (as in RingTheoryDeps)
  RING_RULE : term → ExceptT String IO thm
  basic_ss : List thm → IO (Except String HolCore.Simp.simpset)
  TAUT : term → ExceptT String IO thm           -- bool.ml's TAUT
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3
  core4 : CoreThms4
  core5 : CoreThms5
  core6 : CoreThms6
  core7 : CoreThms7
  core8 : CoreThms8
  core9 : CoreThms9
  core10 : CoreThms10
  core11 : CoreThms11
  core12 : CoreThms12
  core13 : CoreThms13
  core14 : CoreThms14
  core15 : CoreThms15
  core16 : CoreThms16

/- ------------------------------------------------------------------------- -/
/- Subfields. This does *not* build in the assumption that the overring r    -/
/- is itself a field, just that s is. For example Q is a subfield of R[x].   -/
/- (fieldtheory.ml 7-266)                                                    -/
/- ------------------------------------------------------------------------- -/

structure Subfields where
  -- @@FIELDS
  subfield_of : thm
  SUBFIELD_IMP_SUBRING_OF : thm
  SUBFIELD_OF_IMP_SUBSET : thm
  SUBFIELD_OF_IMP_10 : thm
  SUBFIELD_OF_IMP_NONTRIVIAL : thm
  IN_SUBFIELD_LINV : thm
  IN_SUBFIELD_RINV : thm
  IN_SUBFIELD_INV : thm
  RING_INV_SUBRING_GENERATED : thm
  SUBFIELD_OF_FIELD_INV : thm
  SUBFIELD_OF_INTERS : thm
  SUBFIELD_OF_INTER : thm
  CARRIER_SUBFIELD_OF : thm
  IN_SUBFIELD_0 : thm
  IN_SUBFIELD_1 : thm
  IN_SUBFIELD_NEG : thm
  IN_SUBFIELD_ADD : thm
  IN_SUBFIELD_MUL : thm
  IN_SUBFIELD_SUB : thm
  IN_SUBFIELD_POW : thm
  IN_SUBFIELD_SUM : thm
  IN_SUBFIELD_PRODUCT : thm
  SUBFIELD_OF_HOMOMORPHIC_EQUALITIES : thm
  SUBFIELD_OF_FIXPOINTS : thm
  SUBFIELD_OF_SUBRING_QUOTIENTS : thm
  deriving Inhabited

@[nospecialize]
def setupSubfields [HolBase] (D : FieldTheoryDeps) :
    ExceptT String IO Subfields := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, ASM_METIS_TAC, MESON_TAC, RING_TAC, SET_TAC, TAUT,
        new_definition, parse_as_infix, .. } := D
  let { CARRIER_SUBRING_GENERATED_SUBRING, CARRIER_SUBRING_OF, CONJ_ASSOC,
        EXISTS_IN_GSPEC, .. } := D.core1
  let { FIELD_HOMOMORPHISM_INV, FIELD_NONTRIVIAL, FIELD_UNIT, FORALL_IN_GSPEC,
        FORALL_IN_INSERT, .. } := D.core2
  let { IMP_CONJ, INTERS_2, IN_ELIM_THM, IN_INTERS, IN_SUBRING_0, IN_SUBRING_1,
        IN_SUBRING_ADD, IN_SUBRING_MUL, IN_SUBRING_NEG, IN_SUBRING_POW,
        IN_SUBRING_PRODUCT, IN_SUBRING_SUB, IN_SUBRING_SUM, .. } := D.core3
  let { MEMBER_NOT_EMPTY, MONO_EXISTS, NOT_IMP, NOT_INSERT_EMPTY, NOT_IN_EMPTY, .. } := D.core4
  let { RIGHT_FORALL_IMP_THM, RING_0, RING_1, .. } := D.core5
  let { RING_DIV, RING_DIV_1, RING_HOMOMORPHISM_ID, RING_INV, RING_INV_0, RING_INV_MUL,
        RING_LINV_UNIQUE, .. } := D.core6
  let { RING_MUL_LZERO, RING_MUL_RINV, RING_MUL_SYM, RING_RINV_UNIQUE,
        SUBRING_GENERATED, .. } := D.core7
  let { SUBRING_GENERATED_RING_CARRIER, SUBRING_OF_HOMOMORPHIC_EQUALITIES,
        SUBRING_OF_IMP_SUBSET, SUBRING_OF_INTERS, SUBSET, TRIVIAL_RING_10, field, .. } := D.core8
  let { ring_div, ring_endomorphism, subring_of, .. } := D.core9
  -- @@SCOPE END

  parse_as_infix ("subfield_of", (12, "right"))

  let subfield_of ← new_definition
   r"(s:A->bool) subfield_of (r:A ring) <=>
    s subring_of r /\ field(subring_generated r s)"

  let SUBFIELD_IMP_SUBRING_OF ← prove
   r"!r s:A->bool. s subfield_of r ==> s subring_of r"
   (SIMP_TAC [subfield_of])

  let SUBFIELD_OF_IMP_SUBSET ← prove
   r"!r s:A->bool. s subfield_of r ==> s SUBSET ring_carrier r"
   (SIMP_TAC [subring_of, subfield_of])

  let SUBFIELD_OF_IMP_10 ← prove
   r"!(r:A ring) s. s subfield_of r ==> ~(ring_1 r = ring_0 r)"
   (SIMP_TAC [subfield_of, field, SUBRING_GENERATED])

  let SUBFIELD_OF_IMP_NONTRIVIAL ← prove
   r"!(r:A ring) s. s subfield_of r ==> ~trivial_ring r"
   (REWRITE_TAC [TRIVIAL_RING_10, SUBFIELD_OF_IMP_10])

  let IN_SUBFIELD_LINV ← prove
   r"!r s x:A. s subfield_of r /\ x IN s /\ ~(x = ring_0 r)
               ==> ring_inv r x IN s /\ ring_mul r x (ring_inv r x) = ring_1 r"
   (REPEAT GEN_TAC THEN REWRITE_TAC [subfield_of, field, ← GSYM CONJ_ASSOC] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING] THEN
    REWRITE_TAC [← CONJUNCT2 SUBRING_GENERATED] THEN STRIP_TAC THEN
    ASM_METIS_TAC [RING_RINV_UNIQUE, SUBRING_OF_IMP_SUBSET, SUBSET])

  let IN_SUBFIELD_RINV ← prove
   r"!r s x:A. s subfield_of r /\ x IN s /\ ~(x = ring_0 r)
               ==> ring_inv r x IN s /\ ring_mul r (ring_inv r x) x = ring_1 r"
   (MESON_TAC [IN_SUBFIELD_LINV, RING_MUL_SYM, SUBFIELD_OF_IMP_SUBSET, SUBSET])

  let IN_SUBFIELD_INV ← prove
   r"!r s x:A. s subfield_of r /\ x IN s ==> ring_inv r x IN s"
   (REPEAT STRIP_TAC THEN
    ASM_MESON_TAC [IN_SUBFIELD_LINV, RING_INV_0, IN_SUBRING_0, subfield_of])

  let RING_INV_SUBRING_GENERATED ← prove
   r"!r s x:A.
          s subfield_of r /\ x IN s /\ ~(x = ring_0 r)
          ==> ring_inv (subring_generated r s) x = ring_inv r x"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_LINV_UNIQUE THEN
    ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING, SUBFIELD_IMP_SUBRING_OF,
                 ← CONJUNCT2 SUBRING_GENERATED] THEN
    ASM_MESON_TAC [IN_SUBFIELD_RINV])

  let SUBFIELD_OF_FIELD_INV ← prove
   r"!k (s:A->bool).
          field k /\ s subring_of k /\
          (!x. x IN s ==> ring_inv k x IN s)
          ==> s subfield_of k"
   (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [subfield_of] THEN
    ASM_SIMP_TAC [field, ← CONJUNCT2 SUBRING_GENERATED, FIELD_NONTRIVIAL,
                 CARRIER_SUBRING_GENERATED_SUBRING] THEN
    X_GEN_TAC (← q "x:A") THEN STRIP_TAC THEN EXISTS_TAC (← q "ring_inv k x:A") THEN
    ASM_SIMP_TAC [] THEN MATCH_MP_TAC RING_MUL_RINV THEN
    ASM_SIMP_TAC [FIELD_UNIT] THEN ASM_MESON_TAC [subring_of, SUBSET])

  let SUBFIELD_OF_INTERS ← prove
   r"!r (gs:(A->bool)->bool).
          (!g. g IN gs ==> g subfield_of r) /\ ~(gs = {})
          ==> (INTERS gs) subfield_of r"
   (REPEAT GEN_TAC THEN REWRITE_TAC [subfield_of] THEN
    SIMP_TAC [SUBRING_OF_INTERS, field, CARRIER_SUBRING_GENERATED_SUBRING,
             ← CONJUNCT2 SUBRING_GENERATED] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    X_GEN_TAC (← q "x:A") THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q "g:A->bool")) THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q "g:A->bool")) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, REWRITE_TAC [IMP_CONJ]] THEN
    SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING] THEN
    DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN (MP_TAC o SPEC (← q "x:A")) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q "y:A") THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [IN_INTERS] THEN X_GEN_TAC (← q "h:A->bool") THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q "h:A->bool")) THEN
    ASM_SIMP_TAC [IMP_CONJ, CARRIER_SUBRING_GENERATED_SUBRING] THEN
    DISCH_TAC THEN DISCH_THEN (MP_TAC o SPEC (← q "x:A")) THEN
    ASM SET_TAC [RING_RINV_UNIQUE, SUBRING_OF_IMP_SUBSET])

  let SUBFIELD_OF_INTER ← prove
   r"!r g h:A->bool.
          g subfield_of r /\ h subfield_of r ==> (g INTER h) subfield_of r"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM INTERS_2] THEN
    MATCH_MP_TAC SUBFIELD_OF_INTERS THEN
    ASM_REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY, NOT_INSERT_EMPTY])

  let CARRIER_SUBFIELD_OF ← prove
   r"!r:A ring. ring_carrier r subfield_of r <=> field r"
   (REWRITE_TAC [subfield_of, CARRIER_SUBRING_OF] THEN
    REWRITE_TAC [SUBRING_GENERATED_RING_CARRIER])

  let IN_SUBFIELD_0 ← prove
   r"!r h:A->bool. h subfield_of r ==> ring_0 r IN h"
   (SIMP_TAC [subfield_of, IN_SUBRING_0])

  let IN_SUBFIELD_1 ← prove
   r"!r h:A->bool. h subfield_of r ==> ring_1 r IN h"
   (SIMP_TAC [subfield_of, IN_SUBRING_1])

  let IN_SUBFIELD_NEG ← prove
   r"!r h x:A. h subfield_of r /\ x IN h ==> ring_neg r x IN h"
   (SIMP_TAC [subfield_of, IN_SUBRING_NEG])

  let IN_SUBFIELD_ADD ← prove
   r"!r h x y:A. h subfield_of r /\ x IN h /\ y IN h ==> ring_add r x y IN h"
   (SIMP_TAC [subfield_of, IN_SUBRING_ADD])

  let IN_SUBFIELD_MUL ← prove
   r"!r h x y:A. h subfield_of r /\ x IN h /\ y IN h ==> ring_mul r x y IN h"
   (SIMP_TAC [subfield_of, IN_SUBRING_MUL])

  let IN_SUBFIELD_SUB ← prove
   r"!r h x y:A. h subfield_of r /\ x IN h /\ y IN h ==> ring_sub r x y IN h"
   (SIMP_TAC [subfield_of, IN_SUBRING_SUB])

  let IN_SUBFIELD_POW ← prove
   r"!r h (x:A) n. h subfield_of r /\ x IN h ==> ring_pow r x n IN h"
   (SIMP_TAC [subfield_of, IN_SUBRING_POW])

  let IN_SUBFIELD_SUM ← prove
   r"!r h (f:K->A) s.
          h subfield_of r /\ (!a. a IN s ==> f a IN h) ==> ring_sum r s f IN h"
   (SIMP_TAC [subfield_of, IN_SUBRING_SUM])

  let IN_SUBFIELD_PRODUCT ← prove
   r"!r h (f:K->A) s.
        h subfield_of r /\ (!a. a IN s ==> f a IN h) ==> ring_product r s f IN h"
   (SIMP_TAC [subfield_of, IN_SUBRING_PRODUCT])

  let SUBFIELD_OF_HOMOMORPHIC_EQUALITIES ← prove
   r"!k l (f:A->B) g.
          field k /\ field l /\
          ring_homomorphism(k,l) f /\ ring_homomorphism(k,l) g
          ==> {x | x IN ring_carrier k /\ f x = g x} subfield_of k"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_OF_FIELD_INV THEN
    ASM_REWRITE_TAC [IN_ELIM_THM] THEN
    ASM SET_TAC [FIELD_HOMOMORPHISM_INV, SUBRING_OF_HOMOMORPHIC_EQUALITIES,
                RING_INV])

  let SUBFIELD_OF_FIXPOINTS ← prove
   r"!k (f:A->A).
          field k /\ ring_endomorphism k f
          ==> {x | x IN ring_carrier k /\ f x = x} subfield_of k"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_OF_HOMOMORPHIC_EQUALITIES THEN
    ASM_MESON_TAC [RING_HOMOMORPHISM_ID, ring_endomorphism])

  let SUBFIELD_OF_SUBRING_QUOTIENTS ← prove
   r"!r s:A->bool.
          ~(trivial_ring r) /\ s subring_of r /\
          (!x. x IN s /\ ~(x = ring_0 r) ==> ring_unit r x)
          ==> { ring_div r x y | x,y | x IN s /\ y IN s /\ ~(y = ring_0 r) }
              subfield_of r"
   (← do
    let t2 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    let t1 ← TAUT (← q r"p /\ q <=> ~(p ==> ~q)")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [subfield_of] THEN
    ONCE_REWRITE_TAC [t1] THEN
    SIMP_TAC [field, CARRIER_SUBRING_GENERATED_SUBRING] THEN
    REWRITE_TAC [NOT_IMP, SUBRING_GENERATED] THEN REWRITE_TAC [subring_of] THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, SUBSET] THEN
    REWRITE_TAC [FORALL_IN_GSPEC, EXISTS_IN_GSPEC] THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [subring_of]) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [SUBSET, TRIVIAL_RING_10]) THEN
    SUBGOAL_THEN
     (← q r"!x:A. x IN s /\ ~(x = ring_0 r) ==> ring_mul r x (ring_inv r x) = ring_1 r")
    (LABEL_TAC "*") THENL [ASM_MESON_TAC [RING_MUL_RINV], ALL_TAC] THEN
    ASM_REWRITE_TAC [IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC [RING_DIV],
      MAP_EVERY EXISTS_TAC [(← q "ring_0 r:A"), (← q "ring_1 r:A")] THEN
      ASM_SIMP_TAC [RING_DIV_1, RING_0],
      MAP_EVERY EXISTS_TAC [(← q "ring_1 r:A"), (← q "ring_1 r:A")] THEN
      ASM_SIMP_TAC [RING_DIV_1, RING_1],
      MAP_EVERY X_GEN_TAC [(← q "a:A"), (← q "b:A")] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [(← q "ring_neg r a:A"), (← q "b:A")] THEN
      ASM_SIMP_TAC [ring_div] THEN RING_TAC THEN ASM SET_TAC [RING_INV],
      MAP_EVERY X_GEN_TAC [(← q "a:A"), (← q "b:A")] THEN STRIP_TAC THEN
      MAP_EVERY X_GEN_TAC [(← q "c:A"), (← q "d:A")] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC
       [(← q "ring_add r (ring_mul r a d) (ring_mul r b c):A"),
        (← q "ring_mul r b d:A")] THEN
      ASM_SIMP_TAC [ring_div, RING_INV_MUL] THEN REMOVE_THEN "*"
       (fun th => tactic_of do
         pure (MP_TAC (← SPEC (← q "d:A") th) THEN MP_TAC (← SPEC (← q "b:A") th))) THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC (← q r"~(ring_1 r:A = ring_0 r)") THEN
      RING_TAC THEN ASM_SIMP_TAC [RING_INV],
      MAP_EVERY X_GEN_TAC [(← q "a:A"), (← q "b:A")] THEN STRIP_TAC THEN
      MAP_EVERY X_GEN_TAC [(← q "c:A"), (← q "d:A")] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC
       [(← q "ring_mul r a c:A"), (← q "ring_mul r b d:A")] THEN
      ASM_SIMP_TAC [ring_div, RING_INV_MUL] THEN REMOVE_THEN "*"
       (fun th => tactic_of do
         pure (MP_TAC (← SPEC (← q "d:A") th) THEN MP_TAC (← SPEC (← q "b:A") th))) THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC (← q r"~(ring_1 r:A = ring_0 r)") THEN
      RING_TAC THEN ASM_SIMP_TAC [RING_INV],
      MAP_EVERY X_GEN_TAC [(← q "a:A"), (← q "b:A")] THEN STRIP_TAC THEN
      REWRITE_TAC [ring_div] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [(← q "b:A"), (← q "a:A")] THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC t2 THEN CONJ_TAC THENL
       [ASM_MESON_TAC [RING_INV, RING_MUL_LZERO], DISCH_TAC] THEN
      REMOVE_THEN "*"
       (fun th => tactic_of do
         pure (MP_TAC (← SPEC (← q "b:A") th) THEN MP_TAC (← SPEC (← q "a:A") th))) THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN DISCH_TAC THEN
      RING_TAC THEN ASM_SIMP_TAC [RING_INV]]))

  -- @@RETURN BEGIN
  return { subfield_of, SUBFIELD_IMP_SUBRING_OF, SUBFIELD_OF_IMP_SUBSET,
           SUBFIELD_OF_IMP_10, SUBFIELD_OF_IMP_NONTRIVIAL, IN_SUBFIELD_LINV,
           IN_SUBFIELD_RINV, IN_SUBFIELD_INV, RING_INV_SUBRING_GENERATED,
           SUBFIELD_OF_FIELD_INV, SUBFIELD_OF_INTERS, SUBFIELD_OF_INTER,
           CARRIER_SUBFIELD_OF, IN_SUBFIELD_0, IN_SUBFIELD_1, IN_SUBFIELD_NEG,
           IN_SUBFIELD_ADD, IN_SUBFIELD_MUL, IN_SUBFIELD_SUB, IN_SUBFIELD_POW,
           IN_SUBFIELD_SUM, IN_SUBFIELD_PRODUCT, SUBFIELD_OF_HOMOMORPHIC_EQUALITIES,
           SUBFIELD_OF_FIXPOINTS, SUBFIELD_OF_SUBRING_QUOTIENTS }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Subfields generated by a set, totalized to whole ring in trivial case.    -/
/- (fieldtheory.ml 268-446)                                                  -/
/- ------------------------------------------------------------------------- -/

structure SubfieldGenerated where
  -- @@FIELDS
  subfield_generated : thm
  SUBFIELD_GENERATED : thm
  CARRIER_SUBFIELD_GENERATED_FIELD : thm
  CARRIER_SUBFIELD_GENERATED_SUBFIELD : thm
  RING_CARRIER_SUBFIELD_GENERATED_SUBSET : thm
  SUBFIELD_GENERATED_RESTRICT : thm
  SUBFIELD_GENERATED_MONO : thm
  SUBFIELD_GENERATED_MINIMAL : thm
  SUBRING_SUBSET_SUBFIELD_GENERATED : thm
  SUBRING_SUBFIELD_GENERATED : thm
  SUBFIELD_GENERATED_TRIVIAL : thm
  SUBRING_EQ_SUBFIELD_GENERATED : thm
  SUBRING_GENERATED_BY_SUBFIELD_GENERATED : thm
  SUBFIELD_GENERATED_SUBSET_CARRIER : thm
  SUBFIELD_SUBFIELD_GENERATED_ALT : thm
  SUBFIELD_SUBFIELD_GENERATED : thm
  FIELD_SUBFIELD_GENERATED_ALT : thm
  FIELD_SUBFIELD_GENERATED_EQ : thm
  SUBFIELD_SUBFIELD_GENERATED_EQ : thm
  FIELD_SUBFIELD_GENERATED : thm
  FIELD_SUBFIELD_GENERATED_MONO : thm
  SUBFIELD_GENERATED_EQ : thm
  SUBFIELDS_GENERATED_EQ : thm
  SUBFIELD_GENERATED_SUPERSET : thm
  FINITE_SUBFIELD_GENERATED : thm
  deriving Inhabited

@[nospecialize]
def setupSubfieldGenerated [HolBase] (D : FieldTheoryDeps) (BSubfields : Subfields) :
    ExceptT String IO SubfieldGenerated := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, TAUT, new_definition, .. } := D
  let { AND_FORALL_THM, CARRIER_SUBRING_OF, CONJ_ASSOC, .. } := D.core1
  let { FINITE_SUBSET, .. } := D.core2
  let { INTERS_ANTIMONO, INTERS_GSPEC, INTER_SUBSET, IN_ELIM_THM, .. } := D.core3
  let { MEMBER_NOT_EMPTY, NOT_EXISTS_THM, .. } := D.core4
  let { RINGS_EQ, RING_0, RING_1, RING_ADD, RING_ADD_ASSOC, RING_ADD_LDISTRIB,
        RING_ADD_LNEG, RING_ADD_LZERO, RING_ADD_SYM,
        RING_CARRIER_SUBRING_GENERATED_SUBSET, .. } := D.core5
  let { RING_MUL, .. } := D.core6
  let { RING_MUL_ASSOC, RING_MUL_LID, RING_MUL_SYM, RING_NEG, SUBRING_GENERATED,
        SUBRING_GENERATED_BY_SUBRING_GENERATED, .. } := D.core7
  let { SUBRING_GENERATED_MINIMAL, SUBRING_GENERATED_SUBSET_CARRIER,
        SUBRING_GENERATED_SUBSET_CARRIER_SUBSET, SUBRING_OF_INTERS,
        SUBRING_SUBRING_GENERATED, SUBSET, SUBSET_ANTISYM, SUBSET_ANTISYM_EQ,
        SUBSET_REFL, .. } := D.core8
  let { ring_0, ring_1, ring_add, ring_carrier, ring_mul, ring_neg, ring_tybij,
        subring_of, .. } := D.core9
  let { CARRIER_SUBFIELD_OF, SUBFIELD_OF_IMP_SUBSET, SUBFIELD_OF_INTERS, subfield_of, .. } := BSubfields
  -- @@SCOPE END

  let subfield_generated ← new_definition
   r"subfield_generated r (s:A->bool) =
        ring((if ?h. h subfield_of r /\ (ring_carrier r INTER s) SUBSET h then
              INTERS {h | h subfield_of r /\ (ring_carrier r INTER s) SUBSET h}
              else ring_carrier r),
             ring_0 r,ring_1 r,ring_neg r,ring_add r,ring_mul r)"

  let SUBFIELD_GENERATED ← prove
   r"(!r s:A->bool.
          ring_carrier (subfield_generated r s) =
            if ?h. h subfield_of r /\ (ring_carrier r INTER s) SUBSET h then
              INTERS {h | h subfield_of r /\ (ring_carrier r INTER s) SUBSET h}
              else ring_carrier r) /\
     (!r s:A->bool. ring_0 (subfield_generated r s) = ring_0 r) /\
     (!r s:A->bool. ring_1 (subfield_generated r s) = ring_1 r) /\
     (!r s:A->bool. ring_neg (subfield_generated r s) = ring_neg r) /\
     (!r s:A->bool. ring_add (subfield_generated r s) = ring_add r) /\
     (!r s:A->bool. ring_mul (subfield_generated r s) = ring_mul r)"
   (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
    MP_TAC (← EQ_IMP_RULE
     (← ISPEC (← liftExcept (do rand (← rand (strip_forall (concl subfield_generated)).2)))
       (← CONJUNCT2 ring_tybij))).1 THEN
    REWRITE_TAC [← GSYM subfield_generated] THEN ANTS_TAC THENL
     [ALL_TAC,
      DISCH_TAC THEN
      ASM_REWRITE_TAC [ring_carrier, ring_0, ring_1, ring_neg,
                      ring_add, ring_mul]] THEN
    REPLICATE_TAC 4 (GEN_REWRITE_TAC I [CONJ_ASSOC]) THEN CONJ_TAC THENL
     [COND_CASES_TAC THEN
      SIMP_TAC [RING_0, RING_1, RING_NEG, RING_ADD, RING_MUL] THEN
      REWRITE_TAC [INTERS_GSPEC, IN_ELIM_THM] THEN
      MESON_TAC [subfield_of, subring_of],
      ALL_TAC] THEN
    COND_CASES_TAC THENL
     [REWRITE_TAC [INTERS_GSPEC, IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (X_CHOOSE_THEN (← q "h:A->bool") STRIP_ASSUME_TAC) THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q "h:A->bool"))) THEN
      ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP SUBFIELD_OF_IMP_SUBSET) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [SUBSET]),
      ALL_TAC] THEN
    ASM_MESON_TAC [RING_ADD_SYM, RING_ADD_ASSOC, RING_ADD_LZERO, RING_ADD_LNEG,
      RING_MUL_SYM, RING_MUL_ASSOC, RING_MUL_LID, RING_ADD_LDISTRIB])

  let CARRIER_SUBFIELD_GENERATED_FIELD ← prove
   r"!r s:A->bool.
          field r
          ==> ring_carrier(subfield_generated r s) =
              INTERS {h | h subfield_of r /\ (ring_carrier r INTER s) SUBSET h}"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [SUBFIELD_GENERATED] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q "ring_carrier r:A->bool") o
      GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC [CARRIER_SUBFIELD_OF] THEN SET_TAC [])

  let CARRIER_SUBFIELD_GENERATED_SUBFIELD ← prove
   r"!r s:A->bool.
          s subfield_of r ==> ring_carrier(subfield_generated r s) = s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [SUBFIELD_GENERATED] THEN
    ASM SET_TAC [SUBFIELD_OF_IMP_SUBSET])

  let RING_CARRIER_SUBFIELD_GENERATED_SUBSET ← prove
   r"!r h:A->bool.
          ring_carrier (subfield_generated r h) SUBSET ring_carrier r"
   (REPEAT GEN_TAC THEN REWRITE_TAC [SUBFIELD_GENERATED] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [SUBSET_REFL] THEN
    ASM SET_TAC [SUBFIELD_OF_IMP_SUBSET])

  let SUBFIELD_GENERATED_RESTRICT ← prove
   r"!r s:A->bool.
          subfield_generated r s =
          subfield_generated r (ring_carrier r INTER s)"
   (← do
    let s1 ← SET_RULE (← q r"g INTER g INTER s = g INTER s")
    pure (REWRITE_TAC [subfield_generated, s1]))

  let SUBFIELD_GENERATED_MONO ← prove
   r"!r s t:A->bool.
          s SUBSET t
          ==> ring_carrier(subfield_generated r s) SUBSET
              ring_carrier(subfield_generated r t)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [SUBFIELD_GENERATED] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    TRY (MATCH_MP_TAC INTERS_ANTIMONO) THEN ASM SET_TAC [SUBFIELD_OF_IMP_SUBSET])

  let SUBFIELD_GENERATED_MINIMAL ← prove
   r"!r h s:A->bool.
          s SUBSET h /\ h subfield_of r
          ==> ring_carrier(subfield_generated r s) SUBSET h"
   (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [SUBFIELD_GENERATED] THEN
    ASM SET_TAC [SUBFIELD_OF_IMP_SUBSET])

  let SUBRING_SUBSET_SUBFIELD_GENERATED ← prove
   r"!r s:A->bool.
          ring_carrier(subring_generated r s) SUBSET
          ring_carrier(subfield_generated r s)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [SUBFIELD_GENERATED] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC [RING_CARRIER_SUBRING_GENERATED_SUBSET] THEN
    REWRITE_TAC [SUBRING_GENERATED] THEN MATCH_MP_TAC INTERS_ANTIMONO THEN
    REWRITE_TAC [subfield_of] THEN SET_TAC [])

  let SUBRING_SUBFIELD_GENERATED ← prove
   r"!r s:A->bool.
          ring_carrier(subfield_generated r s) subring_of r"
   (REPEAT GEN_TAC THEN REWRITE_TAC [SUBFIELD_GENERATED] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [CARRIER_SUBRING_OF] THEN
    MATCH_MP_TAC SUBRING_OF_INTERS THEN
    ASM_REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM] THEN
    SIMP_TAC [subfield_of])

  let SUBFIELD_GENERATED_TRIVIAL ← prove
   r"!r s:A->bool.
          ~(?h. h subfield_of r /\ ring_carrier r INTER s SUBSET h)
          ==> subfield_generated r s = r"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [RINGS_EQ, SUBFIELD_GENERATED])

  let SUBRING_EQ_SUBFIELD_GENERATED ← prove
   r"!r s:A->bool.
          field(subring_generated r s)
          ==> subring_generated r s = subfield_generated r s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [RINGS_EQ] THEN
    REWRITE_TAC [← CONJUNCT2 SUBRING_GENERATED, ← CONJUNCT2 SUBFIELD_GENERATED] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC [SUBRING_SUBSET_SUBFIELD_GENERATED] THEN
    ONCE_REWRITE_TAC [SUBFIELD_GENERATED_RESTRICT] THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN
    ASM_REWRITE_TAC [SUBRING_GENERATED_SUBSET_CARRIER, subfield_of] THEN
    ASM_REWRITE_TAC [SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
    REWRITE_TAC [SUBRING_SUBRING_GENERATED])

  let SUBRING_GENERATED_BY_SUBFIELD_GENERATED ← prove
   r"!r s:A->bool.
          subring_generated r (ring_carrier(subfield_generated r s)) =
          subfield_generated r s"
   (REPEAT GEN_TAC THEN REWRITE_TAC [RINGS_EQ] THEN
    REWRITE_TAC [← CONJUNCT2 SUBRING_GENERATED, ← CONJUNCT2 SUBFIELD_GENERATED] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN
      REWRITE_TAC [SUBRING_SUBFIELD_GENERATED, SUBSET_REFL],
      MATCH_MP_TAC SUBRING_GENERATED_SUBSET_CARRIER_SUBSET THEN
      REWRITE_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET]])

  let SUBFIELD_GENERATED_SUBSET_CARRIER ← prove
   r"!r h:A->bool.
       ring_carrier r INTER h SUBSET ring_carrier(subfield_generated r h)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [SUBFIELD_GENERATED] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [INTER_SUBSET] THEN ASM SET_TAC [])

  let SUBFIELD_SUBFIELD_GENERATED_ALT ← prove
   r"!r s:A->bool.
          ring_carrier(subfield_generated r s) subfield_of r <=>
          ?h. h subfield_of r /\ ring_carrier r INTER s SUBSET h"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [MESON_TAC [SUBFIELD_GENERATED_SUBSET_CARRIER], DISCH_TAC] THEN
    ASM_REWRITE_TAC [SUBFIELD_GENERATED] THEN
    MATCH_MP_TAC SUBFIELD_OF_INTERS THEN
    ASM_SIMP_TAC [← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM])

  let SUBFIELD_SUBFIELD_GENERATED ← prove
   r"!r s:A->bool.
          field r ==> ring_carrier(subfield_generated r s) subfield_of r"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [SUBFIELD_SUBFIELD_GENERATED_ALT] THEN
    EXISTS_TAC (← q "ring_carrier r:A->bool") THEN
    ASM_REWRITE_TAC [CARRIER_SUBFIELD_OF, INTER_SUBSET])

  let FIELD_SUBFIELD_GENERATED_ALT ← prove
   r"!r s:A->bool. field(subfield_generated r s) <=>
                   ?h. h subfield_of r /\ ring_carrier r INTER s SUBSET h"
   (REWRITE_TAC [← GSYM SUBFIELD_SUBFIELD_GENERATED_ALT] THEN
    REWRITE_TAC [subfield_of, SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    REWRITE_TAC [SUBRING_SUBFIELD_GENERATED])

  let FIELD_SUBFIELD_GENERATED_EQ ← prove
   r"!r s:A->bool.
          field(subfield_generated r s) <=>
          ring_carrier(subfield_generated r s) subfield_of r"
   (REWRITE_TAC [SUBFIELD_SUBFIELD_GENERATED_ALT, FIELD_SUBFIELD_GENERATED_ALT])

  let SUBFIELD_SUBFIELD_GENERATED_EQ ← prove
   r"!r s:A->bool.
          ring_carrier(subfield_generated r s) subfield_of r <=>
          field(subfield_generated r s)"
   (REWRITE_TAC [FIELD_SUBFIELD_GENERATED_EQ])

  let FIELD_SUBFIELD_GENERATED ← prove
   r"!r s:A->bool. field r ==> field(subfield_generated r s)"
   (MESON_TAC [SUBFIELD_SUBFIELD_GENERATED, subfield_of,
              SUBRING_GENERATED_BY_SUBFIELD_GENERATED])

  let FIELD_SUBFIELD_GENERATED_MONO ← prove
   r"!r s t:A->bool.
          s SUBSET t /\ field(subfield_generated r t)
          ==> field(subfield_generated r s)"
   (REWRITE_TAC [FIELD_SUBFIELD_GENERATED_ALT] THEN SET_TAC [])

  let SUBFIELD_GENERATED_EQ ← prove
   r"!r s:A->bool.
          subfield_generated r s = r <=>
          ring_carrier(subfield_generated r s) = ring_carrier r"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [RINGS_EQ] THEN
    REWRITE_TAC [← CONJUNCT2 SUBFIELD_GENERATED])

  let SUBFIELDS_GENERATED_EQ ← prove
   r"!r s:A->bool.
       (!h. h subfield_of r
            ==> (ring_carrier r INTER s SUBSET h <=>
                 ring_carrier r INTER t SUBSET h))
       ==> subfield_generated r s = subfield_generated r t"
   (← do
    let t1 ← TAUT (← q r"(p ==> (q <=> r)) <=> (p /\ q <=> p /\ r)")
    pure (REWRITE_TAC [t1] THEN
    SIMP_TAC [subfield_generated]))

  let SUBFIELD_GENERATED_SUPERSET ← prove
   r"!r s:A->bool.
      subfield_generated r s = r <=>
      ring_carrier r SUBSET ring_carrier(subfield_generated r s)"
   (REWRITE_TAC [SUBFIELD_GENERATED_EQ, ← GSYM SUBSET_ANTISYM_EQ] THEN
    REWRITE_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET])

  let FINITE_SUBFIELD_GENERATED ← prove
   r"!r s:A->bool.
          FINITE(ring_carrier r)
          ==> FINITE(ring_carrier(subfield_generated r s))"
   (MESON_TAC [FINITE_SUBSET, RING_CARRIER_SUBFIELD_GENERATED_SUBSET])

  -- @@RETURN BEGIN
  return { subfield_generated, SUBFIELD_GENERATED, CARRIER_SUBFIELD_GENERATED_FIELD,
           CARRIER_SUBFIELD_GENERATED_SUBFIELD, RING_CARRIER_SUBFIELD_GENERATED_SUBSET,
           SUBFIELD_GENERATED_RESTRICT, SUBFIELD_GENERATED_MONO,
           SUBFIELD_GENERATED_MINIMAL, SUBRING_SUBSET_SUBFIELD_GENERATED,
           SUBRING_SUBFIELD_GENERATED, SUBFIELD_GENERATED_TRIVIAL,
           SUBRING_EQ_SUBFIELD_GENERATED, SUBRING_GENERATED_BY_SUBFIELD_GENERATED,
           SUBFIELD_GENERATED_SUBSET_CARRIER, SUBFIELD_SUBFIELD_GENERATED_ALT,
           SUBFIELD_SUBFIELD_GENERATED, FIELD_SUBFIELD_GENERATED_ALT,
           FIELD_SUBFIELD_GENERATED_EQ, SUBFIELD_SUBFIELD_GENERATED_EQ,
           FIELD_SUBFIELD_GENERATED, FIELD_SUBFIELD_GENERATED_MONO,
           SUBFIELD_GENERATED_EQ, SUBFIELDS_GENERATED_EQ, SUBFIELD_GENERATED_SUPERSET,
           FINITE_SUBFIELD_GENERATED }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Subfield generated by a set, continued.  (fieldtheory.ml 448-644)         -/
/- ------------------------------------------------------------------------- -/

structure SubfieldGenerated1 where
  -- @@FIELDS
  SUBSET_CARRIER_SUBFIELD_GENERATED : thm
  SUBFIELD_GENERATED_MINIMAL_EQ : thm
  SUBFIELD_GENERATED_RING_CARRIER : thm
  SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET : thm
  SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED : thm
  SUBFIELD_GENERATED_REFL : thm
  SUBFIELD_GENERATED_INC : thm
  SUBFIELD_GENERATED_INC_GEN : thm
  SUBRING_OF_SUBFIELD_GENERATED_EQ : thm
  SUBFIELD_OF_SUBFIELD_GENERATED_EQ : thm
  SUBFIELD_OF_SUBFIELD_GENERATED_SUBFIELD_EQ : thm
  SUBFIELD_OF_SUBFIELD_GENERATED : thm
  SUBFIELD_OF_SUBFIELD_GENERATED_REV : thm
  SUBFIELD_GENERATED_IDEMPOT : thm
  SUBFIELD_GENERATED_SUBFIELD_GENERATED : thm
  SUBRING_GENERATED_SUBFIELD_GENERATED : thm
  TRIVIAL_RING_SUBFIELD_GENERATED : thm
  SUBFIELD_GENERATED_UNION_LEFT : thm
  SUBFIELD_GENERATED_UNION_RIGHT : thm
  SUBFIELD_GENERATED_UNION : thm
  deriving Inhabited

@[nospecialize]
def setupSubfieldGenerated1 [HolBase] (D : FieldTheoryDeps) (BSubfields : Subfields) (BSubfieldGenerated : SubfieldGenerated) :
    ExceptT String IO SubfieldGenerated1 := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, SET_RULE, SET_TAC, TAUT, .. } := D
  let { CARRIER_SUBRING_GENERATED_SUBRING, CONJ_ASSOC, CONTRAPOS_THM, .. } := D.core1
  let { IMP_CONJ, INTERS_ANTIMONO_GEN, INTER_SUBSET, IN_ELIM_THM, IN_INTER, .. } := D.core3
  let { RIGHT_FORALL_IMP_THM, RINGS_EQ, .. } := D.core5
  let { SUBRING_GENERATED, .. } := D.core7
  let { SUBRING_GENERATED_RING_CARRIER, SUBRING_OF_IMP_SUBSET, SUBRING_OF_INTER,
        SUBSET, SUBSET_ANTISYM, SUBSET_INTER, SUBSET_REFL, SUBSET_TRANS,
        TRIVIAL_RING_10, UNION_COMM, UNION_OVER_INTER, UNION_SUBSET, field, .. } := D.core8
  let { subring_of, .. } := D.core9
  let { SUBFIELD_OF_IMP_SUBSET, SUBFIELD_OF_INTER, subfield_of, .. } := BSubfields
  let { CARRIER_SUBFIELD_GENERATED_SUBFIELD, RING_CARRIER_SUBFIELD_GENERATED_SUBSET,
        SUBFIELDS_GENERATED_EQ, SUBFIELD_GENERATED, SUBFIELD_GENERATED_MINIMAL,
        SUBFIELD_GENERATED_RESTRICT, SUBFIELD_GENERATED_SUBSET_CARRIER,
        SUBFIELD_GENERATED_SUPERSET, SUBFIELD_GENERATED_TRIVIAL,
        SUBFIELD_SUBFIELD_GENERATED_ALT, SUBRING_SUBFIELD_GENERATED,
        SUBRING_SUBSET_SUBFIELD_GENERATED, .. } := BSubfieldGenerated
  -- @@SCOPE END

  let SUBSET_CARRIER_SUBFIELD_GENERATED ← prove
   r"!r s t:A->bool.
        s SUBSET ring_carrier r /\ s SUBSET t
        ==> s SUBSET ring_carrier(subfield_generated r t)"
   (MESON_TAC [SUBSET_TRANS, SUBSET_INTER, SUBFIELD_GENERATED_SUBSET_CARRIER])

  let SUBFIELD_GENERATED_MINIMAL_EQ ← prove
   r"!r h s:A->bool.
        h subfield_of r
        ==> (ring_carrier(subfield_generated r s) SUBSET h <=>
             ring_carrier r INTER s SUBSET h)"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] SUBSET_TRANS) THEN
      REWRITE_TAC [SUBFIELD_GENERATED_SUBSET_CARRIER],
      ONCE_REWRITE_TAC [SUBFIELD_GENERATED_RESTRICT] THEN
      ASM_SIMP_TAC [SUBFIELD_GENERATED_MINIMAL]])

  let SUBFIELD_GENERATED_RING_CARRIER ← prove
   r"!r:A ring. subfield_generated r (ring_carrier r) = r"
   (GEN_TAC THEN REWRITE_TAC [SUBFIELD_GENERATED_SUPERSET] THEN
    MESON_TAC [SUBRING_SUBSET_SUBFIELD_GENERATED, SUBRING_GENERATED_RING_CARRIER,
              SUBSET_TRANS])

  let SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET ← prove
   r"!r s:A->bool.
        s SUBSET ring_carrier r
        ==> s SUBSET ring_carrier(subfield_generated r s)"
   (MESON_TAC [SUBFIELD_GENERATED_SUBSET_CARRIER,
      ← SET_RULE (← q r"s SUBSET t <=> t INTER s = s")])

  let SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED ← prove
   r"!r s:A->bool.
        subfield_generated r (ring_carrier(subfield_generated r s)) =
        subfield_generated r s"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [RINGS_EQ, ← CONJUNCT2 SUBFIELD_GENERATED] THEN
    ASM_CASES_TAC
     (← q r"ring_carrier (subfield_generated r s:A ring) subfield_of r") THEN
    ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [SUBFIELD_SUBFIELD_GENERATED_ALT]) THEN
    ASM_SIMP_TAC [SUBFIELD_GENERATED_TRIVIAL, SUBFIELD_GENERATED_RING_CARRIER])

  let SUBFIELD_GENERATED_REFL ← prove
   r"!r s:A->bool. ring_carrier r SUBSET s ==> subfield_generated r s = r"
   (← do
    let s1 ← SET_RULE (← q r"u SUBSET s ==> u INTER s = u")
    pure (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [SUBFIELD_GENERATED_RESTRICT] THEN
    ASM_SIMP_TAC [s1] THEN
    REWRITE_TAC [SUBFIELD_GENERATED_RING_CARRIER]))

  let SUBFIELD_GENERATED_INC ← prove
   r"!r s x:A.
        s SUBSET ring_carrier r /\ x IN s
        ==> x IN ring_carrier(subfield_generated r s)"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, ← GSYM SUBSET] THEN
    REWRITE_TAC [SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET])

  let SUBFIELD_GENERATED_INC_GEN ← prove
   r"!r s x:A.
        x IN ring_carrier r /\ x IN s
        ==> x IN ring_carrier(subfield_generated r s)"
   (MESON_TAC [SUBFIELD_GENERATED_SUBSET_CARRIER, IN_INTER, SUBSET])

  let SUBRING_OF_SUBFIELD_GENERATED_EQ ← prove
   r"!r h k:A->bool.
        h subring_of (subfield_generated r k) <=>
        h subring_of r /\ h SUBSET ring_carrier(subfield_generated r k)"
   (← do
    let t1 ← TAUT (← q r"(p ==> r) /\ (r ==> (p <=> q)) ==> (p <=> q /\ r)")
    pure (REPEAT GEN_TAC THEN
    MATCH_MP_TAC t1 THEN
    REWRITE_TAC [SUBRING_OF_IMP_SUBSET] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [subring_of, ← CONJUNCT2 SUBFIELD_GENERATED] THEN
    ASM SET_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET]))

  let SUBFIELD_OF_SUBFIELD_GENERATED_EQ ← prove
   r"!r h k:A->bool.
        h subfield_of (subfield_generated r k) <=>
        h subfield_of r /\ h SUBSET ring_carrier(subfield_generated r k)"
   (← do
    let t1 ← TAUT
      (← q r"((p /\ q) /\ r <=> (p /\ s) /\ q) <=> (p /\ q ==> (r <=> s))")
    pure (REPEAT GEN_TAC THEN
    REWRITE_TAC [subfield_of, SUBRING_OF_SUBFIELD_GENERATED_EQ] THEN
    REWRITE_TAC [t1] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(h:A->bool) subring_of (subfield_generated r k)")
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC [SUBRING_OF_SUBFIELD_GENERATED_EQ],
      ASM_SIMP_TAC [field, ← CONJUNCT2 SUBFIELD_GENERATED, ← CONJUNCT2
                   SUBRING_GENERATED] THEN
      ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING]]))

  let SUBFIELD_OF_SUBFIELD_GENERATED_SUBFIELD_EQ ← prove
   r"!r h k:A->bool.
        k subfield_of r
        ==> (h subfield_of (subfield_generated r k) <=>
             h subfield_of r /\ h SUBSET k)"
   (REWRITE_TAC [SUBFIELD_OF_SUBFIELD_GENERATED_EQ] THEN
    SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD])

  let SUBFIELD_OF_SUBFIELD_GENERATED ← prove
   r"!r g h:A->bool.
        g subfield_of r /\ g SUBSET h
        ==> g subfield_of (subfield_generated r h)"
   (SIMP_TAC [SUBFIELD_OF_SUBFIELD_GENERATED_EQ] THEN
    SET_TAC [SUBFIELD_OF_IMP_SUBSET, SUBFIELD_GENERATED_SUBSET_CARRIER])

  let SUBFIELD_OF_SUBFIELD_GENERATED_REV ← prove
   r"!r g h:A->bool.
        g subfield_of (subfield_generated r h)
        ==> g subfield_of r"
   (SIMP_TAC [SUBFIELD_OF_SUBFIELD_GENERATED_EQ])

  let SUBFIELD_GENERATED_IDEMPOT ← prove
   r"!r s:A->bool.
        subfield_generated (subfield_generated r s) s =
        subfield_generated r s"
   (← do
    let g3 ← ONCE_REWRITE_RULE [← GSYM CONTRAPOS_THM] SUBFIELD_GENERATED_TRIVIAL
    let t2 ← TAUT (← q r"(~p ==> p) ==> p")
    let g1 ← ONCE_REWRITE_RULE [← GSYM CONTRAPOS_THM] SUBFIELD_GENERATED_TRIVIAL
    pure (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"subfield_generated r s:A ring = r") THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP g1) THEN
    REWRITE_TAC [] THEN DISCH_TAC THEN
    MATCH_MP_TAC t2 THEN
    DISCH_THEN (MP_TAC o MATCH_MP g3) THEN
    REWRITE_TAC [] THEN DISCH_TAC THEN
    REWRITE_TAC [RINGS_EQ, ← CONJUNCT2 SUBFIELD_GENERATED] THEN
    ONCE_REWRITE_TAC [SUBFIELD_GENERATED] THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
    MATCH_MP_TAC INTERS_ANTIMONO_GEN THEN X_GEN_TAC (← q r"h:A->bool") THEN
    REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THENL
     [FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"j:A->bool") MP_TAC) THEN
      REWRITE_TAC [SUBFIELD_OF_SUBFIELD_GENERATED_EQ] THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"h INTER j:A->bool") THEN ASM_SIMP_TAC [SUBFIELD_OF_INTER] THEN
      ASM SET_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET],
      EXISTS_TAC (← q r"h:A->bool") THEN
      RULE_ASSUM_TAC (REWRITE_RULE [SUBFIELD_OF_SUBFIELD_GENERATED_EQ]) THEN
      ASM_REWRITE_TAC [SUBSET_REFL] THEN
      ASM SET_TAC [SUBFIELD_GENERATED_SUBSET_CARRIER]]))

  let SUBFIELD_GENERATED_SUBFIELD_GENERATED ← prove
   r"!r s t:A->bool.
        s subfield_of r /\ t subfield_of r
        ==> subfield_generated (subfield_generated r s) t =
            subfield_generated r (s INTER t)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [RINGS_EQ, ← CONJUNCT2 SUBFIELD_GENERATED] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SUBFIELD_GENERATED_RESTRICT] THEN
    ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD, SUBFIELD_OF_INTER] THEN
    MATCH_MP_TAC CARRIER_SUBFIELD_GENERATED_SUBFIELD THEN
    ASM_SIMP_TAC [SUBFIELD_OF_SUBFIELD_GENERATED_SUBFIELD_EQ] THEN
    ASM_SIMP_TAC [INTER_SUBSET, SUBFIELD_OF_INTER])

  let SUBRING_GENERATED_SUBFIELD_GENERATED ← prove
   r"!r s:A->bool.
        subring_generated (subfield_generated r s) s =
        subring_generated r s"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [RINGS_EQ, ← CONJUNCT2 SUBRING_GENERATED,
                ← CONJUNCT2 SUBFIELD_GENERATED] THEN
    REWRITE_TAC [SUBRING_GENERATED, SUBRING_OF_SUBFIELD_GENERATED_EQ] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
    MATCH_MP_TAC INTERS_ANTIMONO_GEN THEN X_GEN_TAC (← q r"h:A->bool") THEN
    REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THENL
     [EXISTS_TAC (← q r"h INTER ring_carrier (subfield_generated r s):A->bool") THEN
      REWRITE_TAC [← GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBRING_OF_INTER THEN
        ASM_REWRITE_TAC [SUBRING_SUBFIELD_GENERATED],
        ASM SET_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET]],
      EXISTS_TAC (← q r"h:A->bool") THEN
      ASM SET_TAC [SUBFIELD_GENERATED_SUBSET_CARRIER]])

  let TRIVIAL_RING_SUBFIELD_GENERATED ← prove
   r"!r s:A->bool.
        trivial_ring(subfield_generated r s) <=> trivial_ring r"
   (REWRITE_TAC [TRIVIAL_RING_10, ← CONJUNCT2 SUBFIELD_GENERATED])

  let SUBFIELD_GENERATED_UNION_LEFT ← prove
   r"!r s t:A->bool.
        subfield_generated r (ring_carrier(subfield_generated r s) UNION t) =
        subfield_generated r (s UNION t)"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC SUBFIELDS_GENERATED_EQ THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [UNION_OVER_INTER, UNION_SUBSET] THEN
    ASM_SIMP_TAC [← GSYM SUBFIELD_GENERATED_MINIMAL_EQ] THEN
    REWRITE_TAC [SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED])

  let SUBFIELD_GENERATED_UNION_RIGHT ← prove
   r"!r s t:A->bool.
        subfield_generated r (s UNION ring_carrier(subfield_generated r t)) =
        subfield_generated r (s UNION t)"
   (ONCE_REWRITE_TAC [UNION_COMM] THEN
    REWRITE_TAC [SUBFIELD_GENERATED_UNION_LEFT])

  let SUBFIELD_GENERATED_UNION ← prove
   r"!r s t:A->bool.
        subfield_generated r (ring_carrier(subfield_generated r s) UNION
                              ring_carrier(subfield_generated r t)) =
        subfield_generated r (s UNION t)"
   (REWRITE_TAC [SUBFIELD_GENERATED_UNION_LEFT,
                SUBFIELD_GENERATED_UNION_RIGHT])

  -- @@RETURN BEGIN
  return { SUBSET_CARRIER_SUBFIELD_GENERATED, SUBFIELD_GENERATED_MINIMAL_EQ,
           SUBFIELD_GENERATED_RING_CARRIER, SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET,
           SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED, SUBFIELD_GENERATED_REFL,
           SUBFIELD_GENERATED_INC, SUBFIELD_GENERATED_INC_GEN,
           SUBRING_OF_SUBFIELD_GENERATED_EQ, SUBFIELD_OF_SUBFIELD_GENERATED_EQ,
           SUBFIELD_OF_SUBFIELD_GENERATED_SUBFIELD_EQ, SUBFIELD_OF_SUBFIELD_GENERATED,
           SUBFIELD_OF_SUBFIELD_GENERATED_REV, SUBFIELD_GENERATED_IDEMPOT,
           SUBFIELD_GENERATED_SUBFIELD_GENERATED, SUBRING_GENERATED_SUBFIELD_GENERATED,
           TRIVIAL_RING_SUBFIELD_GENERATED, SUBFIELD_GENERATED_UNION_LEFT,
           SUBFIELD_GENERATED_UNION_RIGHT, SUBFIELD_GENERATED_UNION }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Subfield generated, monomorphic images and ring operations.               -/
/- (fieldtheory.ml 645-890)                                                  -/
/- ------------------------------------------------------------------------- -/

structure SubfieldGenerated2 where
  -- @@FIELDS
  SUBFIELD_OF_MONOMORPHIC_IMAGE : thm
  SUBFIELD_OF_MONOMORPHIC_PREIMAGE : thm
  SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE : thm
  RING_SUB_SUBFIELD_GENERATED : thm
  RING_POW_SUBFIELD_GENERATED : thm
  RING_OF_NUM_SUBFIELD_GENERATED : thm
  RING_OF_INT_SUBFIELD_GENERATED : thm
  RING_CHAR_SUBFIELD_GENERATED : thm
  RING_0_IN_SUBFIELD_GENERATED : thm
  RING_1_IN_SUBFIELD_GENERATED : thm
  RING_NEG_IN_SUBFIELD_GENERATED : thm
  RING_ADD_IN_SUBFIELD_GENERATED : thm
  RING_MUL_IN_SUBFIELD_GENERATED : thm
  RING_POW_IN_SUBFIELD_GENERATED : thm
  RING_INV_SUBFIELD_GENERATED : thm
  RING_INV_IN_SUBFIELD_GENERATED : thm
  RING_DIV_IN_SUBFIELD_GENERATED : thm
  SUBFIELD_GENERATED_INDUCT : thm
  POLY_CONST_SUBFIELD_GENERATED : thm
  POLY_SUBFIELD_GENERATED_CLAUSES : thm
  deriving Inhabited

@[nospecialize]
def setupSubfieldGenerated2 [HolBase] (D : FieldTheoryDeps) (BSubfields : Subfields) (BSubfieldGenerated : SubfieldGenerated) (BSubfieldGenerated1 : SubfieldGenerated1) :
    ExceptT String IO SubfieldGenerated2 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INDUCT_TAC, MESON, MESON_TAC, SET_RULE, SET_TAC, TAUT, .. } := D
  let { CARRIER_SUBRING_GENERATED_SUBRING, EQ_IMP, .. } := D.core1
  let { FUN_EQ_THM, IMAGE_SUBSET, .. } := D.core2
  let { IN_ELIM_THM, ISOMORPHIC_RING_FIELDNESS, .. } := D.core3
  let { POLY_SUBRING_GENERATED_CLAUSES, RING_0, RING_1, RING_ADD, RING_CHAR_UNIQUE, .. } := D.core5
  let { RING_HOMOMORPHISM_IMAGE_PREIMAGE_EQ, RING_INV, RING_INV_0,
        RING_ISOMORPHISM_IMP_ISOMORPHIC, RING_ISOMORPHISM_ONTO_IMAGE,
        RING_MONOMORPHISM_FROM_SUBRING_GENERATED, RING_MONOMORPHISM_IMP_HOMOMORPHISM,
        RING_MUL, .. } := D.core6
  let { RING_NEG, RING_OF_NUM_EQ_0, RING_POW, SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE,
        SUBRING_GENERATED_BY_SUBRING_GENERATED, .. } := D.core7
  let { SUBRING_OF_HOMOMORPHIC_IMAGE, SUBRING_OF_HOMOMORPHIC_PREIMAGE, SUBSET,
        SUBSET_ANTISYM, SUBSET_RESTRICT, .. } := D.core8
  let { poly_const, ring_div, ring_homomorphism, ring_image, ring_monomorphism,
        ring_of_int, ring_of_num, ring_pow, ring_sub, subring_of, .. } := D.core9
  let { RING_INV_SUBRING_GENERATED, SUBFIELD_OF_FIELD_INV, subfield_of, .. } := BSubfields
  let { RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBFIELD_GENERATED,
        SUBFIELD_GENERATED_MINIMAL, SUBFIELD_GENERATED_RESTRICT,
        SUBFIELD_SUBFIELD_GENERATED_ALT, SUBFIELD_SUBFIELD_GENERATED_EQ,
        SUBRING_GENERATED_BY_SUBFIELD_GENERATED, .. } := BSubfieldGenerated
  let { SUBFIELD_GENERATED_IDEMPOT, SUBFIELD_GENERATED_INC_GEN,
        SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET, SUBFIELD_OF_SUBFIELD_GENERATED_REV, .. } := BSubfieldGenerated1
  -- @@SCOPE END

  let SUBFIELD_OF_MONOMORPHIC_IMAGE ← prove
   r"!(f:A->B) r r' s.
        ring_monomorphism(r,r') f /\ s subfield_of r
        ==> IMAGE f s subfield_of r'"
   (REWRITE_TAC [subfield_of] THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM,
                    SUBRING_OF_HOMOMORPHIC_IMAGE],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"ring_monomorphism (subring_generated r s:A ring,r') (f:A->B)")
    MP_TAC THENL
     [ASM_SIMP_TAC [RING_MONOMORPHISM_FROM_SUBRING_GENERATED],
      REWRITE_TAC [← GSYM RING_ISOMORPHISM_ONTO_IMAGE]] THEN
    DISCH_THEN (MP_TAC o MATCH_MP RING_ISOMORPHISM_IMP_ISOMORPHIC) THEN
    DISCH_THEN (MP_TAC o MATCH_MP ISOMORPHIC_RING_FIELDNESS) THEN
    ASM_REWRITE_TAC [ring_image] THEN
    ASM_MESON_TAC [SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE,
                  RING_MONOMORPHISM_IMP_HOMOMORPHISM, subring_of,
                  CARRIER_SUBRING_GENERATED_SUBRING])

  let SUBFIELD_OF_MONOMORPHIC_PREIMAGE ← prove
   r"!r r' (f:A->B) h.
        ring_monomorphism(r,r') f /\
        h subfield_of r' /\
        h SUBSET IMAGE f (ring_carrier r)
        ==> {x | x IN ring_carrier r /\ f x IN h} subfield_of r"
   (← do
    let i1 ← ISPECL
      [← q r"r:A ring", ← q r"r':B ring", ← q r"f:A->B",
       ← q r"{x | x IN ring_carrier r /\ (f:A->B) x IN h}"]
      SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE
    pure (REWRITE_TAC [subfield_of] THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM,
                    SUBRING_OF_HOMOMORPHIC_PREIMAGE],
     ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"ring_monomorphism
       (subring_generated r {x | x IN ring_carrier r /\ f x IN h}:A ring,r')
       (f:A->B)")
    MP_TAC THENL
     [ASM_SIMP_TAC [RING_MONOMORPHISM_FROM_SUBRING_GENERATED],
      REWRITE_TAC [← GSYM RING_ISOMORPHISM_ONTO_IMAGE]] THEN
    DISCH_THEN (MP_TAC o MATCH_MP RING_ISOMORPHISM_IMP_ISOMORPHIC) THEN
    DISCH_THEN (MP_TAC o MATCH_MP ISOMORPHIC_RING_FIELDNESS) THEN
    ASM_REWRITE_TAC [ring_image] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC (← q r"field (subring_generated r' h:B ring)") THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    MP_TAC i1 THEN
    ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM, SUBSET_RESTRICT] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
    CONV_TAC SYM_CONV THEN AP_TERM_TAC THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_IMAGE_PREIMAGE_EQ THEN
    EXISTS_TAC (← q r"r':B ring") THEN
    ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM, ring_image]))

  let SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE ← prove
   r"!r r' (f:A->B) s.
        ring_monomorphism(r,r') f /\
        s SUBSET ring_carrier r /\
        field(subfield_generated r s)
        ==> ring_carrier (subfield_generated r' (IMAGE f s)) =
            IMAGE f (ring_carrier(subfield_generated r s))"
   (← do
    let s3 ← SET_RULE (← q r"s SUBSET {x | x IN t /\ P x} ==> s SUBSET t")
    let t2 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    let s1 ← SET_RULE
      (← q r"IMAGE f s SUBSET t <=> s SUBSET {x | x IN s /\ f x IN t}")
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC [s1] THEN
    CONJ_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THENL
     [ASM_SIMP_TAC [SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET, IMAGE_SUBSET] THEN
      MATCH_MP_TAC SUBFIELD_OF_MONOMORPHIC_IMAGE THEN
      EXISTS_TAC (← q r"r:A ring") THEN
      ASM_REWRITE_TAC [SUBFIELD_SUBFIELD_GENERATED_EQ],
      ALL_TAC] THEN
    MATCH_MP_TAC t2 THEN CONJ_TAC THENL
     [REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:A") THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
      RULE_ASSUM_TAC (REWRITE_RULE [ring_monomorphism, ring_homomorphism]) THEN
      ASM SET_TAC [],
      DISCH_THEN (ASSUME_TAC o MATCH_MP s3)] THEN
    MATCH_MP_TAC SUBFIELD_OF_SUBFIELD_GENERATED_REV THEN
    EXISTS_TAC (← q r"s:A->bool") THEN
    MATCH_MP_TAC SUBFIELD_OF_MONOMORPHIC_PREIMAGE THEN
    EXISTS_TAC (← q r"r':B ring") THEN
    ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    ASM_SIMP_TAC [RING_MONOMORPHISM_FROM_SUBRING_GENERATED] THEN
    REWRITE_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [SUBFIELD_SUBFIELD_GENERATED_ALT] THEN
      EXISTS_TAC (← q r"IMAGE (f:A->B) (ring_carrier(subfield_generated r s))") THEN
      CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []],
      MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN
      ASM_SIMP_TAC [IMAGE_SUBSET]] THEN
    MATCH_MP_TAC SUBFIELD_OF_MONOMORPHIC_IMAGE THEN
    ASM_MESON_TAC [SUBFIELD_SUBFIELD_GENERATED_EQ]))

  let RING_SUB_SUBFIELD_GENERATED ← prove
   r"!r s:A->bool. ring_sub (subfield_generated r s) = ring_sub r"
   (REWRITE_TAC [FUN_EQ_THM, ring_sub, SUBFIELD_GENERATED])

  let RING_POW_SUBFIELD_GENERATED ← prove
   r"!r s:A->bool. ring_pow (subfield_generated r s) = ring_pow r"
   (REPEAT GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC [ring_pow, SUBFIELD_GENERATED])

  let RING_OF_NUM_SUBFIELD_GENERATED ← prove
   r"!r s:A->bool. ring_of_num (subfield_generated r s) = ring_of_num r"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC [ring_of_num, SUBFIELD_GENERATED])

  let RING_OF_INT_SUBFIELD_GENERATED ← prove
   r"!r s:A->bool. ring_of_int (subfield_generated r s) = ring_of_int r"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    REWRITE_TAC [ring_of_int, RING_OF_NUM_SUBFIELD_GENERATED] THEN
    REWRITE_TAC [SUBFIELD_GENERATED])

  let RING_CHAR_SUBFIELD_GENERATED ← prove
   r"!r s:A->bool. ring_char(subfield_generated r s) = ring_char r"
   (REWRITE_TAC [RING_CHAR_UNIQUE] THEN
    REWRITE_TAC [SUBFIELD_GENERATED, RING_OF_NUM_SUBFIELD_GENERATED] THEN
    REWRITE_TAC [RING_OF_NUM_EQ_0])

  let RING_0_IN_SUBFIELD_GENERATED ← prove
   r"!r (s:A->bool). ring_0 r IN ring_carrier (subfield_generated r s)"
   (MESON_TAC [RING_0, SUBFIELD_GENERATED])

  let RING_1_IN_SUBFIELD_GENERATED ← prove
   r"!r (s:A->bool). ring_1 r IN ring_carrier (subfield_generated r s)"
   (MESON_TAC [RING_1, SUBFIELD_GENERATED])

  let RING_NEG_IN_SUBFIELD_GENERATED ← prove
   r"!r s x:A.
        x IN ring_carrier (subfield_generated r s)
        ==> ring_neg r x IN ring_carrier (subfield_generated r s)"
   (MESON_TAC [RING_NEG, SUBFIELD_GENERATED])

  let RING_ADD_IN_SUBFIELD_GENERATED ← prove
   r"!r s x y:A.
        x IN ring_carrier (subfield_generated r s) /\
        y IN ring_carrier (subfield_generated r s)
        ==> ring_add r x y IN ring_carrier (subfield_generated r s)"
   (MESON_TAC [RING_ADD, SUBFIELD_GENERATED])

  let RING_MUL_IN_SUBFIELD_GENERATED ← prove
   r"!r s x y:A.
        x IN ring_carrier (subfield_generated r s) /\
        y IN ring_carrier (subfield_generated r s)
        ==> ring_mul r x y IN ring_carrier (subfield_generated r s)"
   (MESON_TAC [RING_MUL, SUBFIELD_GENERATED])

  let RING_POW_IN_SUBFIELD_GENERATED ← prove
   r"!r s (x:A) n.
        x IN ring_carrier (subfield_generated r s)
        ==> ring_pow r x n IN ring_carrier (subfield_generated r s)"
   (MESON_TAC [RING_POW, RING_POW_SUBFIELD_GENERATED])

  let RING_INV_SUBFIELD_GENERATED ← prove
   r"!r s x:A.
        field(subfield_generated r s) /\
        x IN ring_carrier(subfield_generated r s) /\
        ~(x = ring_0 r)
        ==> ring_inv (subfield_generated r s) x = ring_inv r x"
   (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    MATCH_MP_TAC RING_INV_SUBRING_GENERATED THEN
    ASM_REWRITE_TAC [SUBFIELD_SUBFIELD_GENERATED_EQ])

  let RING_INV_IN_SUBFIELD_GENERATED ← prove
   r"!r s x:A.
        field(subfield_generated r s) /\
        x IN ring_carrier(subfield_generated r s)
        ==> ring_inv r x IN ring_carrier(subfield_generated r s)"
   (MESON_TAC [RING_INV_0, RING_0_IN_SUBFIELD_GENERATED,
              RING_INV, RING_INV_SUBFIELD_GENERATED])

  let RING_DIV_IN_SUBFIELD_GENERATED ← prove
   r"!r s x y:A.
        field(subfield_generated r s) /\
        x IN ring_carrier (subfield_generated r s) /\
        y IN ring_carrier (subfield_generated r s)
        ==> ring_div r x y IN ring_carrier (subfield_generated r s)"
   (SIMP_TAC [ring_div, RING_MUL_IN_SUBFIELD_GENERATED,
             RING_INV_IN_SUBFIELD_GENERATED])

  let SUBFIELD_GENERATED_INDUCT ← prove
   r"!r P s:A->bool.
        field(subfield_generated r s) /\
        (!x. x IN ring_carrier r /\ x IN s ==> P x) /\
        P(ring_0 r) /\
        P(ring_1 r) /\
        (!x. x IN ring_carrier r /\ P x ==> P(ring_neg r x)) /\
        (!x. x IN ring_carrier r /\ ~(x = ring_0 r) /\ P x
             ==> P(ring_inv r x)) /\
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r /\ P x /\ P y
               ==> P(ring_add r x y)) /\
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r /\ P x /\ P y
               ==> P(ring_mul r x y))
        ==> !x. x IN ring_carrier(subfield_generated r s) ==> P x"
   (← do
    let m1 ← MESON []
      (← q r"(!k. field k ==> P k) /\ ((!k. field k ==> P k) ==> !r. P r)
    ==> !r. P r")
    pure (MATCH_MP_TAC m1 THEN
    CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"ring_carrier(subfield_generated k s) SUBSET
      {x:A | x IN ring_carrier k /\ P x}")
      MP_TAC THENL [ALL_TAC, SET_TAC []] THEN
      ONCE_REWRITE_TAC [SUBFIELD_GENERATED_RESTRICT] THEN
      MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN
      CONJ_TAC THENL [ASM SET_TAC [], MATCH_MP_TAC SUBFIELD_OF_FIELD_INV] THEN
      ASM_REWRITE_TAC [subring_of, IN_ELIM_THM, RING_0, RING_1] THEN
      SIMP_TAC [RING_NEG, RING_ADD, RING_MUL, RING_INV] THEN
      ASM SET_TAC [RING_INV_0],
      DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"subfield_generated r s:A ring")) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o SPECL [← q r"P:A->bool", ← q r"s:A->bool"]) THEN
    REWRITE_TAC [SUBFIELD_GENERATED_IDEMPOT] THEN
    ASM_REWRITE_TAC [← CONJUNCT2 SUBFIELD_GENERATED] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC [RING_INV_SUBFIELD_GENERATED] THEN
    ASM_MESON_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET]))

  let POLY_CONST_SUBFIELD_GENERATED ← prove
   r"!r s. poly_const (subfield_generated r s):A->(V->num)->A = poly_const r"
   (REWRITE_TAC [FUN_EQ_THM, poly_const, ← CONJUNCT2 SUBFIELD_GENERATED])

  let POLY_SUBFIELD_GENERATED_CLAUSES ← prove
   r"(!(r:A ring) s (v:V->bool).
        ring_0 (poly_ring (subfield_generated r s) v) =
        ring_0 (poly_ring r v)) /\
   (!(r:A ring) s (v:V->bool).
        ring_1 (poly_ring (subfield_generated r s) v) =
        ring_1 (poly_ring r v)) /\
   (!(r:A ring) s (v:V->bool).
        ring_neg (poly_ring (subfield_generated r s) v) =
        ring_neg (poly_ring r v)) /\
   (!(r:A ring) s (v:V->bool).
        ring_add (poly_ring (subfield_generated r s) v) =
        ring_add (poly_ring r v)) /\
   (!(r:A ring) s (v:V->bool) p q.
        (!m. p m IN ring_carrier(subfield_generated r s)) /\
        (!m. q m IN ring_carrier(subfield_generated r s))
        ==> ring_mul (poly_ring (subfield_generated r s) v) p q =
            ring_mul (poly_ring r v) p q) /\
   (!(r:A ring) s (v:V->bool).
        ring_sub (poly_ring (subfield_generated r s) v) =
        ring_sub (poly_ring r v))"
   (ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    REWRITE_TAC [POLY_SUBRING_GENERATED_CLAUSES])

  -- @@RETURN BEGIN
  return { SUBFIELD_OF_MONOMORPHIC_IMAGE, SUBFIELD_OF_MONOMORPHIC_PREIMAGE,
           SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE, RING_SUB_SUBFIELD_GENERATED,
           RING_POW_SUBFIELD_GENERATED, RING_OF_NUM_SUBFIELD_GENERATED,
           RING_OF_INT_SUBFIELD_GENERATED, RING_CHAR_SUBFIELD_GENERATED,
           RING_0_IN_SUBFIELD_GENERATED, RING_1_IN_SUBFIELD_GENERATED,
           RING_NEG_IN_SUBFIELD_GENERATED, RING_ADD_IN_SUBFIELD_GENERATED,
           RING_MUL_IN_SUBFIELD_GENERATED, RING_POW_IN_SUBFIELD_GENERATED,
           RING_INV_SUBFIELD_GENERATED, RING_INV_IN_SUBFIELD_GENERATED,
           RING_DIV_IN_SUBFIELD_GENERATED, SUBFIELD_GENERATED_INDUCT,
           POLY_CONST_SUBFIELD_GENERATED, POLY_SUBFIELD_GENERATED_CLAUSES }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Quotient-based descriptions of subfield_generated.  (fieldtheory.ml       -/
/- 893-1182)                                                                 -/
/- ------------------------------------------------------------------------- -/

structure SubfieldQuotients where
  -- @@FIELDS
  FIELD_SUBFIELD_GENERATED_UNITS : thm
  SUBFIELD_GENERATED_SUBRING_QUOTIENTS : thm
  RING_CARRIER_SUBFIELD_GENERATED_SUBRING_QUOTIENTS : thm
  SUBFIELD_GENERATED_QUOTIENTS : thm
  FINITE_SUBSET_SUBFIELD_GENERATED_DENOMINATOR : thm
  POLY_OVER_SUBFIELD_GENERATED_DENOMINATOR : thm
  IN_SUBFIELD_GENERATED_FINITARY : thm
  PRIME_SUBFIELD_MINIMAL : thm
  PRIME_SUBFIELD_EQ_SUBRING : thm
  FROBENIUS_FIXED_FIELD : thm
  deriving Inhabited

@[nospecialize]
def setupSubfieldQuotients [HolBase] (D : FieldTheoryDeps) (BSubfields : Subfields) (BSubfieldGenerated : SubfieldGenerated) (BSubfieldGenerated1 : SubfieldGenerated1) (BSubfieldGenerated2 : SubfieldGenerated2) :
    ExceptT String IO SubfieldQuotients := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, FIELD_TAC, MESON_TAC, RING_TAC, SET_RULE, SET_TAC, .. } := D
  let { CARRIER_SUBRING_GENERATED_SUBRING, DE_MORGAN_THM, EMPTY_SUBSET,
        FIELD_EQ_ALL_UNITS, .. } := D.core1
  let { FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING, FIELD_MUL_EQ_0,
        FIELD_PRIME_SUBRING, FINITE_EMPTY, FINITE_IMAGE, FINITE_INDUCT_STRONG,
        FINITE_INSERT, FINITE_SUBSET, FINITE_UNION, FORALL_IN_GSPEC, FORALL_IN_IMAGE,
        FORALL_IN_INSERT, FROBENIUS_FIXED, .. } := D.core2
  let { IMP_CONJ, IMP_IMP, INSERT_SUBSET, IN_ELIM_THM, IN_INTER,
        IN_SUBRING_GENERATED_FINITARY, IN_UNIV, LEFT_IMP_EXISTS_THM, .. } := D.core3
  let { MONO_EXISTS, NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY, .. } := D.core4
  let { POLY_MUL_CONST, POLY_RING, POLY_SUBRING_GENERATED_CLAUSES,
        RIGHT_FORALL_IMP_THM, RINGS_EQ, RING_0_IN_SUBRING_GENERATED,
        RING_1_IN_SUBRING_GENERATED, RING_CARRIER_SUBRING_GENERATED_0,
        RING_CARRIER_SUBRING_GENERATED_SUBSET, .. } := D.core5
  let { RING_DIV, RING_DIV_1, .. } := D.core6
  let { RING_MUL_IN_SUBRING_GENERATED, SING_SUBSET, SUBRING_GENERATED,
        SUBRING_GENERATED_BY_SUBRING_GENERATED, .. } := D.core7
  let { SUBRING_GENERATED_INC_GEN, SUBRING_GENERATED_MONO, SUBRING_GENERATED_RESTRICT,
        SUBRING_GENERATED_SUBSET_CARRIER, SUBRING_SUBRING_GENERATED, SUBSET,
        SUBSET_ANTISYM, SUBSET_UNION, TRIVIAL_RING_10, UNION_SUBSET, field, .. } := D.core8
  let { poly_const, poly_vars, ring_polynomial, ring_powerseries, ring_unit,
        trivial_ring, .. } := D.core9
  let { IN_SUBFIELD_0, SUBFIELD_IMP_SUBRING_OF, SUBFIELD_OF_SUBRING_QUOTIENTS, .. } := BSubfields
  let { FIELD_SUBFIELD_GENERATED, FIELD_SUBFIELD_GENERATED_ALT,
        FIELD_SUBFIELD_GENERATED_MONO, RING_CARRIER_SUBFIELD_GENERATED_SUBSET,
        SUBFIELD_GENERATED, SUBFIELD_GENERATED_MINIMAL, SUBFIELD_GENERATED_RESTRICT,
        SUBFIELD_GENERATED_TRIVIAL, SUBRING_EQ_SUBFIELD_GENERATED,
        SUBRING_GENERATED_BY_SUBFIELD_GENERATED, SUBRING_SUBSET_SUBFIELD_GENERATED, .. } := BSubfieldGenerated
  let { SUBFIELD_GENERATED_IDEMPOT, SUBRING_GENERATED_SUBFIELD_GENERATED,
        TRIVIAL_RING_SUBFIELD_GENERATED, .. } := BSubfieldGenerated1
  let { POLY_CONST_SUBFIELD_GENERATED, POLY_SUBFIELD_GENERATED_CLAUSES,
        RING_0_IN_SUBFIELD_GENERATED, RING_DIV_IN_SUBFIELD_GENERATED, .. } := BSubfieldGenerated2
  -- @@SCOPE END

  let FIELD_SUBFIELD_GENERATED_UNITS ← prove
   r"!r s:A->bool.
        field(subfield_generated r s) <=>
        ~(trivial_ring r) /\
        !x. x IN ring_carrier(subring_generated r s) /\ ~(x = ring_0 r)
            ==> ring_unit r x"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP FIELD_IMP_NONTRIVIAL_RING) THEN
      SIMP_TAC [TRIVIAL_RING_SUBFIELD_GENERATED] THEN DISCH_TAC THEN
      FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [FIELD_EQ_ALL_UNITS]) THEN
      ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
      REWRITE_TAC [ring_unit, ← CONJUNCT2 SUBRING_GENERATED] THEN
      REWRITE_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
      MP_TAC (← ISPECL [← q r"r:A ring", ← q r"s:A->bool"]
       SUBRING_SUBSET_SUBFIELD_GENERATED) THEN
      MP_TAC (← ISPECL [← q r"r:A ring", ← q r"s:A->bool"]
          RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN
      SET_TAC [],
      STRIP_TAC THEN REWRITE_TAC [FIELD_SUBFIELD_GENERATED_ALT] THEN
      EXISTS_TAC
       (← q r"{ ring_div r x y | x,y |
          x IN ring_carrier(subring_generated r s) /\
          y IN ring_carrier(subring_generated r s) /\
          ~(y:A = ring_0 r) }") THEN
      ASM_SIMP_TAC [SUBFIELD_OF_SUBRING_QUOTIENTS, SUBRING_SUBRING_GENERATED] THEN
      REWRITE_TAC [SUBSET, IN_INTER, IN_ELIM_THM] THEN
      X_GEN_TAC (← q r"a:A") THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [← q r"a:A", ← q r"ring_1 r:A"] THEN
      ASM_SIMP_TAC [← GSYM TRIVIAL_RING_10, RING_DIV_1] THEN
      REWRITE_TAC [RING_1_IN_SUBRING_GENERATED] THEN
      MP_TAC (← ISPECL [← q r"r:A ring", ← q r"s:A->bool"]
        SUBRING_GENERATED_SUBSET_CARRIER) THEN
      ASM SET_TAC []])

  let SUBFIELD_GENERATED_SUBRING_QUOTIENTS ← prove
   r"!r s:A->bool.
        ~(trivial_ring r) /\
        (!x. x IN ring_carrier(subring_generated r s) /\ ~(x = ring_0 r)
             ==> ring_unit r x)
        ==> subfield_generated r s =
            subring_generated r
             { ring_div r x y | x,y |
               x IN ring_carrier(subring_generated r s) /\
               y IN ring_carrier(subring_generated r s) /\
               ~(y = ring_0 r) }"
   (← do
    let s1 ← SET_RULE
      (← q r"ring_carrier r INTER s SUBSET ring_carrier(r:A ring)")
    pure (REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [SUBFIELD_GENERATED_RESTRICT] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [SUBRING_GENERATED_RESTRICT] THEN
    GEN_REWRITE_TAC (funpow 3 RAND_CONV o ONCE_DEPTH_CONV)
     [SUBRING_GENERATED_RESTRICT] THEN
    MP_TAC s1 THEN
    SPEC_TAC (← q r"ring_carrier r INTER s:A->bool", ← q r"s:A->bool") THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"r:A ring", ← q r"ring_carrier(subring_generated r s):A->bool"]
      SUBFIELD_OF_SUBRING_QUOTIENTS) THEN
    ASM_REWRITE_TAC [SUBRING_SUBRING_GENERATED] THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"r:A ring", ← q r"s:A->bool"] FIELD_SUBFIELD_GENERATED_UNITS) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN REWRITE_TAC [RINGS_EQ] THEN
    REWRITE_TAC [← CONJUNCT2 SUBRING_GENERATED, ← CONJUNCT2 SUBFIELD_GENERATED] THEN
    ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING, SUBFIELD_IMP_SUBRING_OF] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [← q r"a:A", ← q r"ring_1 r:A"] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [SUBSET]) THEN
      ASM_SIMP_TAC [RING_1_IN_SUBRING_GENERATED, RING_DIV_1] THEN
      ASM_SIMP_TAC [← GSYM TRIVIAL_RING_10, SUBRING_GENERATED_INC_GEN],
      REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_DIV_IN_SUBFIELD_GENERATED THEN
      ASM SET_TAC [SUBRING_SUBSET_SUBFIELD_GENERATED]]))

  let RING_CARRIER_SUBFIELD_GENERATED_SUBRING_QUOTIENTS ← prove
   r"!r s:A->bool.
        ~(trivial_ring r) /\
        (!x. x IN ring_carrier(subring_generated r s) /\ ~(x = ring_0 r)
             ==> ring_unit r x)
        ==> ring_carrier(subfield_generated r s) =
             { ring_div r x y | x,y |
               x IN ring_carrier(subring_generated r s) /\
               y IN ring_carrier(subring_generated r s) /\
               ~(y = ring_0 r) }"
   (ASM_SIMP_TAC [SUBFIELD_GENERATED_SUBRING_QUOTIENTS] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CARRIER_SUBRING_GENERATED_SUBRING THEN
    MATCH_MP_TAC SUBFIELD_IMP_SUBRING_OF THEN
    ASM_SIMP_TAC [SUBFIELD_OF_SUBRING_QUOTIENTS, SUBRING_SUBRING_GENERATED])

  let SUBFIELD_GENERATED_QUOTIENTS ← prove
   r"!r s x:A.
        field(subfield_generated r s) /\
        x IN ring_carrier (subfield_generated r s)
        ==> ?a b. a IN ring_carrier(subring_generated r s) /\
                  b IN ring_carrier(subring_generated r s) /\
                  ~(b = ring_0 r) /\
                  ring_div r a b = x"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE id
      [FIELD_SUBFIELD_GENERATED_UNITS]) THEN
    ASM_SIMP_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBRING_QUOTIENTS] THEN
    SET_TAC [])

  let FINITE_SUBSET_SUBFIELD_GENERATED_DENOMINATOR ← prove
   r"!r s d:A->bool.
      field(subfield_generated r s) /\
      FINITE d /\
      d SUBSET ring_carrier(subfield_generated r s)
      ==> ?c. c IN ring_carrier(subring_generated r s) /\
              ~(c = ring_0 r) /\
              !x. x IN d
                  ==> ring_mul r c x IN ring_carrier(subring_generated r s)"
   (SUBGOAL_THEN
     (← q r"!r s d:A->bool.
          field r /\
          FINITE d /\
          d SUBSET ring_carrier(subfield_generated r s)
          ==> ?c. c IN ring_carrier(subring_generated r s) /\
                  ~(c = ring_0 r) /\
                  !x. x IN d
                      ==> ring_mul r c x IN ring_carrier(subring_generated r s)")
    MP_TAC THENL
     [ALL_TAC,
      DISCH_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM (fun th => tactic_of do pure (MP_TAC
        (← ISPECL [← q r"subfield_generated r s:A ring", ← q r"s:A->bool", ← q r"d:A->bool"] th))) THEN
      ASM_REWRITE_TAC [SUBRING_GENERATED_SUBFIELD_GENERATED] THEN
      ASM_REWRITE_TAC [SUBFIELD_GENERATED_IDEMPOT] THEN
      REWRITE_TAC [← CONJUNCT2 SUBFIELD_GENERATED]] THEN
    GEN_TAC THEN GEN_TAC THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [EMPTY_SUBSET, INSERT_SUBSET] THEN CONJ_TAC THENL
     [EXISTS_TAC (← q r"ring_1 r:A") THEN ASM_REWRITE_TAC [NOT_IN_EMPTY] THEN
      ASM_MESON_TAC [RING_1_IN_SUBRING_GENERATED, field],
      REWRITE_TAC [FORALL_IN_INSERT]] THEN
    MAP_EVERY X_GEN_TAC [← q r"y:A", ← q r"d:A->bool"] THEN
    DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_THEN (← q r"c:A") STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q r"r:A ring", ← q r"s:A->bool", ← q r"y:A"]
          SUBFIELD_GENERATED_QUOTIENTS) THEN
    ASM_SIMP_TAC [LEFT_IMP_EXISTS_THM, FIELD_SUBFIELD_GENERATED] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:A", ← q r"b:A"] THEN STRIP_TAC THEN
    EXISTS_TAC (← q r"ring_mul r b c:A") THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC [RING_MUL_IN_SUBRING_GENERATED],
      ASM_MESON_TAC [← REWRITE_RULE [SUBSET] RING_CARRIER_SUBRING_GENERATED_SUBSET,
                    FIELD_MUL_EQ_0],
      SUBGOAL_THEN (← q r"ring_mul r (ring_mul r b c) y:A = ring_mul r a c") SUBST1_TAC
      THENL [ALL_TAC, ASM_SIMP_TAC [RING_MUL_IN_SUBRING_GENERATED]] THEN
      EXPAND_TAC "y" THEN UNDISCH_TAC (← q r"~(b:A = ring_0 r)") THEN
      REPEAT (FIRST_X_ASSUM (fun th => tactic_of do pure (MP_TAC (← MATCH_MP
       (← REWRITE_RULE [SUBSET] RING_CARRIER_SUBRING_GENERATED_SUBSET) th)))) THEN
      UNDISCH_TAC (← q r"field(r: A ring)") THEN POP_ASSUM_LIST (K ALL_TAC) THEN
      FIELD_TAC,
      X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN
      SUBGOAL_THEN
        (← q r"ring_mul r (ring_mul r b c) x:A = ring_mul r b (ring_mul r c x)")
      SUBST1_TAC THENL [RING_TAC, ALL_TAC] THEN
      ASM_MESON_TAC [SUBSET, RING_CARRIER_SUBRING_GENERATED_SUBSET,
                    RING_CARRIER_SUBFIELD_GENERATED_SUBSET,
                    RING_MUL_IN_SUBRING_GENERATED, RING_DIV]])

  let POLY_OVER_SUBFIELD_GENERATED_DENOMINATOR ← prove
   r"!r s v (p:(V->num)->A).
        field (subfield_generated r s) /\
        p IN ring_carrier(poly_ring (subfield_generated r s) v)
        ==> ?d. d IN ring_carrier(subring_generated r s) /\
                ~(d = ring_0 r) /\
                poly_mul r (poly_const r d) p IN
                ring_carrier(poly_ring (subring_generated r s) v)"
   (ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    REWRITE_TAC [POLY_SUBRING_GENERATED_CLAUSES] THEN
    REWRITE_TAC [POLY_RING, ring_polynomial, IN_ELIM_THM, ring_powerseries] THEN
    REWRITE_TAC [poly_vars] THEN
    REWRITE_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    REWRITE_TAC [← CONJUNCT2 SUBFIELD_GENERATED] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"r:A ring", ← q r"s:A->bool", ← q r"IMAGE (p:(V->num)->A) UNIV"]
          FINITE_SUBSET_SUBFIELD_GENERATED_DENOMINATOR) THEN
    ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN ANTS_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
       (← q r"ring_0 r INSERT IMAGE (p:(V->num)->A) {m | ~(p m = ring_0 r)}") THEN
      ASM_SIMP_TAC [FINITE_IMAGE, FINITE_INSERT] THEN SET_TAC [],
      MATCH_MP_TAC MONO_EXISTS] THEN
    REWRITE_TAC [IN_UNIV] THEN X_GEN_TAC (← q r"d:A") THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [← CONJUNCT2 SUBRING_GENERATED] THEN
    MP_TAC (← ISPECL
     [← q r"subfield_generated r s:A ring", ← q r"d:A", ← q r"p:(V->num)->A"]
     POLY_MUL_CONST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [ring_polynomial, ring_powerseries,
                      ← CONJUNCT2 SUBFIELD_GENERATED] THEN
      ASM SET_TAC [SUBRING_SUBSET_SUBFIELD_GENERATED],
      MP_TAC (← ISPECL [← q r"r:A ring", ← q r"s:A->bool", ← q "(:V)",
                     ← q r"poly_const r d:(V->num)->A", ← q r"p:(V->num)->A"]
        (← liftExcept (match (CONJUNCTS POLY_SUBFIELD_GENERATED_CLAUSES)[4]? with
          | some t => .ok t | none => .error "el"))) THEN
      ASM_REWRITE_TAC [POLY_RING, POLY_CONST_SUBFIELD_GENERATED]] THEN
    ANTS_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [poly_const] THEN
      ASM SET_TAC [RING_0_IN_SUBFIELD_GENERATED,
                  SUBRING_SUBSET_SUBFIELD_GENERATED],
      DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC [← CONJUNCT2 SUBFIELD_GENERATED] THEN
    SUBGOAL_THEN
     (← q r"!m. ring_mul r d ((p:(V->num)->A) m) = ring_0 r <=> p m = ring_0 r")
     (fun th => ASM_REWRITE_TAC [th] THEN ASM SET_TAC []) THEN
    GEN_TAC THEN
    FIRST_ASSUM (MP_TAC o ISPEC (← q r"d:A") o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          FIELD_MUL_EQ_0)) THEN
    ASM_REWRITE_TAC [← CONJUNCT2 SUBFIELD_GENERATED, IMP_IMP] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM SET_TAC [SUBRING_SUBSET_SUBFIELD_GENERATED])

  let IN_SUBFIELD_GENERATED_FINITARY ← prove
   r"!r s x:A.
        x IN ring_carrier(subfield_generated r s)
        ==> ?t. FINITE t /\
                t SUBSET s /\
                x IN ring_carrier(subfield_generated r t)"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"field(subfield_generated r s:A ring)") THENL
     [MP_TAC (← ISPECL [← q r"r:A ring", ← q r"s:A->bool", ← q r"x:A"]
        SUBFIELD_GENERATED_QUOTIENTS) THEN
      ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"y:A", ← q r"z:A"] THEN STRIP_TAC THEN
      MAP_EVERY (fun ts => tactic_of do pure (MP_TAC (← C ISPECL IN_SUBRING_GENERATED_FINITARY ts)))
       [[← q r"r:A ring", ← q r"s:A->bool", ← q r"z:A"],
        [← q r"r:A ring", ← q r"s:A->bool", ← q r"y:A"]] THEN
      ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"t:A->bool") THEN STRIP_TAC THEN
      X_GEN_TAC (← q r"u:A->bool") THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"t UNION u:A->bool") THEN
      ASM_REWRITE_TAC [FINITE_UNION, UNION_SUBSET] THEN
      EXPAND_TAC "x" THEN MATCH_MP_TAC RING_DIV_IN_SUBFIELD_GENERATED THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC [FIELD_SUBFIELD_GENERATED_MONO, UNION_SUBSET], ALL_TAC] THEN
      CONJ_TAC THEN
      MATCH_MP_TAC (← REWRITE_RULE [SUBSET] SUBRING_SUBSET_SUBFIELD_GENERATED) THEN
      ASM_MESON_TAC [SUBRING_GENERATED_MONO, SUBSET, SUBSET_UNION],
      FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV
       [FIELD_SUBFIELD_GENERATED_UNITS]) THEN
      REWRITE_TAC [DE_MORGAN_THM] THEN STRIP_TAC THENL
       [EXISTS_TAC (← q r"{}:A->bool") THEN
        ASM_REWRITE_TAC [FINITE_EMPTY, EMPTY_SUBSET] THEN
        SUBGOAL_THEN (← q r"x:A = ring_0 r") SUBST1_TAC THENL
         [RULE_ASSUM_TAC (REWRITE_RULE [trivial_ring]) THEN
          MP_TAC (← ISPECL [← q r"r:A ring", ← q r"s:A->bool"]
             RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN
          ASM SET_TAC [],
          ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
          REWRITE_TAC [RING_0_IN_SUBRING_GENERATED]],
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [NOT_FORALL_THM]) THEN
        REWRITE_TAC [NOT_IMP] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"u:A") STRIP_ASSUME_TAC) THEN
        FIRST_ASSUM (MP_TAC o MATCH_MP IN_SUBRING_GENERATED_FINITARY) THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:A->bool") THEN
        STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN (← q r"subfield_generated r t:A ring = r") SUBST1_TAC THENL
         [ALL_TAC, ASM SET_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET]] THEN
        MATCH_MP_TAC SUBFIELD_GENERATED_TRIVIAL THEN
        REWRITE_TAC [← GSYM FIELD_SUBFIELD_GENERATED_ALT] THEN
        REWRITE_TAC [FIELD_SUBFIELD_GENERATED_UNITS] THEN
        ASM_MESON_TAC []]])

  let PRIME_SUBFIELD_MINIMAL ← prove
   r"!k s:A->bool.
        s subfield_of k
        ==> ring_carrier(subfield_generated k {ring_0 k}) SUBSET s"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN
    ASM_MESON_TAC [IN_SUBFIELD_0, SING_SUBSET])

  let PRIME_SUBFIELD_EQ_SUBRING ← prove
   r"!k:A ring.
        prime(ring_char k)
        ==> ring_carrier(subfield_generated k {ring_0 k}) =
            {ring_of_int k n | n IN (:int)}"
   (REWRITE_TAC [← GSYM RING_CARRIER_SUBRING_GENERATED_0, ← GSYM FIELD_PRIME_SUBRING,
                SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
    MESON_TAC [SUBRING_EQ_SUBFIELD_GENERATED])

  let FROBENIUS_FIXED_FIELD ← prove
   r"!k:A ring.
        field k /\ prime(ring_char k)
        ==> { x | x IN ring_carrier k /\ ring_pow k x (ring_char k) = x} =
            ring_carrier(subfield_generated k {ring_0 k})"
   (SIMP_TAC [PRIME_SUBFIELD_EQ_SUBRING, FROBENIUS_FIXED,
             FIELD_IMP_INTEGRAL_DOMAIN])

  -- @@RETURN BEGIN
  return { FIELD_SUBFIELD_GENERATED_UNITS, SUBFIELD_GENERATED_SUBRING_QUOTIENTS,
           RING_CARRIER_SUBFIELD_GENERATED_SUBRING_QUOTIENTS,
           SUBFIELD_GENERATED_QUOTIENTS, FINITE_SUBSET_SUBFIELD_GENERATED_DENOMINATOR,
           POLY_OVER_SUBFIELD_GENERATED_DENOMINATOR, IN_SUBFIELD_GENERATED_FINITARY,
           PRIME_SUBFIELD_MINIMAL, PRIME_SUBFIELD_EQ_SUBRING, FROBENIUS_FIXED_FIELD }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Field extensions, allowing a general monomorphism. This does build        -/
/- in the assumption that both the rings involved are indeed fields.         -/
/- (fieldtheory.ml 1184-1416)                                                -/
/- ------------------------------------------------------------------------- -/

structure FieldExtension where
  -- @@FIELDS
  field_extension : thm
  FIELD_EXTENSION_IMP_MONOMORPHISM : thm
  FIELD_EXTENSION_IMP_HOMOMORPHISM : thm
  FIELD_EXTENSION_IMP_SUBSET : thm
  FIELD_EXTENSION_CARRIER : thm
  FIELD_EXTENSION_FROM_SUBRING_GENERATED : thm
  FIELD_EXTENSION_EQ : thm
  FIELD_EXTENSION_REFL : thm
  FIELD_EXTENSION_TRANS : thm
  FIELD_EXTENSION_TRANS_I : thm
  FIELD_EXTENSION_ISOMORPHISM : thm
  FIELD_EXTENSION_SUBRING_GENERATED : thm
  FIELD_EXTENSION_INTO_SUBRING_GENERATED : thm
  FIELD_EXTENSION_INTO_SUBFIELD_GENERATED : thm
  KRONECKER_FIELD_EXTENSION : thm
  KRONECKER_SIMPLE_FIELD_EXTENSION : thm
  COPRIME_POLY_NO_COMMON_ROOT : thm
  COPRIME_POLY_NO_COMMON_ROOT_I : thm
  deriving Inhabited

@[nospecialize]
def setupFieldExtension [HolBase] (D : FieldTheoryDeps) (BSubfields : Subfields) (BSubfieldGenerated : SubfieldGenerated) :
    ExceptT String IO FieldExtension := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_TAC, TAUT, new_definition, .. } := D
  let { CONJ_ACI, ETA_AX, ETA_ONE, .. } := D.core1
  let { FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING, FIELD_QUOTIENT_RING,
        FIELD_UNIT, FORALL_IN_IMAGE, FORALL_IN_INSERT, FUN_IN_IMAGE, IMAGE_CLAUSES,
        IMAGE_o, .. } := D.core2
  let { IMP_CONJ, IMP_IMP, INTEGRAL_DOMAIN_POLY_RING,
        INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE, IN_IDEAL_GENERATED_SING, IN_IMAGE,
        IN_RING_POLYNOMIAL_CARRIER_COMPOSE, ISOMORPHIC_RING_FIELDNESS, I_DEF, I_O_ID, .. } := D.core3
  let { MAXIMAL_IDEAL_SING, MAXIMAL_IMP_PRIME_IDEAL, MAXIMAL_IMP_RING_IDEAL,
        PID_IMP_BEZOUT_RING, PID_IMP_UFD, PID_POLY_RING, POLY_CLAUSES, POLY_CONST,
        POLY_CONST_0, POLY_DEG_0, POLY_DEG_CONST, POLY_EVAL,
        POLY_EVAL_HOMOMORPHIC_IMAGE, .. } := D.core4
  let { POLY_EXTEND_EVALUATE, POLY_EXTEND_ID, POLY_RING, POLY_SUBRING_GENERATED_1,
        POLY_VAR_UNIV, QUOTIENT_RING, QUOTIENT_RING_0, RING_0, .. } := D.core5
  let { RING_COPRIME_00, RING_COPRIME_HOMOMORPHIC_IMAGE, RING_COSET_EQ,
        RING_COSET_EQ_IDEAL, RING_EPIMORPHISM_RING_COSET, RING_HOMOMORPHISM_0,
        RING_HOMOMORPHISM_COMPOSE, RING_HOMOMORPHISM_POLY_CONST,
        RING_HOMOMORPHISM_POLY_EVAL, RING_HOMOMORPHISM_POLY_RINGS,
        RING_HOMOMORPHISM_RING_COSET, RING_ISOMORPHISM_IMP_MONOMORPHISM,
        RING_MONOMORPHISM_ALT, RING_MONOMORPHISM_COMPOSE, RING_MONOMORPHISM_EQ,
        RING_MONOMORPHISM_FROM_SUBRING_GENERATED, RING_MONOMORPHISM_I,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MONOMORPHISM_INCLUSION,
        RING_MONOMORPHISM_INTO_SUBRING, .. } := D.core6
  let { RING_SUB_RZERO, RING_UNIT_NOT_IN_PRIME_IDEAL, RING_UNIT_POLY_CONST,
        RING_UNIT_POLY_DOMAIN, SIMPLE_IMAGE, SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE,
        SUBRING_GENERATED_BY_SUBRING_GENERATED, SUBRING_GENERATED_EQ, .. } := D.core7
  let { SUBRING_GENERATED_RING_CARRIER, SUBRING_SUBRING_GENERATED, SUBSET,
        UFD_PRIME_FACTOR_EXISTS, isomorphic_ring, .. } := D.core8
  let { o_ASSOC, o_THM, poly_eval, ring_epimorphism, ring_homomorphism,
        ring_monomorphism, ring_prime, .. } := D.core9
  let { subfield_of, .. } := BSubfields
  let { SUBRING_EQ_SUBFIELD_GENERATED, .. } := BSubfieldGenerated
  -- @@SCOPE END

  let field_extension ← new_definition
   r"field_extension (k,l) (h:A->B) <=>
        field k /\ field l /\ ring_monomorphism(k,l) h"

  let FIELD_EXTENSION_IMP_MONOMORPHISM ← prove
   r"!(h:A->B) k l. field_extension (k,l) h ==> ring_monomorphism(k,l) h"
   (SIMP_TAC [field_extension])

  let FIELD_EXTENSION_IMP_HOMOMORPHISM ← prove
   r"!(h:A->B) k l. field_extension (k,l) h ==> ring_homomorphism(k,l) h"
   (SIMP_TAC [field_extension, ring_monomorphism])

  let FIELD_EXTENSION_IMP_SUBSET ← prove
   r"!(h:A->B) k l.
        field_extension (k,l) h
        ==> IMAGE h (ring_carrier k) SUBSET ring_carrier l"
   (MESON_TAC [FIELD_EXTENSION_IMP_HOMOMORPHISM, ring_homomorphism])

  let FIELD_EXTENSION_CARRIER ← prove
   r"!(h:A->B) k l x.
        field_extension (k,l) h /\ x IN ring_carrier k
        ==> h x IN ring_carrier l"
   (REWRITE_TAC [field_extension, ring_monomorphism, ring_homomorphism] THEN
    SET_TAC [])

  let FIELD_EXTENSION_FROM_SUBRING_GENERATED ← prove
   r"!(h:A->B) k l.
        field_extension (k,l) h /\ field(subring_generated k s)
        ==> field_extension(subring_generated k s,l) h"
   (SIMP_TAC [field_extension, RING_MONOMORPHISM_FROM_SUBRING_GENERATED])

  let FIELD_EXTENSION_EQ ← prove
   r"!k l (f:A->B) f'.
        field_extension(k,l) f /\
        (!x. x IN ring_carrier k ==> f' x = f x)
        ==> field_extension (k,l) f'"
   (REWRITE_TAC [field_extension] THEN MESON_TAC [RING_MONOMORPHISM_EQ])

  let FIELD_EXTENSION_REFL ← prove
   r"!k:A ring. field_extension (k,k) I <=> field k"
   (REWRITE_TAC [field_extension, RING_MONOMORPHISM_I])

  let FIELD_EXTENSION_TRANS ← prove
   r"!(f:A->B) (g:B->C) k l m.
        field_extension (k,l) f /\ field_extension (l,m) g
        ==> field_extension (k,m) (g o f)"
   (SIMP_TAC [field_extension] THEN MESON_TAC [RING_MONOMORPHISM_COMPOSE])

  let FIELD_EXTENSION_TRANS_I ← prove
   r"!(k:A ring) l m.
     field_extension (k,l) I /\ field_extension (l,m) I
     ==> field_extension (k,m) I"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP FIELD_EXTENSION_TRANS) THEN
    REWRITE_TAC [I_O_ID])

  let FIELD_EXTENSION_ISOMORPHISM ← prove
   r"!(f:A->B) k l.
        (field k \/ field l) /\ ring_isomorphism (k,l) f
        ==> field_extension (k,l) f"
   (REWRITE_TAC [field_extension] THEN
    MESON_TAC [ISOMORPHIC_RING_FIELDNESS, isomorphic_ring,
              RING_ISOMORPHISM_IMP_MONOMORPHISM])

  let FIELD_EXTENSION_SUBRING_GENERATED ← prove
   r"!(l:A ring) k.
        field_extension(subring_generated l k,l) I <=>
        field l /\ ring_carrier(subring_generated l k) subfield_of l"
   (REWRITE_TAC [field_extension, subfield_of] THEN
    REWRITE_TAC [SUBRING_SUBRING_GENERATED] THEN
    REWRITE_TAC [← REWRITE_RULE [← GSYM I_DEF] RING_MONOMORPHISM_INCLUSION] THEN
    REWRITE_TAC [SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
    REWRITE_TAC [CONJ_ACI])

  let FIELD_EXTENSION_INTO_SUBRING_GENERATED ← prove
   r"!(h:A->B) k l s.
        field_extension(k,l) h /\
        s subfield_of l /\
        IMAGE h (ring_carrier k) SUBSET s
        ==> field_extension(k,subring_generated l s) h"
   (REWRITE_TAC [field_extension, subfield_of] THEN
    SIMP_TAC [RING_MONOMORPHISM_INTO_SUBRING])

  let FIELD_EXTENSION_INTO_SUBFIELD_GENERATED ← prove
   r"!(h:A->B) k l s.
        field_extension(k,l) h /\
        s subfield_of l /\
        IMAGE h (ring_carrier k) SUBSET s
        ==> field_extension(k,subfield_generated l s) h"
   (MESON_TAC [SUBRING_EQ_SUBFIELD_GENERATED, subfield_of,
              FIELD_EXTENSION_INTO_SUBRING_GENERATED])

  let KRONECKER_FIELD_EXTENSION ← prove
   r"!(k:A ring) j.
        field k /\ maximal_ideal (poly_ring k (:1)) j
        ==> field_extension (k,quotient_ring (poly_ring k (:1)) j)
                            (ring_coset (poly_ring k (:1)) j o poly_const k)"
   (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [field_extension] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
    ASM_SIMP_TAC [FIELD_QUOTIENT_RING] THEN
    REWRITE_TAC [RING_MONOMORPHISM_ALT] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
      EXISTS_TAC (← q r"poly_ring (k:A ring) (:1)") THEN
      REWRITE_TAC [RING_HOMOMORPHISM_POLY_CONST] THEN
      ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET],
      ALL_TAC] THEN
    X_GEN_TAC (← q r"x:A") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC [QUOTIENT_RING_0, o_THM, RING_COSET_EQ_IDEAL, POLY_CONST] THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"x:A"] FIELD_UNIT) THEN
    ASM_CASES_TAC (← q r"x:A = ring_0 k") THEN ASM_REWRITE_TAC [] THEN
    REPEAT DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q "(:1)", ← q r"x:A"] RING_UNIT_POLY_CONST) THEN
    ASM_MESON_TAC [RING_UNIT_NOT_IN_PRIME_IDEAL, MAXIMAL_IMP_PRIME_IDEAL])

  let KRONECKER_SIMPLE_FIELD_EXTENSION ← prove
   r"!(k:A ring) p.
      field k /\
      p IN ring_carrier(poly_ring k (:1)) /\ ~(poly_deg k p = 0) /\
      ~(?x. x IN ring_carrier k /\ poly_eval k p x = ring_0 k)
      ==> ?l h z:((1->num)->A)->bool.
                field_extension(k,l) h /\
                z IN ring_carrier l /\
                ~(z IN IMAGE h (ring_carrier k)) /\
                subring_generated l (z INSERT IMAGE h (ring_carrier k)) = l /\
                poly_eval l (h o p) z = ring_0 l"
   (← do
    let t1 ← TAUT (← q r"(p ==> ~r) /\ q /\ r ==> ~p /\ q /\ r")
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"poly_ring (k:A ring) (:1)", ← q r"p:(1->num)->A"]
      UFD_PRIME_FACTOR_EXISTS) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [PID_IMP_UFD, PID_POLY_RING, RING_UNIT_POLY_DOMAIN,
                   INTEGRAL_DOMAIN_POLY_RING, FIELD_IMP_INTEGRAL_DOMAIN] THEN
      ASM_MESON_TAC [POLY_DEG_0, POLY_DEG_CONST, POLY_RING],
      DISCH_THEN (X_CHOOSE_THEN (← q r"q:(1->num)->A") STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN (← q r"q IN ring_carrier(poly_ring (k:A ring) (:1))") ASSUME_TAC THENL
     [ASM_MESON_TAC [ring_prime], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"q = ring_0 (poly_ring (k:A ring) (:1))") THENL
     [ASM_MESON_TAC [ring_prime], ALL_TAC] THEN
    MAP_EVERY ABBREV_TAC
     [← q r"j = ideal_generated (poly_ring (k:A ring) (:1)) {q}",
      ← q r"l = quotient_ring (poly_ring (k:A ring) (:1)) j",
      ← q r"h = ring_coset (poly_ring (k:A ring) (:1)) j o poly_const k",
      ← q r"z = ring_coset (poly_ring (k:A ring) (:1)) j (poly_var k one)"] THEN
    MAP_EVERY EXISTS_TAC
     [← q r"l:(((1->num)->A)->bool)ring",
      ← q r"h:A->((1->num)->A)->bool",
      ← q r"z:((1->num)->A)->bool"] THEN
      SUBGOAL_THEN (← q r"maximal_ideal (poly_ring (k:A ring) (:1)) j") ASSUME_TAC THENL
     [EXPAND_TAC "j" THEN ASM_SIMP_TAC [MAXIMAL_IDEAL_SING, PID_POLY_RING] THEN
      ASM_SIMP_TAC [INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE,
                   INTEGRAL_DOMAIN_POLY_RING, FIELD_IMP_INTEGRAL_DOMAIN],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(z:((1->num)->A)->bool) IN ring_carrier l") ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["z", "l"] THEN
      ASM_SIMP_TAC [QUOTIENT_RING, MAXIMAL_IMP_RING_IDEAL] THEN
      EXPAND_TAC "z" THEN REWRITE_TAC [SIMPLE_IMAGE, ETA_AX] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC [POLY_VAR_UNIV],
      ASM_REWRITE_TAC []] THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"j:((1->num)->A)->bool"]
      KRONECKER_FIELD_EXTENSION) THEN
    ASM_REWRITE_TAC [field_extension] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC t1 THEN
    CONJ_TAC THENL
     [REWRITE_TAC [IN_IMAGE] THEN
      ASM_MESON_TAC [RING_MONOMORPHISM_ALT, POLY_EVAL,
                    POLY_EVAL_HOMOMORPHIC_IMAGE],
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [SUBRING_GENERATED_EQ] THEN
      MAP_EVERY EXPAND_TAC ["h", "z"] THEN
      REWRITE_TAC [IMAGE_o, ← GSYM (← CONJUNCT2 IMAGE_CLAUSES)] THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP RING_EPIMORPHISM_RING_COSET o
          MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
      ASM_REWRITE_TAC [ring_epimorphism] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← (SPEC
       (← q r"poly_var (k:A ring) one INSERT IMAGE (poly_const k) (ring_carrier k)") o
       MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE)) th))) THEN
      ASM_REWRITE_TAC [POLY_SUBRING_GENERATED_1,
                      SUBRING_GENERATED_RING_CARRIER] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC [SUBSET, FORALL_IN_INSERT, FORALL_IN_IMAGE] THEN
      SIMP_TAC [POLY_VAR_UNIV, POLY_CONST],
      ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP RING_HOMOMORPHISM_RING_COSET o
          MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
    DISCH_THEN (MP_TAC o MATCH_MP
     (← REWRITE_RULE [IMP_CONJ] POLY_EVAL_HOMOMORPHIC_IMAGE)) THEN
    ASM_REWRITE_TAC [IMP_IMP] THEN
    MAP_EVERY EXPAND_TAC ["h", "z"] THEN REWRITE_TAC [← GSYM o_ASSOC, o_THM] THEN
    DISCH_THEN (fun th => wPart lhand (rand o rand) th) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [POLY_VAR_UNIV] THEN
      MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
      EXISTS_TAC (← q r"k:A ring") THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_POLY_CONST],
      DISCH_THEN (SUBST1_TAC o SYM)] THEN
    FIRST_ASSUM (SUBST1_TAC o SYM o MATCH_MP RING_HOMOMORPHISM_0 o
      MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    EXPAND_TAC "h" THEN REWRITE_TAC [o_THM] THEN
    REWRITE_TAC [poly_eval] THEN
    REWRITE_TAC [← GSYM (← MATCH_MP POLY_EXTEND_EVALUATE
     (← ISPECL [← q r"k:A ring", ← q "(:1)"] RING_HOMOMORPHISM_POLY_CONST))] THEN
    ASM_SIMP_TAC [ETA_ONE, POLY_EXTEND_ID, ETA_AX] THEN
    ASM_SIMP_TAC [RING_COSET_EQ, POLY_CONST, RING_0, MAXIMAL_IMP_RING_IDEAL] THEN
    ASM_SIMP_TAC [POLY_CONST_0, POLY_CLAUSES, RING_SUB_RZERO] THEN
    EXPAND_TAC "j" THEN ASM_SIMP_TAC [IN_IDEAL_GENERATED_SING]))

  let COPRIME_POLY_NO_COMMON_ROOT ← prove
   r"!(k:A ring) (l:B ring) (h:A->B) p q.
        field_extension(k,l) h /\ ring_coprime(poly_ring k (:1)) (p, q)
        ==> ~(?x. x IN ring_carrier l /\
                  poly_eval l (h o p) x = ring_0 l /\
                  poly_eval l (h o q) x = ring_0 l)"
   (REWRITE_TAC [field_extension] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"y:B") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL
     [← q r"poly_ring (k:A ring) (:1)", ← q r"l:B ring",
      ← q r"(\q. poly_eval l q y) o (\p. (h:A->B) o p)",
      ← q r"p:(1->num)->A", ← q r"q:(1->num)->A"] RING_COPRIME_HOMOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC [RING_COPRIME_00, FIELD_IMP_NONTRIVIAL_RING,
                 PID_POLY_RING, PID_IMP_BEZOUT_RING, o_THM] THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
    EXISTS_TAC (← q r"poly_ring (l:B ring) (:1)") THEN
    ASM_SIMP_TAC [RING_HOMOMORPHISM_POLY_RINGS, RING_HOMOMORPHISM_POLY_EVAL,
                 RING_MONOMORPHISM_IMP_HOMOMORPHISM])

  let COPRIME_POLY_NO_COMMON_ROOT_I ← prove
   r"!(k:A ring) (E:A ring) p q.
        field_extension(k,E) I /\
        ring_coprime(poly_ring k (:1)) (p, q)
        ==> ~(?x. x IN ring_carrier E /\
                  poly_eval E p x = ring_0 E /\
                  poly_eval E q x = ring_0 E)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"E:A ring", ← q r"I:A->A",
                   ← q r"p:(1->num)->A", ← q r"q:(1->num)->A"]
      COPRIME_POLY_NO_COMMON_ROOT) THEN
    ASM_REWRITE_TAC [I_O_ID] THEN EXISTS_TAC (← q r"x:A") THEN ASM_REWRITE_TAC [])

  -- @@RETURN BEGIN
  return { field_extension, FIELD_EXTENSION_IMP_MONOMORPHISM,
           FIELD_EXTENSION_IMP_HOMOMORPHISM, FIELD_EXTENSION_IMP_SUBSET,
           FIELD_EXTENSION_CARRIER, FIELD_EXTENSION_FROM_SUBRING_GENERATED,
           FIELD_EXTENSION_EQ, FIELD_EXTENSION_REFL, FIELD_EXTENSION_TRANS,
           FIELD_EXTENSION_TRANS_I, FIELD_EXTENSION_ISOMORPHISM,
           FIELD_EXTENSION_SUBRING_GENERATED, FIELD_EXTENSION_INTO_SUBRING_GENERATED,
           FIELD_EXTENSION_INTO_SUBFIELD_GENERATED, KRONECKER_FIELD_EXTENSION,
           KRONECKER_SIMPLE_FIELD_EXTENSION, COPRIME_POLY_NO_COMMON_ROOT,
           COPRIME_POLY_NO_COMMON_ROOT_I }
  -- @@RETURN END

/-- `CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV ss lev`, as a function of
    the theorem list (used with `ASM`); `ss` is evaluated by the caller, as
    OCaml evaluates `basic_ss []` when it builds the tactic. (as in
    RingTheory.lean's `simpTac`) -/
def simpTac [HolBase] (ss : HolCore.Simp.simpset) (lev : Int) (ths : List thm) : tactic :=
  fun g => do
    match ← HolCore.Simp.GEN_SIMPLIFY_CONV HolBase.B (HolCore.Simp.TOP_DEPTH_SQCONV HolBase.B)
        ss lev ths with
    | .ok c => CONV_TAC c g
    | .error e => pure (.error e)

/- ------------------------------------------------------------------------- -/
/- Linear span of a set of elements s in l with respect to a subfield/ring   -/
/- k, identified by a monomorphism h from k into l. The definition forces it -/
/- to be a subset of the carrier of l, regardless of other hypotheses.       -/
/- ------------------------------------------------------------------------- -/

structure RingSpan where
  -- @@FIELDS
  ring_span_RULES : thm
  ring_span_INDUCT : thm
  ring_span_CASES : thm
  RING_SPAN_0 : thm
  RING_SPAN_INC : thm
  RING_SPAN_ADD : thm
  RING_SPAN_MUL : thm
  RING_SPAN_SUBSET : thm
  RING_SPAN_SUPERSET_GEN : thm
  RING_SPAN_SUPERSET : thm
  RING_SPAN_SUPERSET_EQ : thm
  RING_SPAN_MONO : thm
  SUBSET_RING_SPAN : thm
  RING_SPAN_RESTRICT : thm
  RING_SPAN_SPAN : thm
  RING_SPAN_FINITARY : thm
  RING_SPAN_NONEMPTY : thm
  RING_SPAN_SELF : thm
  RING_SPAN_EMPTY : thm
  RING_SPAN_NEG : thm
  RING_SPAN_SUB : thm
  RING_SPAN_SUM : thm
  RING_SPAN_UNION : thm
  RING_SPAN_SING : thm
  RING_SPAN_EXCHANGE : thm
  RING_SPAN_FINITE : thm
  RING_SPAN_HOMOMORPHIC_IMAGE : thm
  deriving Inhabited

@[nospecialize]
def setupRingSpan [HolBase] (D : FieldTheoryDeps) :
    ExceptT String IO RingSpan := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, ASM_METIS_TAC, MESON_TAC, RING_RULE, RING_TAC, SET_RULE,
        SET_TAC, basic_ss, .. } := D
  let { CONJ_ASSOC, EMPTY_SUBSET, EQ_IMP, .. } := D.core1
  let { FIELD_MUL_LINV, FINITE_EMPTY, FINITE_INDUCT_STRONG, FINITE_SING, FINITE_UNION,
        FORALL_AND_THM, FORALL_IN_GSPEC, FORALL_IN_IMAGE, FORALL_IN_INSERT,
        FORALL_IN_UNION, FORALL_UNWIND_THM2, FUN_IN_IMAGE, .. } := D.core2
  let { IMP_CONJ, IMP_IMP, INSERT_SUBSET, INTER_SUBSET, IN_ELIM_THM, IN_INTER, IN_SING,
        IN_UNION, LEFT_IMP_EXISTS_THM, .. } := D.core3
  let { MEMBER_NOT_EMPTY, NOT_IN_EMPTY, .. } := D.core4
  let { RIGHT_FORALL_IMP_THM, RIGHT_IMP_FORALL_THM, RING_0, RING_1, RING_ADD,
        RING_ADD_LDISTRIB, RING_ADD_LZERO, RING_ADD_RZERO, .. } := D.core5
  let { RING_INV, RING_MUL, .. } := D.core6
  let { RING_MUL_LID, RING_MUL_LZERO, RING_MUL_RZERO, RING_NEG, RING_SUM_CLAUSES,
        RING_SUM_CLOSED, RING_SUM_EQ, SING_SUBSET, .. } := D.core7
  let { SUBSET, SUBSET_ANTISYM, SUBSET_ANTISYM_EQ, SUBSET_REFL, SUBSET_TRANS,
        UNION_SUBSET, .. } := D.core8
  let { o_THM, ring_homomorphism, ring_sub, .. } := D.core9
  -- @@SCOPE END

  let (ring_span_RULES, ring_span_INDUCT, ring_span_CASES) ← do
    let (thr, thi, thc) ← ExceptT.mk (D.new_inductive_set
     (← q r"(ring_0 (SND kl) IN ring_span kl (h:A->B) s) /\
    (!x. x IN s /\ x IN ring_carrier(SND kl) ==> x IN ring_span kl h s) /\
    (!x y. x IN ring_span kl h s /\ y IN ring_span kl h s
           ==> ring_add (SND kl) x y IN ring_span kl h s) /\
    (!a x. a IN ring_carrier(FST kl) /\
           h a IN ring_carrier(SND kl) /\
           x IN ring_span kl h s
           ==> ring_mul (SND kl) (h a) x IN ring_span kl h s)"))
    let l ← [thr, thi, thc].mapM (fun th => do
      GENL [(← q r"h:A->B"), (← q "k:A ring"), (← q "l:B ring")]
        (← REWRITE_RULE []
          (← SPECL [(← q r"(k:A ring),(l:B ring)"), (← q r"h:A->B")] th)))
    match l with
    | [a, b, c] => pure (a, b, c)
    | _ => throw "Match_failure"

  let (RING_SPAN_0, RING_SPAN_INC, RING_SPAN_ADD, RING_SPAN_MUL) ← do
    let l ← pure (CONJUNCTS (← REWRITE_RULE [FORALL_AND_THM] ring_span_RULES))
    match l with
    | [a, b, c, d] => pure (a, b, c, d)
    | _ => throw "Match_failure"

  let RING_SPAN_SUBSET ← prove
   r"!(h:A->B) k l s. ring_span (k,l) h s SUBSET ring_carrier l"
   (REPEAT GEN_TAC THEN REWRITE_TAC [SUBSET] THEN
    MATCH_MP_TAC ring_span_INDUCT THEN
    ASM_SIMP_TAC [RING_0, RING_ADD, RING_MUL])

  let RING_SPAN_SUPERSET_GEN ← prove
   r"!(h:A->B) k l s. ring_carrier l INTER s SUBSET ring_span (k,l) h s"
   (SET_TAC [RING_SPAN_INC])

  let RING_SPAN_SUPERSET ← prove
   r"!(h:A->B) k l s.
        s SUBSET ring_carrier l ==> s SUBSET ring_span (k,l) h s"
   (SET_TAC [RING_SPAN_SUPERSET_GEN])

  let RING_SPAN_SUPERSET_EQ ← prove
   r"!(h:A->B) k l s. s SUBSET ring_span (k,l) h s <=> s SUBSET ring_carrier l"
   (SET_TAC [RING_SPAN_INC, RING_SPAN_SUBSET])

  let RING_SPAN_MONO ← prove
   r"!(h:A->B) k l s t.
        s SUBSET t ==> ring_span (k,l) h s SUBSET ring_span (k,l) h t"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [SUBSET] THEN MATCH_MP_TAC ring_span_INDUCT THEN
    ASM_REWRITE_TAC [RING_SPAN_0, RING_SPAN_ADD, RING_SPAN_MUL] THEN
    ASM SET_TAC [RING_SPAN_INC])

  let SUBSET_RING_SPAN ← prove
   r"!(h:A->B) k l s t.
        ring_span (k,l) h s SUBSET ring_span (k,l) h t <=>
        ring_carrier l INTER s SUBSET ring_span (k,l) h t"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [MESON_TAC [RING_SPAN_SUPERSET_GEN, SUBSET_TRANS],
      REWRITE_TAC [SUBSET] THEN STRIP_TAC] THEN
    MATCH_MP_TAC ring_span_INDUCT THEN ASM SET_TAC [ring_span_RULES])

  let RING_SPAN_RESTRICT ← prove
   r"!(h:A->B) k l s.
        ring_span (k,l) h s = ring_span (k,l) h (ring_carrier l INTER s)"
   (REPEAT GEN_TAC THEN
    SIMP_TAC [← GSYM SUBSET_ANTISYM_EQ, INTER_SUBSET, RING_SPAN_MONO] THEN
    REWRITE_TAC [SUBSET] THEN MATCH_MP_TAC ring_span_INDUCT THEN
    ASM_MESON_TAC [RING_SPAN_0, RING_SPAN_ADD, RING_SPAN_MUL,
                   RING_SPAN_INC, IN_INTER])

  let RING_SPAN_SPAN ← prove
   r"!(h:A->B) k l s.
        ring_span (k,l) h (ring_span (k,l) h s) = ring_span (k,l) h s"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN
    MESON_TAC [SUBSET_RING_SPAN, RING_SPAN_SUPERSET_GEN, SUBSET, IN_INTER,
               RING_SPAN_RESTRICT])

  let RING_SPAN_FINITARY ← prove
   r"!(h:A->B) k l s a.
        a IN ring_span (k,l) h s
        ==> ?t. FINITE t /\ t SUBSET s /\ a IN ring_span (k,l) h t"
   (REPLICATE_TAC 4 GEN_TAC THEN MATCH_MP_TAC ring_span_INDUCT THEN
    REWRITE_TAC [RING_SPAN_0] THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC (← q r"{}:B->bool") THEN ASM_REWRITE_TAC [FINITE_EMPTY, EMPTY_SUBSET],
      X_GEN_TAC (← q "x:B") THEN DISCH_TAC THEN EXISTS_TAC (← q r"{x:B}") THEN
      ASM_SIMP_TAC [FINITE_SING, SING_SUBSET, RING_SPAN_INC, IN_SING],
      MAP_EVERY X_GEN_TAC [(← q "x:B"), (← q "y:B")] THEN
      DISCH_THEN (CONJUNCTS_THEN2
       (X_CHOOSE_TAC (← q r"t:B->bool")) (X_CHOOSE_TAC (← q r"u:B->bool"))) THEN
      EXISTS_TAC (← q r"t UNION u:B->bool") THEN
      ASM_REWRITE_TAC [FINITE_UNION, UNION_SUBSET, SUBSET_REFL] THEN
      MATCH_MP_TAC RING_SPAN_ADD THEN
      ASM_MESON_TAC [RING_SPAN_MONO, SUBSET, IN_UNION],
      MESON_TAC [RING_SPAN_MUL]])

  let RING_SPAN_NONEMPTY ← prove
   r"!(h:A->B) k l s. ~(ring_span (k,l) h s = {})"
   (MESON_TAC [MEMBER_NOT_EMPTY, RING_SPAN_0])

  let RING_SPAN_SELF ← prove
   r"!(h:A->B) l k. ring_span (k,l) h (ring_carrier l) = ring_carrier l"
   (MESON_TAC [RING_SPAN_SUPERSET, RING_SPAN_SUBSET, SUBSET_ANTISYM,
               SUBSET_REFL])

  let RING_SPAN_EMPTY ← prove
   r"!(h:A->B) k l.
        ring_homomorphism(k,l) h ==> ring_span (k,l) h {} = {ring_0 l}"
   (REWRITE_TAC [ring_homomorphism, SUBSET, FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, SING_SUBSET, RING_SPAN_0] THEN
    REWRITE_TAC [SUBSET] THEN MATCH_MP_TAC ring_span_INDUCT THEN
    REWRITE_TAC [IN_SING, NOT_IN_EMPTY] THEN
    ASM_SIMP_TAC [RING_MUL_RZERO, RING_0, RING_ADD_RZERO])

  let RING_SPAN_NEG ← prove
   r"!(h:A->B) k l s x.
        ring_homomorphism(k,l) h /\ x IN ring_span (k,l) h s
        ==> ring_neg l x IN ring_span (k,l) h s"
   (REPEAT STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ring_homomorphism, SUBSET, FORALL_IN_IMAGE]) THEN
    MP_TAC (← ISPECL [(← q r"h:A->B"), (← q "k:A ring"), (← q "l:B ring"), (← q r"s:B->bool"),
                   (← q r"ring_neg k (ring_1 k):A"), (← q "x:B")] RING_SPAN_MUL) THEN
    ASM_SIMP_TAC [RING_NEG, RING_1] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN RING_TAC THEN
    ASM_MESON_TAC [RING_SPAN_SUBSET, SUBSET, RING_0, RING_1])

  let RING_SPAN_SUB ← prove
   r"!(h:A->B) k l s x y.
        ring_homomorphism(k,l) h /\
        x IN ring_span (k,l) h s /\ y IN ring_span (k,l) h s
        ==> ring_sub l x y IN ring_span (k,l) h s"
   (MESON_TAC [ring_sub, RING_SPAN_NEG, RING_SPAN_ADD])

  let RING_SPAN_SUM ← prove
   r"!(h:A->B) k l f s (t:K->bool).
        (!i. i IN t ==> f i IN ring_span (k,l) h s)
        ==> ring_sum l t f IN ring_span (k,l) h s"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [(← q "l:B ring"), (← q r"\x. x IN ring_span (k,l) (h:A->B) s"), (← q r"f:K->B")]
          RING_SUM_CLOSED) THEN
    REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC [RING_SPAN_ADD, RING_SPAN_0])

  let RING_SPAN_UNION ← prove
   r"!(h:A->B) k l s t.
        ring_homomorphism(k,l) h
        ==> ring_span (k,l) h (s UNION t) =
            { ring_add l x y | x,y |
              x IN ring_span (k,l) h s /\ y IN ring_span (k,l) h t}"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ring_span_INDUCT,
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_SPAN_ADD THEN
      ASM_MESON_TAC [RING_SPAN_MONO, SUBSET, IN_UNION]] THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC] THEN
    REWRITE_TAC [UNION_SUBSET, FORALL_IN_UNION, IN_ELIM_THM] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [SUBSET]) THEN REPEAT CONJ_TAC THENL
     [REPEAT (EXISTS_TAC (← q r"ring_0 l:B")) THEN
      ASM_SIMP_TAC [RING_ADD_LZERO, RING_0, RING_SPAN_0],
      X_GEN_TAC (← q "x:B") THEN REPEAT DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [(← q "x:B"), (← q r"ring_0 l:B")] THEN
      ASM_SIMP_TAC [RING_SPAN_0, RING_SPAN_INC, RING_ADD_RZERO],
      X_GEN_TAC (← q "x:B") THEN REPEAT DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [(← q r"ring_0 l:B"), (← q "x:B")] THEN
      ASM_SIMP_TAC [RING_SPAN_0, RING_SPAN_INC, RING_ADD_LZERO],
      REWRITE_TAC [RIGHT_IMP_FORALL_THM] THEN
      MAP_EVERY X_GEN_TAC [(← q "x1:B"), (← q "y1:B"), (← q "x2:B"), (← q "y2:B")] THEN
      REPEAT DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [(← q r"ring_add l x1 x2:B"), (← q r"ring_add l y1 y2:B")] THEN
      ASM_SIMP_TAC [RING_SPAN_ADD] THEN RING_TAC THEN
      ASM_MESON_TAC [RING_SPAN_SUBSET, SUBSET],
      REWRITE_TAC [RIGHT_IMP_FORALL_THM] THEN
      MAP_EVERY X_GEN_TAC [(← q "c:A"), (← q "x:B"), (← q "y:B")] THEN
      REPEAT DISCH_TAC THEN MAP_EVERY EXISTS_TAC
       [(← q r"ring_mul l ((h:A->B) c) x"), (← q r"ring_mul l ((h:A->B) c) y")] THEN
      ASM_SIMP_TAC [RING_SPAN_MUL] THEN RING_TAC THEN
      MP_TAC (← ISPECL [(← q r"h:A->B"), (← q "k:A ring"), (← q "l:B ring")]
        RING_SPAN_SUBSET) THEN
      ASM_REWRITE_TAC [SUBSET] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [ring_homomorphism]) THEN ASM SET_TAC []])

  let RING_SPAN_SING ← prove
   r"!(h:A->B) k l x.
        ring_homomorphism(k,l) h /\ x IN ring_carrier l
        ==> ring_span (k,l) h {x} =
            { ring_mul l (h c) x | c | c IN ring_carrier k}"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ring_homomorphism, SUBSET, FORALL_IN_IMAGE]) THEN
    ASM_SIMP_TAC [RING_SPAN_MUL, RING_SPAN_INC, IN_SING] THEN
    MATCH_MP_TAC ring_span_INDUCT THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [SUBSET]) THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC (← q r"ring_0 k:A") THEN ASM_SIMP_TAC [RING_MUL_LZERO, RING_0],
      REWRITE_TAC [IN_SING, FORALL_UNWIND_THM2] THEN DISCH_TAC THEN
      EXISTS_TAC (← q r"ring_1 k:A") THEN ASM_SIMP_TAC [RING_MUL_LID, RING_1],
      REWRITE_TAC [RIGHT_IMP_FORALL_THM] THEN
      MAP_EVERY X_GEN_TAC [(← q "c:A"), (← q "d:A")] THEN REPEAT DISCH_TAC THEN
      EXISTS_TAC (← q r"ring_add k c d:A"),
      REWRITE_TAC [RIGHT_IMP_FORALL_THM] THEN
      MAP_EVERY X_GEN_TAC [(← q "c:A"), (← q "d:A")] THEN REPEAT DISCH_TAC THEN
      EXISTS_TAC (← q r"ring_mul k c d:A")] THEN
    ASM_SIMP_TAC [RING_ADD, RING_MUL] THEN RING_TAC THEN ASM_SIMP_TAC [])

  let RING_SPAN_EXCHANGE ← prove
   r"!(h:A->B) k l s a b.
        field k /\ ring_homomorphism(k,l) h /\
        a IN ring_span (k,l) h (b INSERT s) /\ ~(a IN ring_span (k,l) h s)
        ==> b IN ring_span (k,l) h (a INSERT s)"
   (← do
    let r3 ← RING_RULE
      (← q r"ring_mul r c' c = ring_1 r
     ==> b = ring_add r (ring_add r (ring_mul r c' (ring_mul r c b)) x)
                        (ring_neg r x)")
    let ss2 ← ExceptT.mk (basic_ss [])
    let s3 ← SET_RULE
     (← q r"{f x y | x IN {g z | P z} /\ Q y} = {f (g z) y |y,z| P z /\ Q y}")
    let s2 ← SET_RULE (← q r"a INSERT s = {a} UNION s")
    let s1 ← SET_RULE
      (← q r"~(b IN l) ==> l INTER (b INSERT s) = l INTER s")
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"(b:B) IN ring_carrier l") THENL
     [ALL_TAC,
      ASM_METIS_TAC [RING_SPAN_RESTRICT, s1]] THEN
    REPLICATE_TAC 2 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    ASM_CASES_TAC (← q r"(a:B) IN ring_carrier l") THENL
     [ONCE_REWRITE_TAC [s2],
      ASM_MESON_TAC [RING_SPAN_SUBSET, SUBSET, INSERT_SUBSET]] THEN
    ASM_SIMP_TAC [RING_SPAN_UNION, SING_SUBSET, RING_SPAN_SING] THEN
    REWRITE_TAC [s3] THEN
    REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [(← q "x':B"), (← q "c:A")] THEN
    ASM_CASES_TAC (← q r"x':B IN ring_carrier l") THENL
     [ALL_TAC, ASM_MESON_TAC [RING_SPAN_SUBSET, SUBSET]] THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [SUBSET, FORALL_IN_IMAGE] o
          GEN_REWRITE_RULE I [ring_homomorphism]) THEN
    ASM_CASES_TAC (← q r"c:A = ring_0 k") THENL
     [ASM_MESON_TAC [RING_ADD_LZERO, RING_MUL_LZERO], STRIP_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [(← q r"ring_neg l (ring_mul l ((h:A->B)(ring_inv k c)) x')"),
      (← q r"ring_inv k c:A")] THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ring_homomorphism]) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [SUBSET, FORALL_IN_IMAGE]) THEN
    ASM (simpTac ss2 5)
     [RING_SPAN_NEG, RING_SPAN_MUL, RING_INV] THEN
    ASM_SIMP_TAC [RING_ADD_LDISTRIB, RING_ADD, RING_MUL, RING_INV] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_IMP] r3) THEN
    ASM_MESON_TAC [FIELD_MUL_LINV, RING_INV, RING_MUL]))

  let RING_SPAN_FINITE ← prove
   r"!(h:A->B) k l s.
      ring_homomorphism(k,l) h /\ FINITE s /\ s SUBSET ring_carrier l
      ==> ring_span (k,l) h s =
          { ring_sum l s (\x. ring_mul l (h(c x)) x) |c|
            !x. x IN s ==> c x IN ring_carrier k }"
   (← do
    let s3 ← SET_RULE (← q r"{x} UNION s = x INSERT s")
    let s2 ← SET_RULE
     (← q r"{f x y | x IN {g w | P w} /\ y IN {h z | Q z}} =
    {f (g w) (h z) | P w /\ Q z}")
    let s1 ← SET_RULE (← q r"x INSERT s = {x} UNION s")
    pure (REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    REPEAT DISCH_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [← CONJUNCT1 RING_SUM_CLAUSES, RING_SPAN_EMPTY, NOT_IN_EMPTY] THEN
    CONJ_TAC THENL [SET_TAC [], REWRITE_TAC [INSERT_SUBSET]] THEN
    MAP_EVERY X_GEN_TAC [(← q "x:B"), (← q r"s:B->bool")] THEN
    REWRITE_TAC [IMP_IMP, ← GSYM CONJ_ASSOC] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    ONCE_REWRITE_TAC [s1] THEN
    ASM_SIMP_TAC [RING_SPAN_UNION, SING_SUBSET] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC [RING_SPAN_SING, s2] THEN
    REWRITE_TAC [s3] THEN
    REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, SUBSET, FORALL_IN_GSPEC] THEN
    REWRITE_TAC [IN_ELIM_THM, FORALL_IN_INSERT] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [SUBSET]) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [SUBSET, FORALL_IN_IMAGE] o
        GEN_REWRITE_RULE I [ring_homomorphism]) THEN
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [(← q "d:A"), (← q r"c:B->A")] THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"\y. if y = x then d else (c:B->A) y") THEN
      REWRITE_TAC [] THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      ASM_SIMP_TAC [RING_SUM_CLAUSES, RING_MUL] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN ASM_MESON_TAC [],
      X_GEN_TAC (← q r"c:B->A") THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [(← q r"(c:B->A) x"), (← q r"c:B->A")] THEN
      ASM_SIMP_TAC [RING_SUM_CLAUSES, RING_MUL]]))

  let RING_SPAN_HOMOMORPHIC_IMAGE ← prove
   r"!(f:A->B) (g:B->C) k l m s.
        ring_homomorphism(k,l) f /\
        ring_homomorphism(l,m) g /\
        s SUBSET ring_carrier l
        ==> IMAGE g (ring_span (k,l) f s) =
            ring_span (k,m) (g o f) (IMAGE g s)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC (← SET_RULE
       (← q r"!t. (!x. x IN s ==> x IN t /\ f(x) IN u)
          ==> IMAGE f s SUBSET u")) THEN
      EXISTS_TAC (← q r"ring_carrier l:B->bool") THEN
      MATCH_MP_TAC ring_span_INDUCT THEN
      RULE_ASSUM_TAC (REWRITE_RULE
       [ring_homomorphism, SUBSET, FORALL_IN_IMAGE]) THEN
      ASM_SIMP_TAC [RING_0, RING_ADD, RING_MUL, RING_SPAN_0,
                   RING_SPAN_ADD, RING_SPAN_INC, FUN_IN_IMAGE] THEN
      ASM_MESON_TAC [RING_SPAN_MUL, o_THM],
      MP_TAC (← ISPECL [(← q r"f:A->B"), (← q "k:A ring"), (← q "l:B ring"), (← q r"s:B->bool")]
          RING_SPAN_SUBSET) THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET] THEN DISCH_TAC THEN
      MATCH_MP_TAC ring_span_INDUCT THEN
      REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE] THEN
      RULE_ASSUM_TAC (REWRITE_RULE
       [ring_homomorphism, SUBSET, FORALL_IN_IMAGE]) THEN
      ASM_SIMP_TAC [o_THM] THEN
      ASM_MESON_TAC [FUN_IN_IMAGE, RING_SPAN_0, RING_SPAN_ADD, RING_SPAN_MUL,
                    RING_SPAN_INC]])

  -- @@RETURN BEGIN
  return { ring_span_RULES, ring_span_INDUCT, ring_span_CASES, RING_SPAN_0,
           RING_SPAN_INC, RING_SPAN_ADD, RING_SPAN_MUL, RING_SPAN_SUBSET,
           RING_SPAN_SUPERSET_GEN, RING_SPAN_SUPERSET, RING_SPAN_SUPERSET_EQ,
           RING_SPAN_MONO, SUBSET_RING_SPAN, RING_SPAN_RESTRICT, RING_SPAN_SPAN,
           RING_SPAN_FINITARY, RING_SPAN_NONEMPTY, RING_SPAN_SELF, RING_SPAN_EMPTY,
           RING_SPAN_NEG, RING_SPAN_SUB, RING_SPAN_SUM, RING_SPAN_UNION, RING_SPAN_SING,
           RING_SPAN_EXCHANGE, RING_SPAN_FINITE, RING_SPAN_HOMOMORPHIC_IMAGE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Set up the matroid derived from ring_span.                                -/
/- ------------------------------------------------------------------------- -/

structure RingMatroid where
  -- @@FIELDS
  ring_matroid : thm
  RING_MATROID : thm
  deriving Inhabited

@[nospecialize]
def setupRingMatroid [HolBase] (D : FieldTheoryDeps) (BRingSpan : RingSpan) :
    ExceptT String IO RingMatroid := do
  -- @@SCOPE BEGIN
  let { new_definition, .. } := D
  let { PAIR_EQ, .. } := D.core4
  let { matroid_set, matroid_span, matroid_tybij, .. } := D.core8
  let { RING_SPAN_EXCHANGE, RING_SPAN_FINITARY, RING_SPAN_MONO, RING_SPAN_SPAN,
        RING_SPAN_SUBSET, RING_SPAN_SUPERSET, .. } := BRingSpan
  -- @@SCOPE END

  let ring_matroid ← new_definition
   r"ring_matroid (k,l) (h:A->B) = matroid(ring_carrier l,ring_span (k,l) h)"

  let RING_MATROID ← prove
   r"!(h:A->B) k l.
        field k /\ ring_homomorphism(k,l) h
        ==> matroid_set(ring_matroid (k,l) h) = ring_carrier l /\
            matroid_span(ring_matroid (k,l) h) = ring_span (k,l) h"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC [matroid_set, matroid_span] THEN
    REWRITE_TAC [← GSYM PAIR_EQ, ring_matroid] THEN
    REWRITE_TAC [← GSYM (← CONJUNCT2 matroid_tybij)] THEN
    ASM_SIMP_TAC [RING_SPAN_SUBSET, RING_SPAN_SUPERSET, RING_SPAN_MONO,
                 RING_SPAN_SPAN, RING_SPAN_FINITARY, RING_SPAN_EXCHANGE])

  -- @@RETURN BEGIN
  return { ring_matroid, RING_MATROID }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Some linear algebra basics with respect to that notion of span.           -/
/- ------------------------------------------------------------------------- -/

structure LinearAlgebra where
  -- @@FIELDS
  ring_dependent : thm
  ring_independent : thm
  ring_spanning : thm
  ring_basis : thm
  RING_DEPENDENT_IMP_SUBSET : thm
  RING_INDEPENDENT_IMP_SUBSET : thm
  RING_SPANNING_IMP_SUBSET : thm
  RING_BASIS_IMP_SUBSET : thm
  RING_MATROID_INDEPENDENT : thm
  RING_MATROID_SPANNING : thm
  RING_MATROID_BASIS : thm
  RING_BASIS_EXISTS : thm
  RING_SPANNING_CONTAINS_BASIS : thm
  RING_BASES_CARD_EQ : thm
  RING_SPANNING_ALT : thm
  RING_SPANNING_IMP_NONEMPTY : thm
  RING_INDEPENDENT_EMPTY : thm
  RING_INDEPENDENT_NONZERO : thm
  RING_DEPENDENT_MONO : thm
  RING_INDEPENDENT_MONO : thm
  deriving Inhabited

@[nospecialize]
def setupLinearAlgebra [HolBase] (D : FieldTheoryDeps) (BFieldExtension : FieldExtension) (BRingSpan : RingSpan) (BRingMatroid : RingMatroid) :
    ExceptT String IO LinearAlgebra := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, .. } := D
  let { CONTRAPOS_THM, EMPTY_SUBSET, .. } := D.core1
  let { FIELD_IMP_NONTRIVIAL_RING, FUN_EQ_THM, .. } := D.core2
  let { IN_DELETE, MATROID_BASES_CARD_EQ, MATROID_BASIS_EXISTS, .. } := D.core3
  let { MATROID_SPANNING_CONTAINS_BASIS, NOT_IN_EMPTY, .. } := D.core4
  let { SUBSET, SUBSET_ANTISYM_EQ, matroid_basis, matroid_independent,
        matroid_spanning, .. } := D.core8
  let { ring_monomorphism, trivial_ring, .. } := D.core9
  let { field_extension, .. } := BFieldExtension
  let { RING_SPAN_0, RING_SPAN_EMPTY, RING_SPAN_MONO, RING_SPAN_SUBSET, .. } := BRingSpan
  let { RING_MATROID, .. } := BRingMatroid
  -- @@SCOPE END

  let ring_dependent ← D.define
   r"ring_dependent (k,l) (h:A->B) s <=>
        s SUBSET ring_carrier l /\
        ?a. a IN s /\ a IN ring_span (k,l) h (s DELETE a)"

  let ring_independent ← D.define
   r"ring_independent (k,l) (h:A->B) s <=>
        s SUBSET ring_carrier l /\ ~(ring_dependent (k,l) h s)"

  let ring_spanning ← D.define
   r"ring_spanning (k,l) (h:A->B) s <=>
        s SUBSET ring_carrier l /\ ring_span (k,l) h s = ring_carrier l"

  let ring_basis ← D.define
   r"ring_basis (k,l) (h:A->B) s <=>
        ring_independent (k,l) h s /\ ring_spanning (k,l) h s"

  let RING_DEPENDENT_IMP_SUBSET ← prove
   r"!(h:A->B) k l s. ring_dependent (k,l) h s ==> s SUBSET ring_carrier l"
   (SIMP_TAC [ring_dependent])

  let RING_INDEPENDENT_IMP_SUBSET ← prove
   r"!(h:A->B) k l s. ring_independent (k,l) h s ==> s SUBSET ring_carrier l"
   (SIMP_TAC [ring_independent])

  let RING_SPANNING_IMP_SUBSET ← prove
   r"!(h:A->B) k l s. ring_spanning (k,l) h s ==> s SUBSET ring_carrier l"
   (SIMP_TAC [ring_spanning])

  let RING_BASIS_IMP_SUBSET ← prove
   r"!(h:A->B) k l s. ring_basis (k,l) h s ==> s SUBSET ring_carrier l"
   (SIMP_TAC [ring_independent, ring_basis])

  let RING_MATROID_INDEPENDENT ← prove
   r"!(h:A->B) k l.
        field k /\ ring_homomorphism(k,l) h
        ==> (matroid_independent(ring_matroid (k,l) h) =
             ring_independent (k,l) h)"
   (SIMP_TAC [FUN_EQ_THM, matroid_independent, RING_MATROID] THEN
    REWRITE_TAC [ring_independent, ring_dependent] THEN MESON_TAC [])

  let RING_MATROID_SPANNING ← prove
   r"!(h:A->B) k l.
        field k /\ ring_homomorphism(k,l) h
        ==> (matroid_spanning(ring_matroid (k,l) h) =
             ring_spanning (k,l) h)"
   (SIMP_TAC [FUN_EQ_THM, matroid_spanning, ring_spanning, RING_MATROID])

  let RING_MATROID_BASIS ← prove
   r"!(h:A->B) k l.
        field k /\ ring_homomorphism(k,l) h
        ==> (matroid_basis(ring_matroid (k,l) h) =
             ring_basis (k,l) h)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
    ASM_SIMP_TAC [matroid_basis, ring_basis, RING_MATROID_INDEPENDENT,
                 ring_spanning, RING_MATROID_SPANNING] THEN
    MESON_TAC [RING_INDEPENDENT_IMP_SUBSET])

  let RING_BASIS_EXISTS ← prove
   r"!(h:A->B) k l.
        field k /\ ring_homomorphism(k,l) h ==> ?b. ring_basis (k,l) h b"
   (SIMP_TAC [← GSYM RING_MATROID_BASIS, MATROID_BASIS_EXISTS])

  let RING_SPANNING_CONTAINS_BASIS ← prove
   r"!(h:A->B) k l.
        field k /\ ring_homomorphism(k,l) h /\ ring_spanning (k,l) h b
        ==> ?c. c SUBSET b /\ ring_basis (k,l) h c"
   (MESON_TAC [MATROID_SPANNING_CONTAINS_BASIS, RING_MATROID_SPANNING,
               RING_MATROID_BASIS])

  let RING_BASES_CARD_EQ ← prove
   r"!(h:A->B) k l b b'.
        field k /\ ring_homomorphism(k,l) h /\
        ring_basis (k,l) h b /\ ring_basis (k,l) h b'
        ==> b =_c b'"
   (MESON_TAC [RING_MATROID_BASIS, MATROID_BASES_CARD_EQ])

  let RING_SPANNING_ALT ← prove
   r"!(h:A->B) k l.
        ring_spanning (k,l) h s <=>
        s SUBSET ring_carrier l /\ ring_carrier l SUBSET ring_span (k,l) h s"
   (REWRITE_TAC [ring_spanning, ← GSYM SUBSET_ANTISYM_EQ, RING_SPAN_SUBSET])

  let RING_SPANNING_IMP_NONEMPTY ← prove
   r"!(h:A->B) k l b.
        field_extension(k,l) h /\ ring_spanning (k,l) h b ==> ~(b = {})"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"b:B->bool = {}") THEN
    ASM_REWRITE_TAC [field_extension, ring_spanning] THEN
    MESON_TAC [RING_SPAN_EMPTY, ring_monomorphism, trivial_ring,
               FIELD_IMP_NONTRIVIAL_RING])

  let RING_INDEPENDENT_EMPTY ← prove
   r"!(h:A->B) k l. ring_independent (k,l) h {}"
   (REWRITE_TAC [ring_dependent, ring_independent, EMPTY_SUBSET, NOT_IN_EMPTY])

  let RING_INDEPENDENT_NONZERO ← prove
   r"!(h:A->B) k l s. ring_independent (k,l) h s ==> ~(ring_0 l IN s)"
   (REWRITE_TAC [ring_independent, CONTRAPOS_THM, ring_dependent] THEN
    MESON_TAC [RING_SPAN_0])

  let RING_DEPENDENT_MONO ← prove
   r"!(h:A->B) k l s t.
    ring_dependent (k,l) h s /\ s SUBSET t /\ t SUBSET ring_carrier l
    ==> ring_dependent (k,l) h t"
   (REWRITE_TAC [ring_dependent] THEN
    ASM_MESON_TAC [RING_SPAN_MONO, SUBSET, IN_DELETE])

  let RING_INDEPENDENT_MONO ← prove
   r"!(h:A->B) k l s t.
        ring_independent (k,l) h t /\ s SUBSET t
        ==> ring_independent (k,l) h s"
   (REWRITE_TAC [ring_independent, ring_dependent] THEN
    ASM_MESON_TAC [RING_SPAN_MONO, SUBSET, IN_DELETE])

  -- @@RETURN BEGIN
  return { ring_dependent, ring_independent, ring_spanning, ring_basis,
           RING_DEPENDENT_IMP_SUBSET, RING_INDEPENDENT_IMP_SUBSET,
           RING_SPANNING_IMP_SUBSET, RING_BASIS_IMP_SUBSET, RING_MATROID_INDEPENDENT,
           RING_MATROID_SPANNING, RING_MATROID_BASIS, RING_BASIS_EXISTS,
           RING_SPANNING_CONTAINS_BASIS, RING_BASES_CARD_EQ, RING_SPANNING_ALT,
           RING_SPANNING_IMP_NONEMPTY, RING_INDEPENDENT_EMPTY, RING_INDEPENDENT_NONZERO,
           RING_DEPENDENT_MONO, RING_INDEPENDENT_MONO }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Finitary characterizations of (in)dependence and finite versions.         -/
/- (fieldtheory.ml 1867-2117)                                                -/
/- ------------------------------------------------------------------------- -/

structure Finitary where
  -- @@FIELDS
  RING_DEPENDENT_FINITARY : thm
  RING_INDEPENDENT_FINITARY : thm
  RING_INDEPENDENT_LE_SPAN : thm
  RING_DEPENDENT_FINITE : thm
  RING_INDEPENDENT_FINITE : thm
  RING_INDEPENDENT_FINITE_EQ : thm
  RING_DEPENDENT_SPAN_IMAGE : thm
  RING_SPAN_SUBSET_SUBRING_GENERATED : thm
  RING_SPAN_SUBSET_SUBFIELD_GENERATED : thm
  RING_INDEPENDENT_INSERT : thm
  RING_INDEPENDENT_CARD_LE_SPANNING : thm
  deriving Inhabited

@[nospecialize]
def setupFinitary [HolBase] (D : FieldTheoryDeps) (BSubfields : Subfields) (BSubfieldGenerated : SubfieldGenerated) (BRingSpan : RingSpan) (BRingMatroid : RingMatroid) (BLinearAlgebra : LinearAlgebra) :
    ExceptT String IO Finitary := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, SET_RULE, SET_TAC, TAUT, .. } := D
  let { CARD_IMAGE_INJ, COND_ID, COND_RAND, COND_RATOR, CONTRAPOS_THM, DELETE,
        EXISTS_IN_IMAGE, EXISTS_IN_INSERT, .. } := D.core1
  let { FIELD_MUL_LINV, FIELD_NONTRIVIAL, FINITE_DELETE, FINITE_IMAGE, FINITE_INSERT,
        FINITE_RESTRICT, FORALL_IN_IMAGE, FUN_EQ_THM, .. } := D.core2
  let { IMP_CONJ, IMP_IMP, INJECTIVE_ON_ALT, INSERT_SUBSET, IN_DELETE, IN_ELIM_THM,
        IN_IMAGE, IN_SUBRING_1, IN_SUBRING_NEG, LEFT_IMP_EXISTS_THM,
        MATROID_INDEPENDENT_CARD_LE_SPANNING, .. } := D.core3
  let { MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE, MATROID_INDEPENDENT_INSERT,
        MONO_FORALL, NOT_FORALL_THM, NOT_IMP, NOT_LE, .. } := D.core4
  let { RIGHT_AND_EXISTS_THM, RING_0, RING_0_IN_SUBRING_GENERATED, RING_1,
        RING_ADD_ASSOC, RING_ADD_IN_SUBRING_GENERATED, RING_ADD_LZERO, RING_ADD_RNEG, .. } := D.core5
  let { RING_HOMOMORPHISM_SUB, RING_INV, RING_MUL, .. } := D.core6
  let { RING_MUL_ASSOC, RING_MUL_IN_SUBRING_GENERATED, RING_MUL_LID, RING_MUL_LNEG,
        RING_MUL_LZERO, RING_NEG, RING_NEG_EQ_0, RING_SUB, RING_SUB_EQ_0,
        RING_SUB_RDISTRIB, RING_SUM, RING_SUM_CASES, RING_SUM_CLAUSES, RING_SUM_EQ,
        RING_SUM_EQ_0, RING_SUM_IMAGE, RING_SUM_LMUL, RING_SUM_SING, RING_SUM_SUB, .. } := D.core7
  let { SUBRING_GENERATED_INC_GEN, SUBSET, SUBSET_TRANS, SWAP_EXISTS_THM, .. } := D.core8
  let { o_DEF, o_THM, ring_homomorphism, .. } := D.core9
  let { SUBFIELD_OF_IMP_SUBSET, .. } := BSubfields
  let { SUBRING_SUBSET_SUBFIELD_GENERATED, .. } := BSubfieldGenerated
  let { RING_SPAN_FINITARY, RING_SPAN_FINITE, RING_SPAN_SUBSET, ring_span_INDUCT, .. } := BRingSpan
  let { RING_MATROID, .. } := BRingMatroid
  let { RING_DEPENDENT_IMP_SUBSET, RING_DEPENDENT_MONO, RING_MATROID_INDEPENDENT,
        RING_MATROID_SPANNING, ring_dependent, ring_independent, .. } := BLinearAlgebra
  -- @@SCOPE END

  let RING_DEPENDENT_FINITARY ← prove
   r"!(h:A->B) k l s.
        ring_dependent (k,l) h s <=>
        s SUBSET ring_carrier l /\
        ?t. FINITE t /\ t SUBSET s /\ ring_dependent (k,l) h t"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [ONCE_REWRITE_TAC [ring_dependent],
      MESON_TAC [RING_DEPENDENT_MONO, RING_DEPENDENT_IMP_SUBSET]] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN (← q "a:B") STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP RING_SPAN_FINITARY) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"t:B->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"(a:B) INSERT t") THEN
    ASM_REWRITE_TAC [FINITE_INSERT, EXISTS_IN_INSERT] THEN
    SUBGOAL_THEN (← q r"(a INSERT t) DELETE (a:B) = t") SUBST1_TAC THEN
    ASM SET_TAC [])

  let RING_INDEPENDENT_FINITARY ← prove
   r"!(h:A->B) k l s.
        ring_independent (k,l) h s <=>
        s SUBSET ring_carrier l /\
        !t. FINITE t /\ t SUBSET s ==> ring_independent (k,l) h t"
   (REPEAT GEN_TAC THEN REWRITE_TAC [ring_independent] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RING_DEPENDENT_FINITARY] THEN
    SET_TAC [])

  let RING_INDEPENDENT_LE_SPAN ← prove
   r"!(h:A->B) k l s t.
        field k /\ ring_homomorphism(k,l) h /\ t SUBSET ring_carrier l /\
        FINITE t /\
        ring_independent (k,l) h s /\ s SUBSET ring_span (k,l) h t
        ==> FINITE s /\ CARD s <= CARD t"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE THEN
    EXISTS_TAC (← q r"ring_matroid (k,l) (h:A->B)") THEN
    ASM_SIMP_TAC [RING_MATROID, RING_MATROID_INDEPENDENT])

  let RING_DEPENDENT_FINITE ← prove
   r"!(h:A->B) k l s.
        field k /\ ring_homomorphism(k,l) h /\ FINITE s
        ==> (ring_dependent (k,l) h s <=>
             s SUBSET ring_carrier l /\
             ?c. ring_sum l s (\x. ring_mul l (h(c x)) x) = ring_0 l /\
                 (!x. x IN s ==> c x IN ring_carrier k) /\
                 ?x. x IN s /\ ~(c x = ring_0 k))"
   (← do
    let r4 ← D.RING_RULE (← q r"
       ring_add r (ring_neg r x) b = ring_mul r y (ring_0 r) <=>
        b = x")
    let r3 ← D.RING_RULE (← q r"
       ring_mul l y y' = ring_neg l (ring_1 l)
        ==> ring_mul l y (ring_mul l y' a) = ring_neg l a")
    let s2 ← SET_RULE (← q r"a IN s ==> {x | x IN s /\ x = a} = {a}")
    let s1 ← SET_RULE (← q r"s SUBSET t ==> s DELETE a SUBSET t")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [ring_dependent] THEN
    ASM_CASES_TAC (← q r"(s:B->bool) SUBSET ring_carrier l") THEN
    ASM_SIMP_TAC [RING_SPAN_FINITE, FINITE_DELETE, s1] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [SUBSET]) THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [SUBSET, FORALL_IN_IMAGE] o
        GEN_REWRITE_RULE I [ring_homomorphism]) THEN
    X_GEN_TAC (← q "a:B") THEN ASM_CASES_TAC (← q r"(a:B) IN s") THEN
    ASM_REWRITE_TAC [IN_ELIM_THM] THEN EQ_TAC THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"c:B->A") THENL
     [DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THEN
      EXISTS_TAC (← q r"\x. if x = a then ring_neg k (ring_1 k) else (c:B->A) x") THEN
      ASM_SIMP_TAC [RING_SUM_CASES, COND_RAND, COND_RATOR] THEN
      ASM_SIMP_TAC [← GSYM DELETE, RING_SUM_SING, RING_NEG, RING_1, RING_MUL,
        s2] THEN
      ASM_SIMP_TAC [IN_SUBRING_1, IN_SUBRING_NEG, IN_DELETE, COND_ID] THEN
      ASM_SIMP_TAC [RING_NEG_EQ_0, RING_1, FIELD_NONTRIVIAL] THEN
      D.RING_TAC THEN ASM_SIMP_TAC [RING_SUM, RING_0, RING_1],
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
      ABBREV_TAC (← q r"y = (h:A->B) (ring_neg k (ring_inv k ((c:B->A) a)))") THEN
      SUBGOAL_THEN (← q r"(y:B) IN ring_carrier l") ASSUME_TAC THENL
       [ASM_MESON_TAC [RING_NEG, RING_INV], ALL_TAC] THEN
      DISCH_THEN (MP_TAC o AP_TERM (← q r"ring_mul l (y:B)")) THEN
      W (MP_TAC o PART_MATCH (lhand o rand) (← GSYM RING_SUM_LMUL) o
        lhand o lhand o snd) THEN
      ASM_SIMP_TAC [RING_MUL, RING_MUL_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN (← q r"s:B->bool = a INSERT (s DELETE a)") MP_TAC THENL
       [ASM SET_TAC [], ALL_TAC] THEN
      DISCH_THEN (fun th => GEN_REWRITE_TAC (funpow 3 LAND_CONV) [th]) THEN
      ASM_SIMP_TAC [RING_SUM_CLAUSES, FINITE_DELETE, RING_MUL, IN_DELETE] THEN
      COND_CASES_TAC THENL [ASM_MESON_TAC [RING_MUL], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"ring_mul l y (ring_mul l (h((c:B->A) a)) a) = ring_neg l a")
      SUBST1_TAC THENL
       [MATCH_MP_TAC (← REWRITE_RULE [IMP_IMP] r3) THEN
        ASM_SIMP_TAC [] THEN EXPAND_TAC "y" THEN
        MP_TAC (← ISPECL [← q "k:A ring", ← q r"(c:B->A) a"] FIELD_MUL_LINV) THEN
        ANTS_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN
        DISCH_THEN (MP_TAC o AP_TERM (← q r"(h:A->B) o ring_neg k")) THEN
        ASM_SIMP_TAC [o_THM, RING_1] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
        ASM_SIMP_TAC [← GSYM RING_MUL_LNEG, RING_INV] THEN EXPAND_TAC "y" THEN
        ASM_MESON_TAC [RING_INV, RING_NEG],
        ASM_SIMP_TAC [RING_SUM, r4] THEN
        DISCH_TAC] THEN
      EXISTS_TAC
       (← q r"\x. ring_mul k (ring_neg k (ring_inv k (c a))) ((c:B->A) x)") THEN
      CONJ_TAC THENL [ASM_MESON_TAC [RING_MUL, RING_NEG, RING_INV], ALL_TAC] THEN
      FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [← SYM th])) THEN
      MATCH_MP_TAC RING_SUM_EQ THEN
      ASM_SIMP_TAC [RING_MUL, RING_NEG, RING_INV, IN_DELETE, RING_MUL_ASSOC] THEN
      ASM_MESON_TAC [RING_MUL, RING_NEG, RING_INV]]))

  let RING_INDEPENDENT_FINITE ← prove
   r"!(h:A->B) k l s.
        field k /\ ring_homomorphism(k,l) h /\ FINITE s
        ==> (ring_independent (k,l) h s <=>
             s SUBSET ring_carrier l /\
             !c. ring_sum l s (\x. ring_mul l (h(c x)) x) = ring_0 l /\
                 (!x. x IN s ==> c x IN ring_carrier k)
                 ==> (!x. x IN s ==> c x = ring_0 k))"
   (SIMP_TAC [ring_independent, RING_DEPENDENT_FINITE] THEN MESON_TAC [])

  let RING_INDEPENDENT_FINITE_EQ ← prove
   r"!(h:A->B) k l s.
        field k /\ ring_homomorphism(k,l) h /\ FINITE s
        ==> (ring_independent (k,l) h s <=>
             s SUBSET ring_carrier l /\
             !c d. ring_sum l s (\x. ring_mul l (h(c x)) x) =
                   ring_sum l s (\x. ring_mul l (h(d x)) x) /\
                  (!x. x IN s
                       ==> c x IN ring_carrier k /\ d x IN ring_carrier k)
                 ==> (!x. x IN s ==> c x = d x))"
   (← do
    let m2 ← MESON [RING_SUB_EQ_0, RING_SUM]
      (← q r"ring_sum r s x = ring_sum r s y
      ==> ring_sub r (ring_sum r s y) (ring_sum r s x) = ring_0 r")
    pure (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [RING_INDEPENDENT_FINITE] THEN
    ASM_CASES_TAC (← q r"(s:B->bool) SUBSET ring_carrier l") THEN ASM_REWRITE_TAC [] THEN
    EQ_TAC THENL
     [DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [← q r"c:B->A", ← q r"d:B->A"] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"\x. ring_sub k ((d:B->A) x) (c x)")) THEN
      ANTS_TAC THENL [ALL_TAC, ASM_MESON_TAC [RING_SUB_EQ_0, SUBSET]] THEN
      ASM_SIMP_TAC [RING_SUB] THEN FIRST_ASSUM (MP_TAC o MATCH_MP m2) THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      W (MP_TAC o PART_MATCH (rand o rand) RING_SUM_SUB o rand o snd) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [ASM_MESON_TAC [ring_homomorphism, RING_MUL, SUBSET, IN_IMAGE],
        DISCH_THEN (SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC RING_SUM_EQ THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_SUB) THEN
      RULE_ASSUM_TAC (REWRITE_RULE
       [ring_homomorphism, SUBSET, FORALL_IN_IMAGE]) THEN
      ASM_SIMP_TAC [RING_SUB_RDISTRIB],
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"c:B->A") THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"(\x. ring_0 k):B->A")) THEN
      DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC [RING_0] THEN DISCH_THEN MATCH_MP_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN
      RULE_ASSUM_TAC (REWRITE_RULE
       [ring_homomorphism, SUBSET, FORALL_IN_IMAGE]) THEN
      ASM_SIMP_TAC [RING_MUL, RING_MUL_LZERO]]))

  let RING_DEPENDENT_SPAN_IMAGE ← prove
   r"!(h:A->B) k l (f:K->B) s t.
        field k /\ ring_homomorphism(k,l) h /\ t SUBSET ring_carrier l /\
        FINITE s /\ FINITE t /\ IMAGE f s SUBSET ring_span (k,l) h t /\
        CARD t < CARD s
        ==> ?c. ring_sum l s (\x. ring_mul l (h(c x)) (f x)) = ring_0 l /\
                (!x. x IN s ==> c x IN ring_carrier k) /\
                ?x. x IN s /\ ~(c x = ring_0 k)"
   (← do
    let s4 ← SET_RULE (← q r"a IN s ==> {x | x IN s /\ x = a} = {a}")
    let t3 ← TAUT (← q r"~(p /\ q) <=> p ==> (p /\ ~q)")
    pure (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"!i j. i IN s /\ j IN s ==> ((f:K->B) i = f j <=> i = j)") THENL
     [MP_TAC (← ISPECL [← q r"h:A->B", ← q "k:A ring", ← q "l:B ring",
                     ← q r"IMAGE (f:K->B) s", ← q r"t:B->bool"]
          RING_INDEPENDENT_LE_SPAN) THEN
      ASM_SIMP_TAC [ring_independent, CARD_IMAGE_INJ, FINITE_IMAGE] THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM CONTRAPOS_THM] THEN SIMP_TAC [NOT_LE] THEN
      ANTS_TAC THENL [ASM_MESON_TAC [CARD_IMAGE_INJ], ALL_TAC] THEN
      REWRITE_TAC [t3] THEN ANTS_TAC THENL
       [ASM SET_TAC [RING_SPAN_SUBSET],
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)] THEN
      W (MP_TAC o PART_MATCH (lhand o rand) RING_DEPENDENT_FINITE o
          lhand o snd) THEN
      ASM_SIMP_TAC [FINITE_IMAGE] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM, FORALL_IN_IMAGE, EXISTS_IN_IMAGE] THEN
      X_GEN_TAC (← q r"c:B->A") THEN ASM_SIMP_TAC [RING_SUM_IMAGE, IMP_CONJ, o_DEF] THEN
      REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"(c:B->A) o (f:K->B)") THEN
      ASM_SIMP_TAC [o_DEF] THEN ASM_MESON_TAC [],
      FIRST_X_ASSUM (MP_TAC o
        GEN_REWRITE_RULE RAND_CONV [← GSYM INJECTIVE_ON_ALT]) THEN
      REWRITE_TAC [NOT_FORALL_THM, LEFT_IMP_EXISTS_THM, NOT_IMP] THEN
      MAP_EVERY X_GEN_TAC [← q "m:K", ← q "n:K"] THEN STRIP_TAC THEN
      EXISTS_TAC
       (← q r"(\i. if i = m then ring_1 k
             else if i = n then ring_neg k (ring_1 k)
             else ring_0 k):K->A") THEN
      REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
       [REPLICATE_TAC 2
         (ONCE_REWRITE_TAC [COND_RAND] THEN
          ONCE_REWRITE_TAC [COND_RAND] THEN
          ONCE_REWRITE_TAC [COND_RATOR] THEN
          ASM_SIMP_TAC [RING_SUM_CASES, FINITE_RESTRICT]),
        MESON_TAC [RING_0, RING_1, RING_NEG],
        EXISTS_TAC (← q "m:K") THEN ASM_MESON_TAC [FIELD_NONTRIVIAL]] THEN
      SUBGOAL_THEN (← q r"!x. x IN s ==> (f:K->B) x IN ring_carrier l") ASSUME_TAC THENL
       [RULE_ASSUM_TAC (REWRITE_RULE [SUBSET, FORALL_IN_IMAGE]) THEN
        ASM_MESON_TAC [RING_SPAN_SUBSET, SUBFIELD_OF_IMP_SUBSET, SUBSET],
        ALL_TAC] THEN
      ASM_SIMP_TAC [IN_ELIM_THM, RING_SUM_SING, RING_MUL, RING_1, RING_NEG,
                   s4] THEN
      RULE_ASSUM_TAC (REWRITE_RULE
       [ring_homomorphism, SUBSET, FORALL_IN_IMAGE]) THEN
      ASM_SIMP_TAC [RING_SUM, RING_1, RING_MUL, RING_NEG,
                   RING_MUL_LNEG, RING_MUL_LID, RING_ADD_ASSOC, RING_SUM,
                   RING_ADD_RNEG, RING_ADD_LZERO] THEN
      MATCH_MP_TAC RING_SUM_EQ_0 THEN
      ASM_SIMP_TAC [IN_ELIM_THM, RING_MUL_LZERO]]))

  let RING_SPAN_SUBSET_SUBRING_GENERATED ← prove
   r"!(h:A->B) k l s.
        ring_span (k,l) h s SUBSET
        ring_carrier(subring_generated l (IMAGE h (ring_carrier k) UNION s))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [SUBSET] THEN
    MATCH_MP_TAC ring_span_INDUCT THEN
    SIMP_TAC [RING_0_IN_SUBRING_GENERATED, RING_ADD_IN_SUBRING_GENERATED] THEN
    REPEAT STRIP_TAC THENL
      [ALL_TAC, MATCH_MP_TAC RING_MUL_IN_SUBRING_GENERATED THEN CONJ_TAC] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ring_homomorphism]) THEN ASM SET_TAC [])

  let RING_SPAN_SUBSET_SUBFIELD_GENERATED ← prove
   r"!(h:A->B) k l s.
        ring_span (k,l) h s SUBSET
        ring_carrier(subfield_generated l (IMAGE h (ring_carrier k) UNION s))"
   (MESON_TAC [RING_SPAN_SUBSET_SUBRING_GENERATED, SUBSET_TRANS,
              SUBRING_SUBSET_SUBFIELD_GENERATED])

  let RING_INDEPENDENT_INSERT ← prove
   r"!(h:A->B) k l s a.
         field k /\
         ring_homomorphism (k,l) h /\
         s SUBSET ring_carrier l /\
         a IN ring_carrier l
        ==> (ring_independent (k,l) h (a INSERT s) <=>
             if a IN s then ring_independent (k,l) h s
             else ring_independent (k,l) h s /\ ~(a IN ring_span (k,l) h s))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"ring_matroid (k,l) (h:A->B)", ← q r"s:B->bool", ← q "a:B"]
          MATROID_INDEPENDENT_INSERT) THEN
    ASM_SIMP_TAC [RING_MATROID, INSERT_SUBSET, RING_MATROID_INDEPENDENT])

  let RING_INDEPENDENT_CARD_LE_SPANNING ← prove
   r"!(h:A->B) k l b c.
        field k /\ ring_homomorphism (k,l) h /\
        ring_independent (k,l) h b /\ ring_spanning (k,l) h c
        ==> b <=_c c"
   (REWRITE_TAC [IMP_CONJ] THEN
    SIMP_TAC [← GSYM RING_MATROID_INDEPENDENT, ← GSYM RING_MATROID_SPANNING] THEN
    MESON_TAC [MATROID_INDEPENDENT_CARD_LE_SPANNING])

  -- @@RETURN BEGIN
  return { RING_DEPENDENT_FINITARY, RING_INDEPENDENT_FINITARY, RING_INDEPENDENT_LE_SPAN,
           RING_DEPENDENT_FINITE, RING_INDEPENDENT_FINITE, RING_INDEPENDENT_FINITE_EQ,
           RING_DEPENDENT_SPAN_IMAGE, RING_SPAN_SUBSET_SUBRING_GENERATED,
           RING_SPAN_SUBSET_SUBFIELD_GENERATED, RING_INDEPENDENT_INSERT,
           RING_INDEPENDENT_CARD_LE_SPANNING }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- The general (finite or infinite) tower law for degree of field extensions -/
/- (fieldtheory.ml 2118-2381)                                                -/
/- ------------------------------------------------------------------------- -/

structure TowerLaw where
  -- @@FIELDS
  RING_SPANNING_TRANS : thm
  RING_INDEPENDENT_PRODUCTS : thm
  RING_INDEPENDENT_TRANS : thm
  RING_BASIS_TRANS : thm
  FIELD_EXTENSION_TOWER_LAW : thm
  deriving Inhabited

@[nospecialize]
def setupTowerLaw [HolBase] (D : FieldTheoryDeps) (BFieldExtension : FieldExtension) (BRingSpan : RingSpan) (BLinearAlgebra : LinearAlgebra) (BFinitary : Finitary) :
    ExceptT String IO TowerLaw := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, SET_RULE, SET_TAC, TAUT, .. } := D
  let { AND_FORALL_THM, CARD_EQ_IMAGE, CARD_EQ_REFL_IMP, CARD_EQ_SYM, CARD_EQ_TRANS,
        CONJ_ASSOC, CROSS, EXISTS_PAIR_THM, FIELD_HOMOMORPHISM_DIV, .. } := D.core1
  let { FIELD_IMP_INTEGRAL_DOMAIN, FINITE_IMAGE, FINITE_PRODUCT_DEPENDENT,
        FORALL_FINITE_SUBSET_IMAGE, FORALL_IN_CROSS, FORALL_IN_GSPEC, FORALL_IN_IMAGE,
        FORALL_PAIR_THM, IMAGE_SUBSET, .. } := D.core2
  let { IMP_CONJ, IMP_CONJ_ALT, IMP_IMP, INTEGRAL_DOMAIN_MUL_LCANCEL,
        INTEGRAL_DOMAIN_MUL_RCANCEL, IN_CROSS, IN_ELIM_THM, IN_IMAGE, LAMBDA_PAIR_THM,
        LEFT_IMP_EXISTS_THM, .. } := D.core3
  let { MONO_FORALL, PAIR_EQ, .. } := D.core4
  let { RIGHT_FORALL_IMP_THM, RIGHT_IMP_FORALL_THM, .. } := D.core5
  let { RING_DIV, RING_HOMOMORPHISM_COMPOSE, RING_HOMOMORPHISM_MUL,
        RING_HOMOMORPHISM_SUM, RING_MONOMORPHISM_ALT, RING_MUL, .. } := D.core6
  let { RING_MUL_ASSOC, RING_SUM, RING_SUM_EQ, RING_SUM_IMAGE, RING_SUM_RMUL,
        RING_SUM_SUM_PRODUCT, .. } := D.core7
  let { SUBSET, SUBSET_ANTISYM_EQ, SUBSET_TRANS, SWAP_FORALL_THM, mul_c, .. } := D.core8
  let { o_DEF, o_THM, ring_homomorphism, ring_monomorphism, .. } := D.core9
  let { FIELD_EXTENSION_CARRIER, FIELD_EXTENSION_IMP_HOMOMORPHISM,
        FIELD_EXTENSION_IMP_SUBSET, field_extension, .. } := BFieldExtension
  let { RING_SPAN_FINITARY, RING_SPAN_FINITE, RING_SPAN_INC, RING_SPAN_MONO,
        RING_SPAN_MUL, RING_SPAN_SING, RING_SPAN_SUM, .. } := BRingSpan
  let { RING_BASES_CARD_EQ, RING_INDEPENDENT_MONO, RING_INDEPENDENT_NONZERO,
        RING_SPANNING_ALT, ring_basis, ring_dependent, ring_independent, .. } := BLinearAlgebra
  let { RING_INDEPENDENT_FINITARY, RING_INDEPENDENT_FINITE, .. } := BFinitary
  -- @@SCOPE END

  let RING_SPANNING_TRANS ← prove
   r"!(f:A->B) (g:B->C) k l m b c.
      field_extension (k,l) f /\ ring_spanning (k,l) f b /\
      field_extension (l,m) g /\ ring_spanning (l,m) g c
      ==> ring_spanning (k,m) (g o f) {ring_mul m (g x) y | x IN b /\ y IN c}"
   (REWRITE_TAC [RING_SPANNING_ALT] THEN REPEAT STRIP_TAC THENL
     [REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN
      ASM_MESON_TAC [FIELD_EXTENSION_CARRIER, RING_MUL, SUBSET],
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
       (← REWRITE_RULE [IMP_CONJ] SUBSET_TRANS))] THEN
    REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q "w:C") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP RING_SPAN_FINITARY) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM, IMP_CONJ] THEN
    X_GEN_TAC (← q r"c':C->bool") THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"(c':C->bool) SUBSET ring_carrier m") ASSUME_TAC
    THENL [ASM SET_TAC [], ALL_TAC] THEN
    ASM_SIMP_TAC [RING_SPAN_FINITE, FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
    SPEC_TAC (← q "w:C", ← q "w:C") THEN
    REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN
    X_GEN_TAC (← q r"d:C->B") THEN DISCH_TAC THEN MATCH_MP_TAC RING_SPAN_SUM THEN
    X_GEN_TAC (← q "z:C") THEN DISCH_TAC THEN REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"(d:C->B) z IN ring_span (k,l) (f:A->B) b") MP_TAC THENL
     [ASM SET_TAC [], DISCH_THEN (MP_TAC o MATCH_MP RING_SPAN_FINITARY)] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM, IMP_CONJ] THEN
    X_GEN_TAC (← q r"b':B->bool") THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"(b':B->bool) SUBSET ring_carrier l") ASSUME_TAC
    THENL [ASM SET_TAC [], ALL_TAC] THEN
    ASM_SIMP_TAC [RING_SPAN_FINITE, FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
    SPEC_TAC (← q r"(d:C->B) z", ← q "y:B") THEN REWRITE_TAC [FORALL_IN_GSPEC] THEN
    X_GEN_TAC (← q r"e:B->A") THEN DISCH_TAC THEN
    MP_TAC (← GEN (← q r"i:B->B")
     (← ISPECL [← q "l:B ring", ← q "m:C ring", ← q r"g:B->C", ← q r"i:B->B", ← q r"b':B->bool"]
        (← REWRITE_RULE [RIGHT_IMP_FORALL_THM] RING_HOMOMORPHISM_SUM))) THEN
    ASM_SIMP_TAC [FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN DISCH_THEN (fun th =>
      W (MP_TAC o PART_MATCH (lhand o rand) th o lhand o lhand o snd)) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [FIELD_EXTENSION_CARRIER, SUBSET, RING_MUL],
      DISCH_THEN SUBST1_TAC] THEN
    W (MP_TAC o PART_MATCH (rand o rand) RING_SUM_RMUL o lhand o snd) THEN
    REWRITE_TAC [o_DEF] THEN ANTS_TAC THENL
     [ASM_MESON_TAC [FIELD_EXTENSION_CARRIER, SUBSET, RING_MUL],
      DISCH_THEN (SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SPAN_SUM THEN X_GEN_TAC (← q "y:B") THEN DISCH_TAC THEN
    REWRITE_TAC [] THEN
    MP_TAC (← ISPECL [← q "l:B ring", ← q "m:C ring", ← q r"g:B->C"] RING_HOMOMORPHISM_MUL) THEN
    ASM_SIMP_TAC [FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN DISCH_THEN (fun th =>
      W (MP_TAC o PART_MATCH (lhand o rand) th o lhand o lhand o snd)) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [FIELD_EXTENSION_CARRIER, SUBSET, RING_MUL],
      DISCH_THEN SUBST1_TAC] THEN
    W (MP_TAC o PART_MATCH (rand o rand) RING_MUL_ASSOC o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [FIELD_EXTENSION_CARRIER, SUBSET, RING_MUL],
      DISCH_THEN (SUBST1_TAC o SYM)] THEN
    MP_TAC (← ISPECL [← q r"(g:B->C) o (f:A->B)", ← q "k:A ring", ← q "m:C ring"]
          RING_SPAN_MUL) THEN
    REWRITE_TAC [o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT (FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET)) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [SUBSET, FORALL_IN_IMAGE]) THEN
    REPEAT (CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC]) THEN
    MATCH_MP_TAC RING_SPAN_INC THEN ASM_SIMP_TAC [RING_MUL] THEN ASM SET_TAC [])

  let (RING_INDEPENDENT_PRODUCTS, RING_INDEPENDENT_TRANS) ← (do
    -- the `let lemma = prove ... in` runs first; then the main tactic's rules
    -- in OCaml's reverse-text order (MESON, then the second TAUT, SET_RULE,
    -- the first TAUT).
    let lemma ← prove
     r"{ring_mul m ((g:B->C) x) y | x IN b' /\ y IN c'} =
       IMAGE (\(y,x). ring_mul m (g x) y) (c' CROSS b')"
     (REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, FORALL_IN_IMAGE, FORALL_IN_CROSS,
                  FORALL_IN_GSPEC, SUBSET] THEN
      REWRITE_TAC [IN_IMAGE, IN_ELIM_THM, EXISTS_PAIR_THM, IN_CROSS] THEN
      SET_TAC [])
    let m4 ← MESON []
     (← q r"P /\ x' = x /\ (Q ==> R) ==> (x = z /\ P ==> Q) ==> (x' = z ==> R)")
    let t3 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    let s2 ← SET_RULE (← q r"!s. s SUBSET t /\ x IN s ==> x IN t")
    let t1 ← TAUT
     (← q r"(p ==> q) /\ (p ==> r) <=> p ==> q /\ (q ==> r)")
    CONJ_PAIR (← prove
     r"(!(f:A->B) (g:B->C) k l m b c.
      field_extension (k,l) f /\ ring_independent (k,l) f b /\
      field_extension (l,m) g /\ ring_independent (l,m) g c
      ==> !x y x' y'. x IN b /\ y IN c /\ x' IN b /\ y' IN c
                      ==> (ring_mul m (g x) y = ring_mul m (g x') y' <=>
                           x = x' /\ y = y')) /\
   (!(f:A->B) (g:B->C) k l m b c.
      field_extension (k,l) f /\ ring_independent (k,l) f b /\
      field_extension (l,m) g /\ ring_independent (l,m) g c
      ==> ring_independent (k,m) (g o f)
           {ring_mul m (g x) y | x IN b /\ y IN c})"
     (REWRITE_TAC [AND_FORALL_THM, t1] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"(!w:B. w IN b ==> w IN ring_carrier l) /\
        (!z:C. z IN c ==> z IN ring_carrier m) /\
        (!u. u IN ring_carrier k ==> (f:A->B) u IN ring_carrier l) /\
        (!v. v IN ring_carrier l ==> (g:B->C) v IN ring_carrier m)")
      STRIP_ASSUME_TAC THENL
       [RULE_ASSUM_TAC (REWRITE_RULE
         [ring_independent, field_extension,
          ring_monomorphism, ring_homomorphism]) THEN
        ASM SET_TAC [],
        ALL_TAC] THEN
      CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC [] THEN
        ASM_CASES_TAC (← q r"x:B = x'") THEN ASM_REWRITE_TAC [] THENL
         [MATCH_MP_TAC (← ONCE_REWRITE_RULE [IMP_CONJ] (← REWRITE_RULE [CONJ_ASSOC]
            INTEGRAL_DOMAIN_MUL_LCANCEL)) THEN
          RULE_ASSUM_TAC (REWRITE_RULE [field_extension, RING_MONOMORPHISM_ALT]) THEN
          ASM_MESON_TAC [RING_INDEPENDENT_NONZERO, FIELD_IMP_INTEGRAL_DOMAIN],
          ALL_TAC] THEN
        ASM_CASES_TAC (← q r"y:C = y'") THEN ASM_REWRITE_TAC [] THENL
         [W (MP_TAC o PART_MATCH (rand o rand o rand o rand o rand o lhand)
            INTEGRAL_DOMAIN_MUL_RCANCEL o rand o snd) THEN
          RULE_ASSUM_TAC (REWRITE_RULE [field_extension, ring_monomorphism]) THEN
          ASM_MESON_TAC [RING_INDEPENDENT_NONZERO, FIELD_IMP_INTEGRAL_DOMAIN],
          DISCH_TAC] THEN
        UNDISCH_TAC (← q r"ring_independent (l,m) (g:B->C) c") THEN
        REWRITE_TAC [ring_independent, ring_dependent] THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC [] THEN
        EXISTS_TAC (← q "y:C") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC s2 THEN
        EXISTS_TAC (← q r"ring_span (l,m) (g:B->C) {y'}") THEN CONJ_TAC THENL
         [MATCH_MP_TAC RING_SPAN_MONO THEN ASM SET_TAC [],
          ASM_SIMP_TAC [RING_SPAN_SING, FIELD_EXTENSION_IMP_HOMOMORPHISM]] THEN
        REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC (← q r"ring_div l x' x:B") THEN
        ASM_SIMP_TAC [RING_DIV] THEN
        MP_TAC (← ISPECL [← q "l:B ring", ← q "m:C ring", ← q r"g:B->C"]
            FIELD_HOMOMORPHISM_DIV) THEN
        ANTS_TAC THENL
         [ASM_MESON_TAC [field_extension, ring_monomorphism],
          ASM_SIMP_TAC [] THEN DISCH_THEN (K ALL_TAC)] THEN
        UNDISCH_TAC (← q r"ring_mul m ((g:B->C) x) y = ring_mul m (g x') y'") THEN
        SUBGOAL_THEN
         (← q r"field m /\
          y IN ring_carrier m /\ y' IN ring_carrier m /\
          (g:B->C) x IN ring_carrier m /\ (g:B->C) x' IN ring_carrier m /\
          ~(g x = ring_0 m)")
        MP_TAC THENL
         [ASM_MESON_TAC [field_extension, RING_MONOMORPHISM_ALT,
                        RING_INDEPENDENT_NONZERO],
          POP_ASSUM_LIST (K ALL_TAC) THEN D.FIELD_TAC],
        DISCH_TAC] THEN
      SUBGOAL_THEN
       (← q r"!b' c'. FINITE b' /\ FINITE c' /\ b' SUBSET b /\ c' SUBSET c
                ==> ring_independent (k,m) ((g:B->C) o (f:A->B))
                      {ring_mul m (g x) y | x IN b' /\ y IN c'}")
      MP_TAC THENL
       [REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN
        W (MP_TAC o PART_MATCH (lhand o rand) RING_INDEPENDENT_FINITE o snd) THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC [FINITE_PRODUCT_DEPENDENT] THEN
          ASM_MESON_TAC [field_extension, ring_monomorphism,
                        RING_HOMOMORPHISM_COMPOSE],
          DISCH_THEN SUBST1_TAC] THEN
        MATCH_MP_TAC t3 THEN CONJ_TAC THENL
         [REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN ASM_MESON_TAC [RING_MUL],
          DISCH_TAC] THEN
        REWRITE_TAC [FORALL_IN_GSPEC] THEN
        X_GEN_TAC (← q r"c:C->A") THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
        REWRITE_TAC [lemma] THEN
        W (MP_TAC o PART_MATCH (lhand o rand) RING_SUM_IMAGE o
           lhand o lhand o snd) THEN
        REWRITE_TAC [FORALL_PAIR_THM, IN_CROSS] THEN
        ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN
        REWRITE_TAC [o_DEF] THEN ONCE_REWRITE_TAC [LAMBDA_PAIR_THM] THEN
        REWRITE_TAC [] THEN REWRITE_TAC [CROSS] THEN
        W (MP_TAC o PART_MATCH (rand o rand) RING_SUM_SUM_PRODUCT o
            lhand o lhand o snd) THEN
        ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
         [ASM_MESON_TAC [RING_MUL], DISCH_THEN (SUBST1_TAC o SYM)] THEN
        SUBGOAL_THEN (← q r"ring_independent(l,m) (g:B->C) c'") MP_TAC THENL
         [ASM_MESON_TAC [RING_INDEPENDENT_MONO, SUBSET], ALL_TAC] THEN
        W (MP_TAC o PART_MATCH (lhand o rand)
          RING_INDEPENDENT_FINITE o lhand o snd) THEN
        ANTS_TAC THENL
         [ASM_MESON_TAC [field_extension, ring_monomorphism],
          DISCH_THEN SUBST1_TAC THEN DISCH_THEN (MP_TAC o CONJUNCT2)] THEN
        DISCH_THEN (MP_TAC o SPEC
         (← q r"\y:C. ring_sum l b'
                  (\x. ring_mul l ((f:A->B)(c(ring_mul m (g x:C) y))) x)")) THEN
        REWRITE_TAC [] THEN MATCH_MP_TAC m4 THEN
        REWRITE_TAC [RING_SUM] THEN CONJ_TAC THENL
         [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q "y:C") THEN
          DISCH_TAC THEN REWRITE_TAC [] THEN
          MP_TAC (← ISPECL [← q "l:B ring", ← q "m:C ring", ← q r"g:B->C",
                    ← q r"\x. ring_mul l ((f:A->B) (c (ring_mul m ((g:B->C) x) y))) x",
                   ← q r"b':B->bool"]
            (← REWRITE_RULE [RIGHT_IMP_FORALL_THM] RING_HOMOMORPHISM_SUM)) THEN
          ASM_SIMP_TAC [FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
          ASM_SIMP_TAC [RING_MUL] THEN DISCH_THEN SUBST1_TAC THEN
          W (MP_TAC o PART_MATCH (rand o rand) RING_SUM_RMUL o rand o snd) THEN
          ASM_SIMP_TAC [o_THM] THEN ANTS_TAC THENL
           [ASM_MESON_TAC [RING_MUL], DISCH_THEN (SUBST1_TAC o SYM)] THEN
          MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q "x:B") THEN DISCH_TAC THEN
          REWRITE_TAC [] THEN
          W (MP_TAC o PART_MATCH (lhand o rand) RING_MUL_ASSOC o lhand o snd) THEN
          ANTS_TAC THENL [ASM_MESON_TAC [RING_MUL], DISCH_THEN SUBST1_TAC] THEN
          AP_THM_TAC THEN AP_TERM_TAC THEN
          ASM_MESON_TAC [FIELD_EXTENSION_IMP_HOMOMORPHISM, RING_HOMOMORPHISM_MUL],
          GEN_REWRITE_TAC RAND_CONV [SWAP_FORALL_THM] THEN
          MATCH_MP_TAC MONO_FORALL] THEN
        X_GEN_TAC (← q "y:C") THEN ASM_CASES_TAC (← q r"(y:C) IN c'") THEN
        ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN (← q r"ring_independent(k,l) (f:A->B) b'") MP_TAC THENL
         [ASM_MESON_TAC [RING_INDEPENDENT_MONO, SUBSET], ALL_TAC] THEN
        W (MP_TAC o PART_MATCH (lhand o rand)
          RING_INDEPENDENT_FINITE o lhand o snd) THEN
        ANTS_TAC THENL
         [ASM_MESON_TAC [field_extension, ring_monomorphism],
          DISCH_THEN SUBST1_TAC THEN DISCH_THEN (MP_TAC o CONJUNCT2)] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"\x. c(ring_mul m ((g:B->C) x) y):A")) THEN
        ASM_SIMP_TAC [RING_MUL],
        DISCH_TAC THEN
        ONCE_REWRITE_TAC [RING_INDEPENDENT_FINITARY] THEN CONJ_TAC THENL
         [ASM_SIMP_TAC [SUBSET, FORALL_IN_GSPEC, RING_MUL], ALL_TAC] THEN
        REWRITE_TAC [lemma, FORALL_FINITE_SUBSET_IMAGE] THEN
        X_GEN_TAC (← q r"t:C#B->bool") THEN STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPECL
         [← q r"IMAGE SND (t:C#B->bool)", ← q r"IMAGE FST (t:C#B->bool)"]) THEN
        ASM_SIMP_TAC [FINITE_IMAGE] THEN ANTS_TAC THENL
         [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
          SIMP_TAC [FORALL_PAIR_THM, SUBSET, FORALL_IN_IMAGE, IN_CROSS] THEN
          MESON_TAC [],
          MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] RING_INDEPENDENT_MONO)] THEN
        REWRITE_TAC [lemma] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC [SUBSET, FORALL_PAIR_THM, IN_CROSS,
                    IN_IMAGE, EXISTS_PAIR_THM] THEN
        MESON_TAC []])))

  let RING_BASIS_TRANS ← prove
   r"!(f:A->B) (g:B->C) k l m b c.
      field_extension (k,l) f /\ ring_basis (k,l) f b /\
      field_extension (l,m) g /\ ring_basis (l,m) g c
      ==> ring_basis (k,m) (g o f) {ring_mul m (g x) y | x IN b /\ y IN c}"
   (REWRITE_TAC [ring_basis] THEN
    MESON_TAC [RING_INDEPENDENT_TRANS, RING_SPANNING_TRANS])

  let FIELD_EXTENSION_TOWER_LAW ← prove
   r"!(f:A->B) (g:B->C) k l m b c d.
     field_extension (k,l) f /\ field_extension (l,m) g /\
     ring_basis (k,l) f b /\ ring_basis (l,m) g c /\ ring_basis (k,m) (g o f) d
     ==> b *_c c =_c d"
   (REPEAT STRIP_TAC THEN TRANS_TAC CARD_EQ_TRANS
     (← q r"{ring_mul m ((g:B->C) x) y | x IN b /\ y IN c}") THEN
    CONJ_TAC THENL
     [TRANS_TAC CARD_EQ_TRANS
       (← q r"IMAGE (\(x:B,y:C). ring_mul m (g x) y) (b CROSS c)") THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN REWRITE_TAC [CROSS, mul_c] THEN
        MATCH_MP_TAC CARD_EQ_IMAGE THEN
        REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC] THEN
        REWRITE_TAC [IMP_IMP, RIGHT_IMP_FORALL_THM, PAIR_EQ] THEN
        ASM_MESON_TAC [RING_INDEPENDENT_PRODUCTS, ring_basis],
        MATCH_MP_TAC CARD_EQ_REFL_IMP THEN
        REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, FORALL_IN_IMAGE, FORALL_IN_CROSS,
                  FORALL_IN_GSPEC, SUBSET] THEN
        REWRITE_TAC [IN_IMAGE, IN_ELIM_THM, EXISTS_PAIR_THM, IN_CROSS] THEN
        SET_TAC []],
      MATCH_MP_TAC RING_BASES_CARD_EQ THEN
      MAP_EVERY EXISTS_TAC [← q r"(g:B->C) o (f:A->B)", ← q "k:A ring", ← q "m:C ring"] THEN
      ASM_REWRITE_TAC [] THEN
      REPEAT (CONJ_TAC THENL
       [ASM_MESON_TAC [field_extension, ring_monomorphism,
                      RING_HOMOMORPHISM_COMPOSE],
         ALL_TAC]) THEN
      MATCH_MP_TAC RING_BASIS_TRANS THEN ASM_MESON_TAC []])

  -- @@RETURN BEGIN
  return { RING_SPANNING_TRANS, RING_INDEPENDENT_PRODUCTS, RING_INDEPENDENT_TRANS,
           RING_BASIS_TRANS, FIELD_EXTENSION_TOWER_LAW }
  -- @@RETURN END

/-- lib.ml's `el` on a list of theorems. -/
def elThm (n : Nat) (l : List thm) : ExceptT String IO thm :=
  match l[n]? with
  | some x => pure x
  | none => throw "el"

/- ------------------------------------------------------------------------- -/
/- Finite field extensions, those finite-dimensional as vector spaces.       -/
/- Finitely generated field extensions.  (fieldtheory.ml 2383-2588)          -/
/- ------------------------------------------------------------------------- -/

structure FiniteExtension where
  -- @@FIELDS
  finite_extension : thm
  RING_MATROID_FINITE_DIMENSIONAL : thm
  FINITE_IMP_FIELD_EXTENSION : thm
  FINITE_EXTENSION_RING_MATROID : thm
  FINITE_EXTENSION : thm
  FINITE_EXTENSION_SPANNING : thm
  FINITE_EXTENSION_BASIS : thm
  FINITE_EXTENSION_ANY : thm
  FINITE_EXTENSION_ISOMORPHISM : thm
  FINITE_EXTENSION_TRANS : thm
  FINITE_EXTENSION_TRANS_EQ : thm
  finitely_generated_extension : thm
  FINITELY_GENERATED_IMP_FIELD_EXTENSION : thm
  FINITE_IMP_FINITELY_GENERATED_EXTENSION : thm
  FINITELY_GENERATED_EXTENSION : thm
  FINITELY_GENERATED_EXTENSION_TRANS : thm
  deriving Inhabited

@[nospecialize]
def setupFiniteExtension [HolBase] (D : FieldTheoryDeps) (BSubfieldGenerated : SubfieldGenerated) (BSubfieldGenerated1 : SubfieldGenerated1) (BSubfieldGenerated2 : SubfieldGenerated2) (BFieldExtension : FieldExtension) (BRingSpan : RingSpan) (BRingMatroid : RingMatroid) (BLinearAlgebra : LinearAlgebra) (BFinitary : Finitary) (BTowerLaw : TowerLaw) :
    ExceptT String IO FiniteExtension := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, TAUT, new_definition, .. } := D
  let { CARD_FINITE_CONG, CARD_MUL_FINITE, CARD_MUL_FINITE_EQ, .. } := D.core1
  let { FINITE_IMAGE, FINITE_SING, FINITE_SUBSET, FINITE_UNION, FORALL_IN_GSPEC,
        FORALL_IN_IMAGE, FORALL_IN_UNION, IMAGE_UNION, IMAGE_o, .. } := D.core2
  let { IMP_CONJ, IN_ELIM_THM, IN_UNION, LEFT_IMP_EXISTS_THM,
        MATROID_FINITE_DIMENSIONAL_ANY, .. } := D.core3
  let { MONO_EXISTS, .. } := D.core4
  let { RING_1, .. } := D.core5
  let { RING_ISOMORPHISM_IMP_EPIMORPHISM, RING_ISOMORPHISM_IMP_HOMOMORPHISM,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, .. } := D.core6
  let { RING_MUL_RID, SING_SUBSET, .. } := D.core7
  let { SUBSET, SUBSET_ANTISYM_EQ, SUBSET_TRANS, UNION_ASSOC, UNION_SUBSET,
        matroid_finite_dimensional, .. } := D.core8
  let { ring_epimorphism, ring_homomorphism, ring_monomorphism, .. } := D.core9
  let { FIELD_SUBFIELD_GENERATED, RING_CARRIER_SUBFIELD_GENERATED_SUBSET,
        SUBFIELD_GENERATED_EQ, SUBFIELD_GENERATED_MINIMAL, SUBFIELD_GENERATED_MONO,
        SUBFIELD_SUBFIELD_GENERATED, .. } := BSubfieldGenerated
  let { SUBFIELD_GENERATED_INC, .. } := BSubfieldGenerated1
  let { SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE, .. } := BSubfieldGenerated2
  let { FIELD_EXTENSION_CARRIER, FIELD_EXTENSION_IMP_MONOMORPHISM,
        FIELD_EXTENSION_ISOMORPHISM, FIELD_EXTENSION_TRANS, field_extension, .. } := BFieldExtension
  let { RING_SPAN_SING, RING_SPAN_SUBSET, .. } := BRingSpan
  let { RING_MATROID, .. } := BRingMatroid
  let { RING_BASIS_EXISTS, RING_MATROID_BASIS, RING_MATROID_SPANNING,
        RING_SPANNING_CONTAINS_BASIS, RING_SPANNING_IMP_NONEMPTY, ring_basis,
        ring_spanning, .. } := BLinearAlgebra
  let { RING_SPAN_SUBSET_SUBFIELD_GENERATED, .. } := BFinitary
  let { FIELD_EXTENSION_TOWER_LAW, .. } := BTowerLaw
  -- @@SCOPE END

  let finite_extension ← new_definition
   r"finite_extension (k,l) (h:A->B) <=>
          field_extension (k,l) h /\
          ?b. FINITE b /\ b SUBSET ring_carrier l /\
              ring_span (k,l) h b = ring_carrier l"

  let RING_MATROID_FINITE_DIMENSIONAL ← prove
   r"!(h:A->B) k l.
          field_extension (k,l) h
          ==> (matroid_finite_dimensional(ring_matroid (k,l) h) <=>
               finite_extension (k,l) h)"
   (SIMP_TAC [matroid_finite_dimensional, field_extension, finite_extension] THEN
    SIMP_TAC [RING_MATROID, RING_MATROID_SPANNING, ring_monomorphism] THEN
    REWRITE_TAC [ring_spanning])

  let FINITE_IMP_FIELD_EXTENSION ← prove
   r"!(h:A->B) k l. finite_extension(k,l) h ==> field_extension(k,l) h"
   (SIMP_TAC [finite_extension])

  let FINITE_EXTENSION_RING_MATROID ← prove
   r"!(h:A->B) k l.
          finite_extension (k,l) h <=>
          field_extension (k,l) h /\
          matroid_finite_dimensional (ring_matroid (k,l) h)"
   (MESON_TAC [FINITE_IMP_FIELD_EXTENSION, RING_MATROID_FINITE_DIMENSIONAL])

  let FINITE_EXTENSION ← prove
   r"!(h:A->B) k l.
          finite_extension (k,l) h <=>
          field_extension (k,l) h /\
          ?b. FINITE b /\ b SUBSET ring_carrier l /\
              ring_carrier l SUBSET ring_span (k,l) h b"
   (REWRITE_TAC [finite_extension, ← GSYM SUBSET_ANTISYM_EQ, field_extension] THEN
    MESON_TAC [RING_SPAN_SUBSET, RING_MONOMORPHISM_IMP_HOMOMORPHISM])

  let FINITE_EXTENSION_SPANNING ← prove
   r"!(h:A->B) k l.
          finite_extension (k,l) h <=>
          field_extension (k,l) h /\ ?b. FINITE b /\ ring_spanning (k,l) h b"
   (REWRITE_TAC [finite_extension, ring_spanning])

  let FINITE_EXTENSION_BASIS ← prove
   r"!(h:A->B) k l.
          finite_extension (k,l) h <=>
          field_extension (k,l) h /\ ?b. FINITE b /\ ring_basis (k,l) h b"
   (REWRITE_TAC [FINITE_EXTENSION_SPANNING] THEN
    MESON_TAC [ring_basis, field_extension, ring_monomorphism,
              RING_SPANNING_CONTAINS_BASIS, FINITE_SUBSET])

  let FINITE_EXTENSION_ANY ← prove
   r"!(h:A->B) k l b.
          ring_basis (k,l) h b
          ==> (finite_extension (k,l) h <=>
               field_extension (k,l) h /\ FINITE b)"
   (MESON_TAC [RING_MATROID_FINITE_DIMENSIONAL, finite_extension,
              RING_MATROID_BASIS, field_extension, ring_monomorphism,
              MATROID_FINITE_DIMENSIONAL_ANY])

  let FINITE_EXTENSION_ISOMORPHISM ← prove
   r"!(f:A->B) k l.
          (field k \/ field l) /\ ring_isomorphism (k,l) f
          ==> finite_extension (k,l) f"
   (REPEAT GEN_TAC THEN DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    ASM_SIMP_TAC [finite_extension, FIELD_EXTENSION_ISOMORPHISM] THEN
    EXISTS_TAC (← q r"{ring_1 l:B}") THEN REWRITE_TAC [FINITE_SING, SING_SUBSET] THEN
    ASM_SIMP_TAC [RING_SPAN_SING, RING_1, RING_ISOMORPHISM_IMP_HOMOMORPHISM] THEN
    REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, SUBSET, FORALL_IN_GSPEC] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM) THEN
    REWRITE_TAC [ring_homomorphism, SUBSET, FORALL_IN_IMAGE] THEN
    STRIP_TAC THEN ASM_SIMP_TAC [RING_MUL_RID] THEN
    X_GEN_TAC (← q "y:B") THEN DISCH_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"p /\ q <=> ~(p ==> ~q)")] THEN
    ASM_SIMP_TAC [RING_MUL_RID] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP RING_ISOMORPHISM_IMP_EPIMORPHISM) THEN
    REWRITE_TAC [ring_epimorphism] THEN (ASM SET_TAC []))

  let FINITE_EXTENSION_TRANS ← prove
   r"!(f:A->B) (g:B->C) k l m.
          finite_extension (k,l) f /\ finite_extension (l,m) g
          ==> finite_extension (k,m) (g o f)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [FINITE_EXTENSION_BASIS] THEN
    REWRITE_TAC [IMP_CONJ, LEFT_IMP_EXISTS_THM] THEN
    DISCH_TAC THEN X_GEN_TAC (← q r"b:B->bool") THEN REPEAT DISCH_TAC THEN
    X_GEN_TAC (← q r"c:C->bool") THEN REPEAT DISCH_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC [FIELD_EXTENSION_TRANS], ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"(g:B->C) o (f:A->B)", ← q "k:A ring", ← q "m:C ring"]
          RING_BASIS_EXISTS) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [FIELD_EXTENSION_TRANS, field_extension, ring_monomorphism],
      MATCH_MP_TAC MONO_EXISTS] THEN
    X_GEN_TAC (← q r"d:C->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (← ISPECL [← q "f:A->B", ← q "g:B->C", ← q "k:A ring", ← q "l:B ring", ← q "m:C ring",
                   ← q r"b:B->bool", ← q r"c:C->bool", ← q r"d:C->bool"]
          FIELD_EXTENSION_TOWER_LAW) THEN
    ASM_MESON_TAC [CARD_MUL_FINITE, CARD_FINITE_CONG])

  let FINITE_EXTENSION_TRANS_EQ ← prove
   r"!(f:A->B) (g:B->C) k l m.
          field_extension (k,l) f /\ field_extension (l,m) g
          ==> (finite_extension (k,m) (g o f) <=>
               finite_extension (k,l) f /\ finite_extension (l,m) g)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q "f:A->B", ← q "g:B->C", ← q "k:A ring", ← q "l:B ring", ← q "m:C ring"]
          FIELD_EXTENSION_TRANS) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"(g:B->C) o (f:A->B)", ← q "k:A ring", ← q "m:C ring"]
          RING_BASIS_EXISTS) THEN
    MP_TAC (← ISPECL [← q "g:B->C", ← q "l:B ring", ← q "m:C ring"] RING_BASIS_EXISTS) THEN
    MP_TAC (← ISPECL [← q "f:A->B", ← q "k:A ring", ← q "l:B ring"] RING_BASIS_EXISTS) THEN
    MAP_EVERY (fun t =>
      ANTS_TAC THENL
       [ASM_MESON_TAC [FIELD_EXTENSION_TRANS, field_extension, ring_monomorphism],
        DISCH_THEN (X_CHOOSE_TAC t)])
     [← q r"b:B->bool", ← q r"c:C->bool", ← q r"d:C->bool"] THEN
    MP_TAC (← ISPECL [← q "f:A->B", ← q "g:B->C", ← q "k:A ring", ← q "l:B ring", ← q "m:C ring",
                   ← q r"b:B->bool", ← q r"c:C->bool", ← q r"d:C->bool"]
          FIELD_EXTENSION_TOWER_LAW) THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (← ISPECL [← q r"(g:B->C) o (f:A->B)", ← q "k:A ring", ← q "m:C ring", ← q r"d:C->bool"]
          FINITE_EXTENSION_ANY) THEN
    MP_TAC (← ISPECL [← q "g:B->C", ← q "l:B ring", ← q "m:C ring", ← q r"c:C->bool"]
          FINITE_EXTENSION_ANY) THEN
    MP_TAC (← ISPECL [← q "f:A->B", ← q "k:A ring", ← q "l:B ring", ← q r"b:B->bool"]
          FINITE_EXTENSION_ANY) THEN
    ASM_REWRITE_TAC [] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN
    DISCH_THEN (MP_TAC o MATCH_MP CARD_FINITE_CONG) THEN
    REWRITE_TAC [CARD_MUL_FINITE_EQ] THEN
    ASM_MESON_TAC [RING_SPANNING_IMP_NONEMPTY, ring_basis])

  /- --------------------------------------------------------------------- -/
  /- Finitely generated field extensions.                                  -/
  /- --------------------------------------------------------------------- -/

  let finitely_generated_extension ← new_definition
   r"finitely_generated_extension (k,l) (h:A->B) <=>
       field_extension (k,l) h /\
       ?b. FINITE b /\ b SUBSET ring_carrier l /\
           subfield_generated l (IMAGE h (ring_carrier k) UNION b) = l"

  let FINITELY_GENERATED_IMP_FIELD_EXTENSION ← prove
   r"!(h:A->B) k l.
          finitely_generated_extension(k,l) h ==> field_extension(k,l) h"
   (SIMP_TAC [finitely_generated_extension])

  let FINITE_IMP_FINITELY_GENERATED_EXTENSION ← prove
   r"!(h:A->B) k l.
          finite_extension (k,l) h ==> finitely_generated_extension (k,l) h"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [finite_extension, finitely_generated_extension] THEN
    REWRITE_TAC [SUBFIELD_GENERATED_EQ] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ,
                RING_CARRIER_SUBFIELD_GENERATED_SUBSET] THEN
    ASM_MESON_TAC [RING_SPAN_SUBSET_SUBFIELD_GENERATED, field_extension,
                  RING_MONOMORPHISM_IMP_HOMOMORPHISM])

  let FINITELY_GENERATED_EXTENSION ← prove
   r"!(h:A->B) k l.
       finitely_generated_extension (k,l) h <=>
       field_extension (k,l) h /\
       ?b. FINITE b /\ b SUBSET ring_carrier l /\
           ring_carrier l SUBSET
           ring_carrier(subfield_generated l (IMAGE h (ring_carrier k) UNION b))"
   (REWRITE_TAC [finitely_generated_extension, SUBFIELD_GENERATED_EQ,
                ← GSYM SUBSET_ANTISYM_EQ] THEN
    REWRITE_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET])

  let FINITELY_GENERATED_EXTENSION_TRANS ← prove
   r"!(f:A->B) (g:B->C) k l m.
          finitely_generated_extension (k,l) f /\
          finitely_generated_extension (l,m) g
          ==> finitely_generated_extension (k,m) (g o f)"
   (← do
    let r1 ← SET_RULE
      (← q r"s SUBSET t ==> IMAGE f t SUBSET u ==> IMAGE f s SUBSET u")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [FINITELY_GENERATED_EXTENSION] THEN
    REWRITE_TAC [IMP_CONJ, LEFT_IMP_EXISTS_THM] THEN DISCH_TAC THEN
    X_GEN_TAC (← q r"b:B->bool") THEN REPEAT DISCH_TAC THEN
    X_GEN_TAC (← q r"c:C->bool") THEN REPEAT DISCH_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC [FIELD_EXTENSION_TRANS], ALL_TAC] THEN
    EXISTS_TAC (← q r"IMAGE (g:B->C) b UNION c") THEN
    ASM_SIMP_TAC [FINITE_IMAGE, FINITE_UNION, UNION_SUBSET] THEN CONJ_TAC THENL
     [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC [SUBSET, FIELD_EXTENSION_CARRIER],
      REWRITE_TAC [IMAGE_o, ← GSYM UNION_ASSOC, ← GSYM IMAGE_UNION]] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
      (← REWRITE_RULE [IMP_CONJ] SUBSET_TRANS)) THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC [UNION_SUBSET],
      ASM_MESON_TAC [SUBFIELD_SUBFIELD_GENERATED, field_extension]] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP r1) THEN
      MP_TAC (← ISPECL [← q "l:B ring", ← q "m:C ring", ← q "g:B->C"]
        SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE) THEN
      DISCH_THEN (fun th =>
        W (MP_TAC o PART_MATCH (rand o rand) th o lhand o snd)) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC [FIELD_EXTENSION_IMP_MONOMORPHISM, UNION_SUBSET] THEN
        RULE_ASSUM_TAC (REWRITE_RULE
         [field_extension, ring_monomorphism, ring_homomorphism]) THEN
        ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED],
        DISCH_THEN (SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN SET_TAC [],
      REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN ASM_REWRITE_TAC [IN_UNION] THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_IN_UNION] THEN
      ASM_MESON_TAC [SUBSET, FIELD_EXTENSION_CARRIER]]))

  -- @@RETURN BEGIN
  return { finite_extension, RING_MATROID_FINITE_DIMENSIONAL, FINITE_IMP_FIELD_EXTENSION,
           FINITE_EXTENSION_RING_MATROID, FINITE_EXTENSION, FINITE_EXTENSION_SPANNING,
           FINITE_EXTENSION_BASIS, FINITE_EXTENSION_ANY, FINITE_EXTENSION_ISOMORPHISM,
           FINITE_EXTENSION_TRANS, FINITE_EXTENSION_TRANS_EQ,
           finitely_generated_extension, FINITELY_GENERATED_IMP_FIELD_EXTENSION,
           FINITE_IMP_FINITELY_GENERATED_EXTENSION, FINITELY_GENERATED_EXTENSION,
           FINITELY_GENERATED_EXTENSION_TRANS }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Algebraic elements and algebraic extensions.  (fieldtheory.ml 2589-2829)  -/
/- ------------------------------------------------------------------------- -/

structure AlgebraicExtension where
  -- @@FIELDS
  algebraic_over : thm
  transcendental_over : thm
  algebraic_extension : thm
  ALGEBRAIC_OVER : thm
  ALGEBRAIC_IMP_FIELD_EXTENSION : thm
  ALGEBRAIC_OVER_ALT : thm
  ALGEBRAIC_OVER_IN_CARRIER : thm
  TRANSCENDENTAL_OVER_IN_CARRIER : thm
  ALGEBRAIC_OVER_IMAGE_GEN : thm
  ALGEBRAIC_OVER_IMAGE : thm
  ALGEBRAIC_OVER_IMAGE_SUBSET : thm
  ALGEBRAIC_OVER_REFL : thm
  ALGEBRAIC_OVER_SUBRING_GENERATED : thm
  ALGEBRAIC_OVER_SUBFIELD_GENERATED : thm
  ALGEBRAIC_OVER_SUBRING_GENERATED_MONO : thm
  ALGEBRAIC_OVER_SUBFIELD_SUBRING_GENERATED : thm
  deriving Inhabited

@[nospecialize]
def setupAlgebraicExtension [HolBase] (D : FieldTheoryDeps) (BSubfieldGenerated : SubfieldGenerated) (BSubfieldGenerated1 : SubfieldGenerated1) (BSubfieldGenerated2 : SubfieldGenerated2) (BSubfieldQuotients : SubfieldQuotients) (BFieldExtension : FieldExtension) :
    ExceptT String IO AlgebraicExtension := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, TAUT, new_definition, .. } := D
  let { FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING, FORALL_IN_IMAGE,
        FORALL_IN_INSERT, .. } := D.core2
  let { IMP_CONJ, INTEGRAL_DOMAIN_POLY_RING, IN_ELIM_THM, IN_POLY_RING_CARRIER,
        IN_SING, IN_UNIV, I_THM, LEFT_IMP_EXISTS_THM, .. } := D.core3
  let { MONO_EXISTS, NOT_IN_EMPTY, POLY_CLAUSES, POLY_CONST, POLY_CONST_0,
        POLY_CONST_EQ, POLY_DEG_0, POLY_DEG_EQ_0, .. } := D.core4
  let { POLY_EXTEND, POLY_EXTEND_CONST, POLY_EXTEND_FROM_SUBRING_GENERATED,
        POLY_EXTEND_INTO_SUBRING_GENERATED, POLY_EXTEND_MUL, POLY_EXTEND_REINDEX,
        POLY_EXTEND_SUB, POLY_EXTEND_VAR, POLY_RING, POLY_SUBRING_GENERATED_CLAUSES,
        POLY_VAR_EQ_CONST, RING_CARRIER_POLY_SUBRING_GENERATED_MONO,
        RING_CARRIER_SUBRING_GENERATED_SUBSET, .. } := D.core5
  let { RING_HOMOMORPHISM_INTO_SUBRING, RING_ISOMORPHISMS_ISOMORPHISM,
        RING_ISOMORPHISMS_POLY_REINDEX, RING_ISOMORPHISM_IMP_MONOMORPHISM,
        RING_MONOMORPHISM_EQ_0, RING_MONOMORPHISM_IMP_HOMOMORPHISM, .. } := D.core6
  let { RING_MUL_RZERO, RING_POLYNOMIAL, RING_POLYNOMIAL_CONST, RING_POLYNOMIAL_SUB,
        RING_POLYNOMIAL_VAR, RING_SUB_EQ_0, RING_SUB_REFL, SUBRING_GENERATED, .. } := D.core7
  let { SUBRING_GENERATED_INC_GEN, SUBRING_GENERATED_RESTRICT, SUBSET, SUBSET_INTER,
        SUBSET_TRANS, UNIV_1, integral_domain, .. } := D.core8
  let { o_DEF, poly_0, ring_homomorphism, ring_monomorphism, ring_polynomial,
        ring_powerseries, .. } := D.core9
  let { FIELD_SUBFIELD_GENERATED, RING_CARRIER_SUBFIELD_GENERATED_SUBSET,
        SUBFIELD_GENERATED, SUBFIELD_GENERATED_SUBSET_CARRIER,
        SUBRING_GENERATED_BY_SUBFIELD_GENERATED, SUBRING_SUBSET_SUBFIELD_GENERATED, .. } := BSubfieldGenerated
  let { SUBFIELD_GENERATED_INC_GEN, .. } := BSubfieldGenerated1
  let { POLY_CONST_SUBFIELD_GENERATED, POLY_SUBFIELD_GENERATED_CLAUSES, .. } := BSubfieldGenerated2
  let { POLY_OVER_SUBFIELD_GENERATED_DENOMINATOR, .. } := BSubfieldQuotients
  let { FIELD_EXTENSION_IMP_HOMOMORPHISM, FIELD_EXTENSION_IMP_SUBSET,
        FIELD_EXTENSION_REFL, field_extension, .. } := BFieldExtension
  -- @@SCOPE END

  let algebraic_over ← new_definition
   r"algebraic_over (k,l) (h:A->B) x <=>
          x IN ring_carrier l /\
          ?p. p IN ring_carrier(poly_ring k (:1)) /\
              ~(p = ring_0(poly_ring k (:1))) /\
              poly_extend(k,l) h (\v. x) p = ring_0 l"

  let transcendental_over ← new_definition
   r"transcendental_over (k,l) (h:A->B) x <=>
          x IN ring_carrier l /\ ~(algebraic_over (k,l) h x)"

  let algebraic_extension ← new_definition
   r"algebraic_extension (k,l) (h:A->B) <=>
          field_extension (k,l) h /\
          !x. x IN ring_carrier l ==> algebraic_over (k,l) h x"

  let ALGEBRAIC_OVER ← prove
   r"!(h:A->B) k l (v:V) x.
           algebraic_over (k,l) h x <=>
           x IN ring_carrier l /\
           ?p. p IN ring_carrier (poly_ring k {v}) /\
               ~(p = ring_0 (poly_ring k {v})) /\
               poly_extend (k,l) h (\v. x) p = ring_0 l"
   (← do
    let s1 ← SET_RULE (← q r"BIJ (\x. b) {a} {b}")
    -- `W(fun (asl,w) -> let ft,gt = dest_pair(rand(lhand w)) in
    --     ABBREV_TAC(mk_eq(mk_var("f",type_of ft),ft)) THEN
    --     ABBREV_TAC(mk_eq(mk_var("g",type_of gt),gt)))`
    let abbrevFG : tactic := fun gl => tactic_of (do
      let w := gl.2
      let mkEq ← ExceptT.mk (mk_eq : IO _)
      let (ft, gt) ← liftExcept (do HolMath.Pair.dest_pair (← rand (← lhand w)))
      let eqf ← liftExcept (mkEq (mk_var "f" (type_of ft), ft))
      let eqg ← liftExcept (mkEq (mk_var "g" (type_of gt), gt))
      pure (ABBREV_TAC eqf THEN ABBREV_TAC eqg)) gl
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [algebraic_over] THEN
    ASM_CASES_TAC (← q r"(x:B) IN ring_carrier l") THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (← ISPECL [← q "k:A ring", ← q "{v:V}", ← q "(:1)", ← q r"\x:V. one", ← q r"\u:1. (v:V)"]
     RING_ISOMORPHISMS_POLY_REINDEX) THEN
    REWRITE_TAC [UNIV_1, FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
    REWRITE_TAC [IN_SING] THEN
    abbrevFG THEN
    DISCH_TAC THEN EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q r"p:(1->num)->A") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"(g:((1->num)->A)->(V->num)->A) p") THEN
      FIRST_X_ASSUM (fun th => tactic_of do pure (ASSUME_TAC (← elThm 1
          (CONJUNCTS (← GEN_REWRITE_RULE id [RING_ISOMORPHISMS_ISOMORPHISM] th))))),
      DISCH_THEN (X_CHOOSE_THEN (← q r"q:(V->num)->A") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"(f:((V->num)->A)->(1->num)->A) q") THEN
      FIRST_X_ASSUM (fun th => tactic_of do pure (ASSUME_TAC (← elThm 0
          (CONJUNCTS (← GEN_REWRITE_RULE id [RING_ISOMORPHISMS_ISOMORPHISM] th)))))] THEN
    FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP RING_ISOMORPHISM_IMP_MONOMORPHISM) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ring_homomorphism, SUBSET, FORALL_IN_IMAGE]) THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          RING_MONOMORPHISM_EQ_0)) THEN
    ASM_SIMP_TAC [] THEN DISCH_THEN (K ALL_TAC) THENL
     [EXPAND_TAC "g" THEN MP_TAC (← ISPECL
       [← q "h:A->B", ← q "k:A ring", ← q "l:B ring", ← q "{v:V}", ← q "{one}", ← q r"p:(1->num)->A",
        ← q r"\x:V. one", ← q r"(\v. x):1->B"] POLY_EXTEND_REINDEX),
      EXPAND_TAC "f" THEN MP_TAC (← ISPECL
       [← q "h:A->B", ← q "k:A ring", ← q "l:B ring", ← q "{one}", ← q "{v:V}", ← q r"q:(V->num)->A",
        ← q r"\x:1. (v:V)", ← q r"(\v. x):V->B"] POLY_EXTEND_REINDEX)] THEN
    ASM_REWRITE_TAC [o_DEF, s1] THEN
    ASM_MESON_TAC [IN_POLY_RING_CARRIER]))

  let ALGEBRAIC_IMP_FIELD_EXTENSION ← prove
   r"!(h:A->B) k l. algebraic_extension(k,l) h ==> field_extension(k,l) h"
   (SIMP_TAC [algebraic_extension])

  let ALGEBRAIC_OVER_ALT ← prove
   r"!(h:A->B) k l x.
          ring_monomorphism(k,l) h
          ==> (algebraic_over (k,l) (h:A->B) x <=>
               x IN ring_carrier l /\
               ?p. p IN ring_carrier(poly_ring k (:1)) /\
                   ~(poly_deg k p = 0) /\
                   poly_extend(k,l) h (\v. x) p = ring_0 l)"
   (← do
    let t1 ← TAUT (← q r"(r ==> ~q) ==> p ==> q ==> ~r")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [algebraic_over] THEN
    EQ_TAC THENL [ALL_TAC, MESON_TAC [POLY_DEG_0, POLY_RING]] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"p:(1->num)->A") THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [IN_POLY_RING_CARRIER]) THEN
    ASM_SIMP_TAC [POLY_DEG_EQ_0] THEN
    MATCH_MP_TAC t1 THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q "c:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [POLY_EXTEND_CONST, RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
    REWRITE_TAC [POLY_RING, poly_0, POLY_CONST_EQ] THEN
    ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0]))

  let ALGEBRAIC_OVER_IN_CARRIER ← prove
   r"!(h:A->B) k l a.
          algebraic_over (k,l) h a ==> a IN ring_carrier l"
   (SIMP_TAC [algebraic_over])

  let TRANSCENDENTAL_OVER_IN_CARRIER ← prove
   r"!(h:A->B) k l a.
          transcendental_over (k,l) h a ==> a IN ring_carrier l"
   (SIMP_TAC [transcendental_over])

  let ALGEBRAIC_OVER_IMAGE_GEN ← prove
   r"!(h:A->B) k l x.
          ~(trivial_ring k /\ x = ring_0 k /\ h x = ring_0 l) /\
          ring_homomorphism(k,l) h /\ x IN ring_carrier k
          ==> algebraic_over(k,l) h (h x)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [algebraic_over] THEN
    FIRST_ASSUM (MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE id [ring_homomorphism]) THEN
    ASM_SIMP_TAC [SUBSET, FORALL_IN_IMAGE] THEN DISCH_TAC THEN
    EXISTS_TAC (← q r"poly_sub k (poly_var k one) (poly_const k (x:A))") THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
     [POLY_CLAUSES] THEN
    ASM_SIMP_TAC [POLY_EXTEND_SUB, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST,
                 POLY_EXTEND_VAR, POLY_EXTEND_CONST, IN_UNIV, RING_SUB_REFL,
                 ← GSYM RING_POLYNOMIAL, RING_POLYNOMIAL_VAR, RING_SUB_EQ_0,
                 RING_POLYNOMIAL_CONST, RING_POLYNOMIAL_SUB] THEN
    ASM_REWRITE_TAC [POLY_VAR_EQ_CONST] THEN ASM_MESON_TAC [ring_homomorphism])

  let ALGEBRAIC_OVER_IMAGE ← prove
   r"!(h:A->B) k l x.
          field_extension(k,l) h /\ x IN ring_carrier k
          ==> algebraic_over(k,l) h (h x)"
   (MESON_TAC [ALGEBRAIC_OVER_IMAGE_GEN, field_extension, ring_monomorphism,
              FIELD_IMP_NONTRIVIAL_RING])

  let ALGEBRAIC_OVER_IMAGE_SUBSET ← prove
   r"!(h:A->B) k l.
          field_extension(k,l) h
          ==> IMAGE h (ring_carrier k) SUBSET {x | algebraic_over(k,l) h x}"
   (REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
    SIMP_TAC [ALGEBRAIC_OVER_IMAGE])

  let ALGEBRAIC_OVER_REFL ← prove
   r"!k y:A. field k
             ==> (algebraic_over (k,k) I y <=> y IN ring_carrier k)"
   (MESON_TAC [ALGEBRAIC_OVER_IN_CARRIER, ALGEBRAIC_OVER_IMAGE,
              FIELD_EXTENSION_REFL, I_THM])

  let ALGEBRAIC_OVER_SUBRING_GENERATED ← prove
   r"!(h:A->B) k l s x.
          field_extension(k,l) h /\
          IMAGE h (ring_carrier k) SUBSET s /\
          algebraic_over(k,l) h x /\ x IN s
          ==> algebraic_over(k,subring_generated l s) h x"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [algebraic_over]) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC [algebraic_over, SUBRING_GENERATED_INC_GEN] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"p:(1->num)->A") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [← CONJUNCT2 SUBRING_GENERATED] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC POLY_EXTEND_INTO_SUBRING_GENERATED THEN
    EXISTS_TAC (← q "(:1)") THEN ASM_SIMP_TAC [SUBRING_GENERATED_INC_GEN] THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_INTO_SUBRING THEN
    ASM_MESON_TAC [FIELD_EXTENSION_IMP_HOMOMORPHISM])

  let ALGEBRAIC_OVER_SUBFIELD_GENERATED ← prove
   r"!(h:A->B) k l s x.
          field_extension(k,l) h /\
          IMAGE h (ring_carrier k) SUBSET s /\
          algebraic_over(k,l) h x /\ x IN s
          ==> algebraic_over(k,subfield_generated l s) h x"
   (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    MATCH_MP_TAC ALGEBRAIC_OVER_SUBRING_GENERATED THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP ALGEBRAIC_OVER_IN_CARRIER) THEN
    ASM_SIMP_TAC [SUBFIELD_GENERATED_INC_GEN] THEN
    TRANS_TAC SUBSET_TRANS (← q r"ring_carrier l INTER s:B->bool") THEN
    ASM_REWRITE_TAC [SUBFIELD_GENERATED_SUBSET_CARRIER, SUBSET_INTER] THEN
    ASM_MESON_TAC [FIELD_EXTENSION_IMP_SUBSET])

  let ALGEBRAIC_OVER_SUBRING_GENERATED_MONO ← prove
   r"!(h:A->B) k l s t x.
          algebraic_over (subring_generated k s,l) h x /\ s SUBSET t
          ==> algebraic_over (subring_generated k t,l) h x"
   (REWRITE_TAC [algebraic_over, POLY_EXTEND_FROM_SUBRING_GENERATED] THEN
    REWRITE_TAC [POLY_SUBRING_GENERATED_CLAUSES] THEN
    MESON_TAC [RING_CARRIER_POLY_SUBRING_GENERATED_MONO, SUBSET])

  let ALGEBRAIC_OVER_SUBFIELD_SUBRING_GENERATED ← prove
   r"!(h:A->B) k l s x.
          field_extension(k,l) h
          ==> (algebraic_over (subfield_generated k s,l) h x <=>
               algebraic_over (subring_generated k s,l) h x)"
   (← do
    let t1 ← TAUT
      (← q r"(p' ==> p) /\ p' /\ (q ==> t ==> r) /\ ~s
        ==> (p ==> q) ==> (p' /\ r ==> s) ==> ~t")
    pure (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [REWRITE_TAC [algebraic_over] THEN
      ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
      REWRITE_TAC [POLY_EXTEND_FROM_SUBRING_GENERATED,
                  POLY_SUBRING_GENERATED_CLAUSES] THEN
      REWRITE_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED],
      ONCE_REWRITE_TAC [SUBRING_GENERATED_RESTRICT] THEN
      ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
      MESON_TAC [SUBFIELD_GENERATED_SUBSET_CARRIER,
                ALGEBRAIC_OVER_SUBRING_GENERATED_MONO]] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"p:(1->num)->A") STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [← CONJUNCT1 POLY_RING]) THEN
    REWRITE_TAC [ring_polynomial, IN_ELIM_THM, ring_powerseries] THEN
    REWRITE_TAC [← CONJUNCT2 SUBFIELD_GENERATED] THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q "k:A ring", ← q r"s:A->bool", ← q "(:1)", ← q r"p:(1->num)->A"]
          POLY_OVER_SUBFIELD_GENERATED_DENOMINATOR) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [ASM_MESON_TAC [field_extension, FIELD_SUBFIELD_GENERATED],
      DISCH_THEN (X_CHOOSE_THEN (← q "d:A") STRIP_ASSUME_TAC)] THEN
    EXISTS_TAC (← q r"poly_mul k (poly_const k d) p:(1->num)->A") THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MP_TAC (← EQ_IMP_RULE (← ISPECL [← q "subfield_generated k s:A ring", ← q "(:1)"]
          INTEGRAL_DOMAIN_POLY_RING)).2 THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC [FIELD_SUBFIELD_GENERATED,
                      FIELD_IMP_INTEGRAL_DOMAIN, field_extension],
        REWRITE_TAC [integral_domain]] THEN
      DISCH_THEN (MP_TAC o SPECL
       [← q r"poly_const k d:(1->num)->A", ← q r"p:(1->num)->A"] o CONJUNCT2) THEN
      MP_TAC (← ISPECL [← q "k:A ring", ← q r"s:A->bool", ← q "(:1)",
                     ← q r"poly_const k d:(1->num)->A", ← q r"p:(1->num)->A"]
        (← elThm 4 (CONJUNCTS POLY_SUBFIELD_GENERATED_CLAUSES))) THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC t1 THEN
      REPEAT CONJ_TAC THENL
       [SIMP_TAC [POLY_RING, ring_polynomial, ring_powerseries, IN_ELIM_THM],
        ASM_MESON_TAC [POLY_CONST_SUBFIELD_GENERATED, POLY_CONST,
                      SUBRING_SUBSET_SUBFIELD_GENERATED, SUBSET],
        REWRITE_TAC [POLY_SUBFIELD_GENERATED_CLAUSES] THEN
        ASM_SIMP_TAC [POLY_RING],
        ASM_REWRITE_TAC [POLY_SUBFIELD_GENERATED_CLAUSES] THEN
        ASM_MESON_TAC [POLY_CONST_0, POLY_CONST_EQ, POLY_RING]],
      MP_TAC (← ISPECL [← q "k:A ring", ← q "l:B ring", ← q "h:A->B", ← q r"(\v. x):1->B",
                     ← q r"poly_const k d:(1->num)->A", ← q r"p:(1->num)->A"]
          POLY_EXTEND_MUL) THEN
      ASM_SIMP_TAC [RING_MUL_RZERO, POLY_EXTEND] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC [RING_POLYNOMIAL_CONST, FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
      ASM_REWRITE_TAC [ring_polynomial, ring_powerseries] THEN
      (ASM SET_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET,
                  RING_CARRIER_SUBRING_GENERATED_SUBSET])]))

  -- @@RETURN BEGIN
  return { algebraic_over, transcendental_over, algebraic_extension, ALGEBRAIC_OVER,
           ALGEBRAIC_IMP_FIELD_EXTENSION, ALGEBRAIC_OVER_ALT, ALGEBRAIC_OVER_IN_CARRIER,
           TRANSCENDENTAL_OVER_IN_CARRIER, ALGEBRAIC_OVER_IMAGE_GEN,
           ALGEBRAIC_OVER_IMAGE, ALGEBRAIC_OVER_IMAGE_SUBSET, ALGEBRAIC_OVER_REFL,
           ALGEBRAIC_OVER_SUBRING_GENERATED, ALGEBRAIC_OVER_SUBFIELD_GENERATED,
           ALGEBRAIC_OVER_SUBRING_GENERATED_MONO,
           ALGEBRAIC_OVER_SUBFIELD_SUBRING_GENERATED }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Algebraic elements and extensions: nonmonomorphism, equality variants,    -/
/- finite dimension, simple extensions and their spans.                      -/
/- (fieldtheory.ml 2830-3037)                                                -/
/- ------------------------------------------------------------------------- -/

structure AlgebraicOverBasics where
  -- @@FIELDS
  ALGEBRAIC_OVER_NONMONOMORPHISM : thm
  ALGEBRAIC_EXTENSION : thm
  ALGEBRAIC_EXTENSION_ALT : thm
  ALGEBRAIC_OVER_EQ : thm
  ALGEBRAIC_OVER_EQ_EQ : thm
  ALGEBRAIC_EXTENSION_EQ : thm
  FINITE_IMP_ALGEBRAIC_EXTENSION_EXPLICIT : thm
  FINITE_IMP_ALGEBRAIC_EXTENSION : thm
  RING_SIMPLE_EXTENSION_SPAN : thm
  RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN : thm
  deriving Inhabited

@[nospecialize]
def setupAlgebraicOverBasics [HolBase] (D : FieldTheoryDeps) (BFieldExtension : FieldExtension) (BRingSpan : RingSpan) (BFinitary : Finitary) (BFiniteExtension : FiniteExtension) (BAlgebraicExtension : AlgebraicExtension) :
    ExceptT String IO AlgebraicOverBasics := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, TAUT, .. } := D
  let { CARD_NUMSEG, COND_RAND, COND_RATOR, .. } := D.core1
  let { FINITE_IMAGE, FINITE_MONOMIAL_VARS_1, FINITE_NUMSEG, FINITE_NUMSEG_LE,
        FINITE_SING, FINITE_SUBSET, FINITE_UNIONS, FORALL_FUN_FROM_1, FORALL_IN_GSPEC,
        FORALL_IN_IMAGE, FORALL_IN_UNION, FUN_EQ_THM, HAS_SIZE, IMAGE_POLY_EXTEND_1, .. } := D.core2
  let { IMP_CONJ_ALT, INFINITE, INSERT_SUBSET, IN_ELIM_THM, IN_INSERT, IN_NUMSEG,
        IN_SING, LEFT_IMP_EXISTS_THM, LE_0, .. } := D.core3
  let { MONOMIAL_DEG_LE_POLY_DEG, MONOMIAL_DEG_UNIVARIATE, MONOMIAL_VARS_UNIVARIATE,
        MONO_EXISTS, POLY_0, POLY_DEG_LE_EQ, POLY_DIVISION, .. } := D.core4
  let { POLY_EXTEND, POLY_EXTEND_ADD, POLY_EXTEND_EQ, POLY_EXTEND_EVALUATE,
        POLY_EXTEND_MUL, POLY_EXTEND_UNIVARIATE, POLY_MONOMIAL_IN_CARRIER, POLY_RING,
        RING_0, RING_ADD_LZERO, .. } := D.core5
  let { RING_HOMOMORPHISM_EQ, RING_HOMOMORPHISM_POLY_EXTEND, RING_MONOMORPHISM_ALT,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, .. } := D.core6
  let { RING_MUL_LZERO, RING_MUL_RZERO, RING_POLYNOMIAL, RING_POLYNOMIAL_MUL, RING_POW,
        RING_POW_IN_SUBRING_GENERATED, RING_SUM_RESTRICT_SET, RING_SUM_SUPERSET,
        SIMPLE_IMAGE, .. } := D.core7
  let { SUBRING_GENERATED_INC, SUBRING_GENERATED_MINIMAL, SUBRING_SUBRING_GENERATED,
        SUBSET, SUBSET_ANTISYM, SUBSET_REFL, SUBSET_TRANS, coeff, .. } := D.core8
  let { one, poly_eval, ring_homomorphism, ring_monomorphism, ring_polynomial,
        ring_powerseries, .. } := D.core9
  let { FIELD_EXTENSION_EQ, field_extension, .. } := BFieldExtension
  let { RING_SPAN_0, RING_SPAN_INC, RING_SPAN_MONO, RING_SPAN_MUL, RING_SPAN_SUM, .. } := BRingSpan
  let { RING_DEPENDENT_SPAN_IMAGE, RING_SPAN_SUBSET_SUBRING_GENERATED, .. } := BFinitary
  let { finite_extension, .. } := BFiniteExtension
  let { algebraic_extension, algebraic_over, .. } := BAlgebraicExtension
  -- @@SCOPE END

  let ALGEBRAIC_OVER_NONMONOMORPHISM ← prove
   r"!(h:A->B) k l a.
        ring_homomorphism(k,l) h /\ a IN ring_carrier l
        ==> (algebraic_over (k,l) h a <=>
             ~ring_monomorphism (poly_ring k (:1),l)
                                (poly_extend(k,l) h (\v. a)))"
   (SIMP_TAC [RING_MONOMORPHISM_ALT, RING_HOMOMORPHISM_POLY_EXTEND] THEN
    MESON_TAC [algebraic_over])

  let ALGEBRAIC_EXTENSION ← prove
   r"!(f:A->B) k l.
        algebraic_extension (k,l) f <=>
        field_extension (k,l) f /\
        !x. x IN ring_carrier l
            ==> ?p. p IN ring_carrier(poly_ring k (:1)) /\
                    ~(p = ring_0(poly_ring k (:1))) /\
                    poly_extend(k,l) f (\v. x) p = ring_0 l"
   (SIMP_TAC [algebraic_extension, algebraic_over])

  let ALGEBRAIC_EXTENSION_ALT ← prove
   r"!(f:A->B) k l.
        algebraic_extension (k,l) f <=>
        field_extension (k,l) f /\
        !x. x IN ring_carrier l
            ==> ?p. p IN ring_carrier(poly_ring k (:1)) /\
                    ~(p = ring_0(poly_ring k (:1))) /\
                    poly_eval l (f o p) x = ring_0 l"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [field_extension, ALGEBRAIC_EXTENSION, ring_monomorphism] THEN
    REWRITE_TAC [poly_eval] THEN MESON_TAC [POLY_EXTEND_EVALUATE])

  let ALGEBRAIC_OVER_EQ ← prove
   r"!k l a (f:A->B) f'.
          ring_homomorphism (k,l) f /\
          (!x. x IN ring_carrier k ==> f' x = f x) /\
          algebraic_over (k,l) f a
          ==> algebraic_over (k,l) f' a"
   (REPEAT GEN_TAC THEN REWRITE_TAC [algebraic_over] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q "p:(1->num)->A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      pure (GEN_REWRITE_TAC RAND_CONV [← SYM th])) THEN
    MATCH_MP_TAC POLY_EXTEND_EQ THEN EXISTS_TAC (← q "(:1)") THEN
    ASM_REWRITE_TAC [])

  let ALGEBRAIC_OVER_EQ_EQ ← prove
   r"!k l a (f:A->B) f'.
        ring_homomorphism (k,l) f /\
        (!x. x IN ring_carrier k ==> f' x = f x)
        ==> (algebraic_over (k,l) f a <=> algebraic_over (k,l) f' a)"
   (MESON_TAC [ALGEBRAIC_OVER_EQ, RING_HOMOMORPHISM_EQ])

  let ALGEBRAIC_EXTENSION_EQ ← prove
   r"!k l (f:A->B) f'.
        algebraic_extension(k,l) f /\
        (!x. x IN ring_carrier k ==> f' x = f x)
        ==> algebraic_extension (k,l) f'"
   (REWRITE_TAC [algebraic_extension] THEN
    MESON_TAC [ALGEBRAIC_OVER_EQ, FIELD_EXTENSION_EQ, field_extension,
              RING_MONOMORPHISM_IMP_HOMOMORPHISM])

  let FINITE_IMP_ALGEBRAIC_EXTENSION_EXPLICIT ← prove
   r"!(h:A->B) k l a b n.
        field k /\ ring_homomorphism(k,l) h /\ a IN ring_carrier l /\
        b HAS_SIZE n /\ b SUBSET ring_carrier l /\
        ring_carrier l SUBSET ring_span (k,l) h b
        ==> ?p. p IN ring_carrier(poly_ring k (:1)) /\
                ~(p = ring_0 (poly_ring k (:1))) /\
                poly_deg k p <= n /\
                poly_extend (k,l) h (\v. a) p = ring_0 l"
   (← do
    let t3 ← TAUT (← q r"(p ==> r) ==> (~p ==> q) ==> ~q ==> r")
    let t2 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    let t1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    pure (REWRITE_TAC [HAS_SIZE] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q "h:A->B", ← q "k:A ring", ← q "l:B ring",
                   ← q "ring_pow l (a:B)", ← q "0..n", ← q "b:B->bool"]
      RING_DEPENDENT_SPAN_IMAGE) THEN
    ASM_REWRITE_TAC [FINITE_NUMSEG, CARD_NUMSEG] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ALL_TAC, ARITH_TAC] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
       (← REWRITE_RULE [IMP_CONJ_ALT] SUBSET_TRANS)) THEN
      ASM_SIMP_TAC [SUBSET, FORALL_IN_IMAGE, RING_POW],
      REWRITE_TAC [IN_NUMSEG, LE_0, LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC (← q "c:num->A") THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    ABBREV_TAC
     (← q r"p = \m. if m one <= n then (c:num->A) (m one) else ring_0 k") THEN
    EXISTS_TAC (← q "p:(1->num)->A") THEN
    MATCH_MP_TAC t1 THEN CONJ_TAC THENL
     [REWRITE_TAC [← GSYM RING_POLYNOMIAL, ring_polynomial, ring_powerseries,
             MONOMIAL_VARS_UNIVARIATE, INFINITE, FINITE_MONOMIAL_VARS_1] THEN
      EXPAND_TAC "p" THEN CONJ_TAC THENL
       [ASM SET_TAC [RING_POW, RING_0, IN_NUMSEG, LE_0], ALL_TAC] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC (← q "UNIONS {{m | m one = i} | i IN {i:num | i <= n}}") THEN
      CONJ_TAC THENL [ALL_TAC, SET_TAC []] THEN
      REWRITE_TAC [FINITE_UNIONS, SIMPLE_IMAGE, FORALL_IN_IMAGE] THEN
      SIMP_TAC [FINITE_IMAGE, FINITE_NUMSEG_LE] THEN
      X_GEN_TAC (← q "i:num") THEN DISCH_THEN (K ALL_TAC) THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{(\v. i):1->num}") THEN
      REWRITE_TAC [FINITE_SING, SUBSET, FORALL_IN_GSPEC, IN_SING] THEN
      REWRITE_TAC [FUN_EQ_THM] THEN MESON_TAC [one],
      DISCH_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "p" THEN
      REWRITE_TAC [FUN_EQ_THM, FORALL_FUN_FROM_1, POLY_RING, POLY_0] THEN
      ASM_MESON_TAC [IN_NUMSEG, LE_0],
      ALL_TAC] THEN
    MATCH_MP_TAC t2 THEN CONJ_TAC THENL
     [ASM_SIMP_TAC [POLY_DEG_LE_EQ, RING_POLYNOMIAL] THEN EXPAND_TAC "p" THEN
      REWRITE_TAC [FORALL_FUN_FROM_1, MONOMIAL_DEG_UNIVARIATE] THEN
      ASM_MESON_TAC [IN_NUMSEG, LE_0],
      DISCH_TAC] THEN
    ASM_SIMP_TAC [POLY_EXTEND_UNIVARIATE] THEN EXPAND_TAC "p" THEN
    REWRITE_TAC [coeff] THEN ASM_REWRITE_TAC [] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ring_homomorphism, SUBSET, FORALL_IN_IMAGE]) THEN
    ASM_SIMP_TAC [COND_RAND, COND_RATOR, RING_MUL_LZERO, RING_POW] THEN
    REWRITE_TAC [← GSYM RING_SUM_RESTRICT_SET] THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      pure (GEN_REWRITE_TAC RAND_CONV [← SYM th])) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_SUPERSET THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM, IN_NUMSEG, LE_0] THEN
    X_GEN_TAC (← q "i:num") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (← ISPECL [← q "k:A ring", ← q "p:(1->num)->A", ← q r"(\x. i):1->num"]
      MONOMIAL_DEG_LE_POLY_DEG) THEN
    ASM_REWRITE_TAC [RING_POLYNOMIAL, MONOMIAL_DEG_UNIVARIATE] THEN
    MATCH_MP_TAC t3 THEN
    EXPAND_TAC "p" THEN REWRITE_TAC [← ASSUME (← q "i:num <= n")] THEN
    ASM_SIMP_TAC [RING_MUL_LZERO, RING_POW]))

  let FINITE_IMP_ALGEBRAIC_EXTENSION ← prove
   r"!(h:A->B) k l.
        finite_extension (k,l) h ==> algebraic_extension (k,l) h"
   (REPEAT GEN_TAC THEN REWRITE_TAC [finite_extension, algebraic_extension] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN (← q "b:B->bool") STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q "a:B") THEN DISCH_TAC THEN
    REWRITE_TAC [algebraic_over] THEN
    MP_TAC (← ISPECL [← q "h:A->B", ← q "k:A ring", ← q "l:B ring", ← q "a:B",
              ← q "b:B->bool", ← q "CARD(b:B->bool)"]
        FINITE_IMP_ALGEBRAIC_EXTENSION_EXPLICIT) THEN
    ASM_REWRITE_TAC [HAS_SIZE, SUBSET_REFL] THEN
    ASM_MESON_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM])

  let RING_SIMPLE_EXTENSION_SPAN ← prove
   r"!(h:A->B) k l a.
        ring_homomorphism(k,l) h /\ a IN ring_carrier l
        ==> ring_carrier
              (subring_generated l (a INSERT IMAGE h (ring_carrier k))) =
            ring_span (k,l) h { ring_pow l a n | n IN (:num) }"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ASM_SIMP_TAC [← GSYM IMAGE_POLY_EXTEND_1],
      wPart lhand lhand
        RING_SPAN_SUBSET_SUBRING_GENERATED THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] SUBSET_TRANS) THEN
      MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN
      REWRITE_TAC [SUBRING_SUBRING_GENERATED] THEN
      REWRITE_TAC [SUBSET, FORALL_IN_UNION, FORALL_IN_GSPEC] THEN
      REPEAT STRIP_TAC THEN TRY (MATCH_MP_TAC RING_POW_IN_SUBRING_GENERATED) THEN
      MATCH_MP_TAC SUBRING_GENERATED_INC THEN ASM_REWRITE_TAC [IN_INSERT] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [ring_homomorphism]) THEN
      ASM_REWRITE_TAC [INSERT_SUBSET]] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q "p:(1->num)->A") THEN
    STRIP_TAC THEN ASM_SIMP_TAC [POLY_EXTEND_UNIVARIATE] THEN
    REWRITE_TAC [coeff] THEN
    MATCH_MP_TAC RING_SPAN_SUM THEN REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN
    MATCH_MP_TAC RING_SPAN_MUL THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP POLY_MONOMIAL_IN_CARRIER) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ring_homomorphism]) THEN
    REPEAT (CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC]) THEN
    MATCH_MP_TAC RING_SPAN_INC THEN ASM_SIMP_TAC [RING_POW] THEN SET_TAC [])

  let RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN ← prove
   r"!(h:A->B) k l p a.
        field k /\ ring_homomorphism(k,l) h /\ a IN ring_carrier l /\
        p IN ring_carrier(poly_ring k (:1)) /\
        ~(p = ring_0(poly_ring k (:1))) /\
        poly_extend (k,l) h (\v. a) p = ring_0 l
        ==> ring_carrier
              (subring_generated l (a INSERT IMAGE h (ring_carrier k))) =
            ring_span (k,l) h { ring_pow l a n | n < poly_deg k p}"
   (← do
    let s1 ← SET_RULE
      (← q r"P i ==> ring_pow l a i IN {ring_pow l a n | P n}")
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ASM_SIMP_TAC [← GSYM IMAGE_POLY_EXTEND_1],
      ASM_SIMP_TAC [RING_SIMPLE_EXTENSION_SPAN] THEN
      MATCH_MP_TAC RING_SPAN_MONO THEN SET_TAC []] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
    X_GEN_TAC (← q "f:(1->num)->A") THEN STRIP_TAC THEN MP_TAC (← ISPECL
     [← q "k:A ring", ← q "f:(1->num)->A", ← q "p:(1->num)->A"] POLY_DIVISION) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q "q:(1->num)->A", ← q "r:(1->num)->A"] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [POLY_RING] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [← GSYM RING_POLYNOMIAL]) THEN
    ASM_SIMP_TAC [POLY_EXTEND_ADD, POLY_EXTEND_MUL, RING_POLYNOMIAL_MUL] THEN
    ASM_SIMP_TAC [POLY_EXTEND, RING_MUL_RZERO, RING_ADD_LZERO] THEN
    ASM_SIMP_TAC [POLY_EXTEND_UNIVARIATE, ← GSYM RING_POLYNOMIAL] THEN
    REWRITE_TAC [coeff] THEN
    MATCH_MP_TAC RING_SPAN_SUM THEN REWRITE_TAC [IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ring_homomorphism, SUBSET, FORALL_IN_IMAGE]) THEN
    ASM_CASES_TAC (← q r"(r:(1->num)->A) (\v. i) = ring_0 k") THEN
    ASM_SIMP_TAC [RING_MUL_LZERO, RING_SPAN_0, RING_POW] THEN
    MATCH_MP_TAC RING_SPAN_MUL THEN ASM_REWRITE_TAC [] THEN
    REPEAT (CONJ_TAC THENL
     [ASM_MESON_TAC [POLY_MONOMIAL_IN_CARRIER, RING_POLYNOMIAL], ALL_TAC]) THEN
    MATCH_MP_TAC RING_SPAN_INC THEN ASM_SIMP_TAC [RING_POW] THEN
    MATCH_MP_TAC s1 THEN
    POP_ASSUM MP_TAC THEN
    FIRST_X_ASSUM (DISJ_CASES_THEN2 MP_TAC SUBST1_TAC) THEN
    REWRITE_TAC [POLY_RING, POLY_0] THEN ASM_ARITH_TAC))

  -- @@RETURN BEGIN
  return { ALGEBRAIC_OVER_NONMONOMORPHISM, ALGEBRAIC_EXTENSION, ALGEBRAIC_EXTENSION_ALT,
           ALGEBRAIC_OVER_EQ, ALGEBRAIC_OVER_EQ_EQ, ALGEBRAIC_EXTENSION_EQ,
           FINITE_IMP_ALGEBRAIC_EXTENSION_EXPLICIT, FINITE_IMP_ALGEBRAIC_EXTENSION,
           RING_SIMPLE_EXTENSION_SPAN, RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Simple algebraic extensions are fields and finite; algebraicity under     -/
/- monomorphic/isomorphic images, range, towers, and finite generation.      -/
/- (fieldtheory.ml 3039-3284)                                                -/
/- ------------------------------------------------------------------------- -/

structure AlgebraicExtensionProps where
  -- @@FIELDS
  FIELD_SIMPLE_ALGEBRAIC_EXTENSION_GEN : thm
  FIELD_SIMPLE_ALGEBRAIC_EXTENSION_EQ : thm
  FIELD_SIMPLE_ALGEBRAIC_EXTENSION : thm
  FINITE_SIMPLE_ALGEBRAIC_EXTENSION : thm
  ALGEBRAIC_OVER_FROM_MONOMORPHIC_IMAGE : thm
  ALGEBRAIC_OVER_ISOMORPHIC_IMAGE : thm
  ALGEBRAIC_OVER_RANGE : thm
  ALGEBRAIC_OVER_FIELD_EXTENSION : thm
  FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION : thm
  FINITE_EQ_FINITELY_GENERATED_ALGEBRAIC_EXTENSION : thm
  deriving Inhabited

@[nospecialize]
def setupAlgebraicExtensionProps [HolBase] (D : FieldTheoryDeps) (BSubfieldGenerated : SubfieldGenerated) (BFieldExtension : FieldExtension) (BFiniteExtension : FiniteExtension) (BAlgebraicExtension : AlgebraicExtension) (BAlgebraicOverBasics : AlgebraicOverBasics) :
    ExceptT String IO AlgebraicExtensionProps := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, TAUT, .. } := D
  let { CONJ_ASSOC, CONTRAPOS_THM, EMPTY_SUBSET, EQ_IMP, EQ_SYM_EQ, .. } := D.core1
  let { FIELD_IMP_INTEGRAL_DOMAIN, FIELD_POLY_RING, FIELD_QUOTIENT_RING, FINITE_IMAGE,
        FINITE_INDUCT_STRONG, FINITE_NUMSEG_LT, FIRST_RING_ISOMORPHISM_THEOREM,
        FORALL_IN_GSPEC, FORALL_IN_INSERT, IMAGE_I, IMAGE_POLY_EXTEND_1, .. } := D.core2
  let { IMP_CONJ, IMP_IMP, INSERT_SUBSET, INTEGRAL_DOMAIN_MUL_EQ_0,
        INTEGRAL_DOMAIN_NONTRIVIAL, IN_ELIM_THM, IN_INSERT,
        IN_RING_POLYNOMIAL_CARRIER_COMPOSE, IN_UNIV, ISOMORPHIC_RING_FIELDNESS, I_DEF,
        I_O_ID, .. } := D.core3
  let { NOT_IN_EMPTY, PID_MAXIMAL_EQ_PRIME_IDEAL, PID_POLY_RING,
        POLY_EQ_0_MONOMORPHIC_IMAGE, .. } := D.core4
  let { POLY_EXTEND, POLY_EXTEND_1, POLY_EXTEND_EVALUATE,
        POLY_EXTEND_INTO_SUBRING_GENERATED, POLY_EXTEND_MUL, POLY_RING, PSUBSET_ALT,
        RIGHT_FORALL_IMP_THM, .. } := D.core5
  let { RING_HOMOMORPHISM_COMPOSE, RING_HOMOMORPHISM_INCLUSION,
        RING_HOMOMORPHISM_POLY_EXTEND, RING_IDEAL_RING_KERNEL,
        RING_ISOMORPHISMS_ISOMORPHISM, RING_ISOMORPHISM_IMP_HOMOMORPHISM,
        RING_ISOMORPHISM_IMP_ISOMORPHIC, RING_ISOMORPHISM_IMP_MONOMORPHISM,
        RING_ISOMORPHISM_ONTO_IMAGE, RING_MONOMORPHISM_FROM_SUBRING_GENERATED,
        RING_MONOMORPHISM_I, RING_MONOMORPHISM_IMP_HOMOMORPHISM,
        RING_MONOMORPHISM_INTO_SUBRING, .. } := D.core6
  let { RING_POLYNOMIAL, RING_POLYNOMIAL_1, RING_POW_IN_SUBRING_GENERATED,
        RING_POW_SUBRING_GENERATED, SIMPLE_IMAGE_GEN, SUBRING_GENERATED,
        SUBRING_GENERATED_BY_SUBRING_GENERATED, .. } := D.core7
  let { SUBRING_GENERATED_IDEMPOT, SUBRING_GENERATED_INC,
        SUBRING_GENERATED_UNION_RIGHT, SUBSET, SUBSET_REFL, SUBSET_RESTRICT,
        SUBSET_UNIV, UNION_EMPTY, UNIV_NOT_EMPTY, .. } := D.core8
  let { o_ASSOC, o_DEF, o_THM, prime_ideal, proper_ideal, ring_homomorphism,
        ring_image, ring_isomorphism, ring_kernel, .. } := D.core9
  let { SUBRING_EQ_SUBFIELD_GENERATED, .. } := BSubfieldGenerated
  let { field_extension, .. } := BFieldExtension
  let { FINITE_EXTENSION_ISOMORPHISM, FINITE_EXTENSION_TRANS,
        FINITE_IMP_FINITELY_GENERATED_EXTENSION, finite_extension,
        finitely_generated_extension, .. } := BFiniteExtension
  let { ALGEBRAIC_OVER_IN_CARRIER, algebraic_extension, algebraic_over, .. } := BAlgebraicExtension
  let { ALGEBRAIC_OVER_EQ, ALGEBRAIC_OVER_EQ_EQ, ALGEBRAIC_OVER_NONMONOMORPHISM,
        FINITE_IMP_ALGEBRAIC_EXTENSION, RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN, .. } := BAlgebraicOverBasics
  -- @@SCOPE END

  let FIELD_SIMPLE_ALGEBRAIC_EXTENSION_GEN ← prove
   r"!(h:A->B) k l a.
        field k /\ integral_domain l /\
        ring_homomorphism(k,l) h /\
        algebraic_over (k,l) h a
        ==> field(subring_generated l (a INSERT IMAGE h (ring_carrier k)))"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP ALGEBRAIC_OVER_IN_CARRIER) THEN
    MP_TAC (← ISPECL
     [← q "poly_ring (k:A ring) (:1)", ← q "l:B ring",
      ← q r"poly_extend (k,l) (h:A->B) (\x:1. a)"]
     FIRST_RING_ISOMORPHISM_THEOREM) THEN
    REWRITE_TAC [ring_image] THEN
    ASM_SIMP_TAC [IMAGE_POLY_EXTEND_1, RING_HOMOMORPHISM_POLY_EXTEND] THEN
    REWRITE_TAC [SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
    DISCH_THEN (SUBST1_TAC o SYM o MATCH_MP ISOMORPHIC_RING_FIELDNESS) THEN
    ASM_SIMP_TAC [FIELD_QUOTIENT_RING, RING_IDEAL_RING_KERNEL,
                 RING_HOMOMORPHISM_POLY_EXTEND] THEN
    wPart (fun t => .ok t)
      (fun t => do lhand (← rand t)) PID_MAXIMAL_EQ_PRIME_IDEAL THEN
    ASM_SIMP_TAC [PID_POLY_RING, prime_ideal, proper_ideal,
                RING_IDEAL_RING_KERNEL, RING_HOMOMORPHISM_POLY_EXTEND] THEN
    REWRITE_TAC [ring_kernel] THEN ANTS_TAC THENL
     [RULE_ASSUM_TAC (REWRITE_RULE [algebraic_over]) THEN ASM SET_TAC [],
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [IN_ELIM_THM]] THEN
    SIMP_TAC [PSUBSET_ALT, SUBSET_RESTRICT, IN_ELIM_THM] THEN CONJ_TAC THENL
     [EXISTS_TAC (← q "poly_1 k:(1->num)->A") THEN
      ASM_SIMP_TAC [POLY_EXTEND_1, RING_HOMOMORPHISM_POLY_EXTEND] THEN
      ASM_SIMP_TAC [INTEGRAL_DOMAIN_NONTRIVIAL, ← GSYM RING_POLYNOMIAL,
                   RING_POLYNOMIAL_1],
      MAP_EVERY X_GEN_TAC [← q "p:(1->num)->A", ← q "q:(1->num)->A"] THEN
      REWRITE_TAC [POLY_RING, IN_ELIM_THM, SUBSET_UNIV] THEN
      ASM_SIMP_TAC [POLY_EXTEND_MUL, RING_HOMOMORPHISM_POLY_EXTEND,
                   IN_UNIV, IMP_CONJ, INTEGRAL_DOMAIN_MUL_EQ_0, POLY_EXTEND]])

  let FIELD_SIMPLE_ALGEBRAIC_EXTENSION_EQ ← prove
   r"!(h:A->B) k l a.
        field k /\ integral_domain l /\
        ring_homomorphism(k,l) h /\ a IN ring_carrier l
        ==> (field(subring_generated l (a INSERT IMAGE h (ring_carrier k))) <=>
             algebraic_over (k,l) h a)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN
    ASM_SIMP_TAC [FIELD_SIMPLE_ALGEBRAIC_EXTENSION_GEN] THEN
    GEN_REWRITE_TAC id [← GSYM CONTRAPOS_THM] THEN
    ASM_SIMP_TAC [ALGEBRAIC_OVER_NONMONOMORPHISM] THEN
    REWRITE_TAC [← GSYM RING_ISOMORPHISM_ONTO_IMAGE, ring_image] THEN
    ASM_SIMP_TAC [IMAGE_POLY_EXTEND_1] THEN
    REWRITE_TAC [SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
    DISCH_THEN (MP_TAC o MATCH_MP RING_ISOMORPHISM_IMP_ISOMORPHIC) THEN
    DISCH_THEN (MP_TAC o MATCH_MP ISOMORPHIC_RING_FIELDNESS) THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [FIELD_POLY_RING] THEN
    REWRITE_TAC [UNIV_NOT_EMPTY])

  let FIELD_SIMPLE_ALGEBRAIC_EXTENSION ← prove
   r"!(h:A->B) k l a.
        field_extension (k,l) h /\
        algebraic_over (k,l) h a
        ==> field(subring_generated l (a INSERT IMAGE h (ring_carrier k)))"
   (REWRITE_TAC [field_extension] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC FIELD_SIMPLE_ALGEBRAIC_EXTENSION_GEN THEN
    ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM,
                 FIELD_IMP_INTEGRAL_DOMAIN])

  let FINITE_SIMPLE_ALGEBRAIC_EXTENSION ← prove
   r"!(h:A->B) k l a.
        field_extension(k,l) h /\
        algebraic_over(k,l) h a
        ==> finite_extension
             (k,subring_generated l (a INSERT IMAGE h (ring_carrier k))) h"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP ALGEBRAIC_OVER_IN_CARRIER) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE id [field_extension]) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    ASM_SIMP_TAC [finite_extension, field_extension,
                 FIELD_SIMPLE_ALGEBRAIC_EXTENSION] THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN (← q "p:(1->num)->A") STRIP_ASSUME_TAC o
       CONJUNCT2 o GEN_REWRITE_RULE id [algebraic_over]) THEN
    MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_MONOMORPHISM_INTO_SUBRING THEN ASM SET_TAC [],
      DISCH_TAC] THEN
    EXISTS_TAC (← q "{ring_pow l (a:B) n | n < poly_deg k (p:(1->num)->A)}") THEN
    REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
      SIMP_TAC [FINITE_IMAGE, FINITE_NUMSEG_LT],
      REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC RING_POW_IN_SUBRING_GENERATED THEN
      MATCH_MP_TAC SUBRING_GENERATED_INC THEN
      ASM_REWRITE_TAC [IN_INSERT, INSERT_SUBSET] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [ring_homomorphism]) THEN ASM SET_TAC [],
      ALL_TAC] THEN
    MP_TAC (← ISPECL
       [← q "h:A->B", ← q "k:A ring",
        ← q r"subring_generated l (a INSERT IMAGE (h:A->B) (ring_carrier k))",
        ← q "p:(1->num)->A", ← q "a:B"]
       RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN) THEN
    SIMP_TAC [SUBRING_GENERATED_IDEMPOT, SUBSET_REFL] THEN
    REWRITE_TAC [RING_POW_SUBRING_GENERATED] THEN
    GEN_REWRITE_TAC RAND_CONV [EQ_SYM_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBRING_GENERATED_INC THEN
      ASM_REWRITE_TAC [IN_INSERT, INSERT_SUBSET] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [ring_homomorphism]) THEN ASM SET_TAC [],
      REWRITE_TAC [SUBRING_GENERATED]] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (GEN_REWRITE_TAC RAND_CONV [← SYM th])) THEN
    MATCH_MP_TAC POLY_EXTEND_INTO_SUBRING_GENERATED THEN EXISTS_TAC (← q "(:1)") THEN
    ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBRING_GENERATED_INC THEN
    ASM_REWRITE_TAC [IN_INSERT, INSERT_SUBSET] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ring_homomorphism]) THEN ASM SET_TAC [])

  let ALGEBRAIC_OVER_FROM_MONOMORPHIC_IMAGE ← prove
   r"!(f:A->B) (g:B->C) k l m z.
        ring_monomorphism (k,l) f /\ ring_homomorphism (l,m) g /\
        algebraic_over (k,m) (g o f) z
        ==> algebraic_over (l,m) g z"
   (REPEAT GEN_TAC THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    REWRITE_TAC [algebraic_over] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN (← q "p:(1->num)->A") STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC [] THEN
    EXISTS_TAC (← q "(f:A->B) o (p:(1->num)->A)") THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
      EXISTS_TAC (← q "k:A ring") THEN ASM_REWRITE_TAC [],
      FIRST_ASSUM (MP_TAC o ISPEC (← q "p:(1->num)->A") o
          MATCH_MP (← REWRITE_RULE [IMP_CONJ] POLY_EQ_0_MONOMORPHIC_IMAGE)) THEN
      ASM_MESON_TAC [POLY_RING, RING_POLYNOMIAL],
      MP_TAC (← ISPECL
       [← q "k:A ring", ← q "l:B ring", ← q "m:C ring", ← q "f:A->B", ← q "g:B->C"]
       RING_HOMOMORPHISM_COMPOSE) THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
      UNDISCH_TAC
         (← q r"poly_extend (k,m) ((g:B->C) o (f:A->B)) (\v:1. z) p = ring_0 m") THEN
      ASM_SIMP_TAC [POLY_EXTEND_EVALUATE, o_ASSOC]])

  let ALGEBRAIC_OVER_ISOMORPHIC_IMAGE ← prove
   r"!(f:A->B) (g:B->C) k l m z.
        ring_isomorphism (k,l) f /\ ring_homomorphism (l,m) g
        ==> (algebraic_over (k,m) (g o f) z <=> algebraic_over (l,m) g z)"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [ASM_MESON_TAC [ALGEBRAIC_OVER_FROM_MONOMORPHIC_IMAGE,
                    RING_ISOMORPHISM_IMP_MONOMORPHISM],
      DISCH_TAC] THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN (← q "f':B->A") STRIP_ASSUME_TAC o
      GEN_REWRITE_RULE id [ring_isomorphism]) THEN
    MATCH_MP_TAC
     (← HolLight.INST_TYPE [(← qty "B", ← qty "A"), (← qty "Y", ← qty "B"),
                   (← qty "Z", ← qty "C")]
           ALGEBRAIC_OVER_FROM_MONOMORPHIC_IMAGE) THEN
    MAP_EVERY EXISTS_TAC [← q "f':B->A", ← q "l:B ring"] THEN
    REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL
     [ALL_TAC, MATCH_MP_TAC ALGEBRAIC_OVER_EQ THEN EXISTS_TAC (← q "g:B->C")] THEN
    ASM_MESON_TAC [o_THM, ALGEBRAIC_OVER_EQ, RING_ISOMORPHISMS_ISOMORPHISM,
                  RING_ISOMORPHISM_IMP_MONOMORPHISM, RING_HOMOMORPHISM_COMPOSE,
                  RING_ISOMORPHISM_IMP_HOMOMORPHISM])

  let ALGEBRAIC_OVER_RANGE ← prove
   r"!(h:A->B) k l x.
        ring_monomorphism(k,l) h
        ==> (algebraic_over (k,l) h x <=>
             algebraic_over
               (subring_generated l (IMAGE h (ring_carrier k)),l) I x)"
   (REPEAT STRIP_TAC THEN FIRST_ASSUM
     (MP_TAC o GEN_REWRITE_RULE id [← GSYM RING_ISOMORPHISM_ONTO_IMAGE]) THEN
    ASM_REWRITE_TAC [ring_image, ring_isomorphism] THEN
    REWRITE_TAC [RING_ISOMORPHISMS_ISOMORPHISM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "h':B->A") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL
     [← q "h':B->A", ← q "h:A->B",
       ← q "subring_generated l (IMAGE (h:A->B) (ring_carrier k))",
       ← q "k:A ring", ← q "l:B ring", ← q "x:B"]
     ALGEBRAIC_OVER_ISOMORPHIC_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM],
      DISCH_THEN (SUBST1_TAC o SYM)] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC ALGEBRAIC_OVER_EQ_EQ THEN
    REWRITE_TAC [o_DEF, I_DEF, RING_HOMOMORPHISM_INCLUSION] THEN
    ASM_MESON_TAC [])

  let ALGEBRAIC_OVER_FIELD_EXTENSION ← prove
   r"!(f:A->B) (g:B->C) k l m z.
        field_extension (k,l) f /\ field_extension (l,m) g /\
        algebraic_over (k,m) (g o f) z
        ==> algebraic_over (l,m) g z"
   (REWRITE_TAC [field_extension] THEN
    MESON_TAC [ALGEBRAIC_OVER_FROM_MONOMORPHIC_IMAGE,
              RING_MONOMORPHISM_IMP_HOMOMORPHISM])

  let FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION ← prove
   r"!(h:A->B) k l b.
        field_extension(k,l) h /\
        FINITE b /\
        (!x. x IN b ==> algebraic_over(k,l) h x)
        ==> finite_extension
             (k,subring_generated l (IMAGE h (ring_carrier k) UNION b)) h"
   (← do
    let setC ← SET_RULE (← q r"x INSERT s = {x} UNION s")
    let tauB ← TAUT (← q r"p /\ q /\ r ==> s <=> p /\ r ==> q ==> s")
    let tauA ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    pure (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [EMPTY_SUBSET, INSERT_SUBSET, UNION_EMPTY, NOT_IN_EMPTY] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_EXTENSION_ISOMORPHISM THEN
      ASM_MESON_TAC [field_extension, RING_ISOMORPHISM_ONTO_IMAGE, ring_image],
      REWRITE_TAC [FORALL_IN_INSERT]] THEN
    MAP_EVERY X_GEN_TAC [← q "y:B", ← q "b:B->bool"] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (STRIP_TAC THEN MP_TAC th THEN ASM_REWRITE_TAC [])) THEN
    STRIP_TAC THEN
    MP_TAC (← ISPECL [← q "I:B->B",
      ← q "subring_generated l (IMAGE (h:A->B) (ring_carrier k) UNION b)",
      ← q "l:B ring",
      ← q "y:B"]
      FINITE_SIMPLE_ALGEBRAIC_EXTENSION) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [MATCH_MP_TAC tauA THEN CONJ_TAC THENL
       [RULE_ASSUM_TAC (REWRITE_RULE [finite_extension, field_extension]) THEN
        ASM_REWRITE_TAC [field_extension] THEN
        MATCH_MP_TAC RING_MONOMORPHISM_FROM_SUBRING_GENERATED THEN
        REWRITE_TAC [RING_MONOMORPHISM_I],
        MATCH_MP_TAC (← REWRITE_RULE [tauB] ALGEBRAIC_OVER_FIELD_EXTENSION) THEN
        ASM_MESON_TAC [I_O_ID, finite_extension]],
      UNDISCH_TAC
       (← q r"finite_extension
         (k,subring_generated l (IMAGE h (ring_carrier k) UNION b))
         (h:A->B)") THEN
      REWRITE_TAC [IMP_IMP] THEN
      DISCH_THEN (MP_TAC o MATCH_MP FINITE_EXTENSION_TRANS) THEN
      REWRITE_TAC [I_O_ID, IMAGE_I] THEN MATCH_MP_TAC EQ_IMP THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      ONCE_REWRITE_TAC [setC] THEN
      REWRITE_TAC [SUBRING_GENERATED_UNION_RIGHT] THEN
      AP_TERM_TAC THEN SET_TAC []]))

  let FINITE_EQ_FINITELY_GENERATED_ALGEBRAIC_EXTENSION ← prove
   r"!(h:A->B) k l.
        finite_extension (k,l) h <=>
        finitely_generated_extension (k,l) h /\
        algebraic_extension (k,l) h"
   (REPEAT GEN_TAC THEN EQ_TAC THEN
    SIMP_TAC [FINITE_IMP_ALGEBRAIC_EXTENSION,
             FINITE_IMP_FINITELY_GENERATED_EXTENSION] THEN
    REWRITE_TAC [algebraic_extension] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    REWRITE_TAC [finitely_generated_extension] THEN
    ASM_MESON_TAC [FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION, SUBSET,
      SUBRING_EQ_SUBFIELD_GENERATED, finite_extension, field_extension])

  -- @@RETURN BEGIN
  return { FIELD_SIMPLE_ALGEBRAIC_EXTENSION_GEN, FIELD_SIMPLE_ALGEBRAIC_EXTENSION_EQ,
           FIELD_SIMPLE_ALGEBRAIC_EXTENSION, FINITE_SIMPLE_ALGEBRAIC_EXTENSION,
           ALGEBRAIC_OVER_FROM_MONOMORPHIC_IMAGE, ALGEBRAIC_OVER_ISOMORPHIC_IMAGE,
           ALGEBRAIC_OVER_RANGE, ALGEBRAIC_OVER_FIELD_EXTENSION,
           FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION,
           FINITE_EQ_FINITELY_GENERATED_ALGEBRAIC_EXTENSION }
  -- @@RETURN END

/- ======== END TRANSLATION ======== -/

/-- `W(MP_TAC o PART_MATCH f th o snd)`: match `th`'s part `f` against the
    whole goal, and MP_TAC the instance. -/
def wPartWhole [HolBase] (f : term → Except String term) (th : thm) : tactic := fun gl =>
  ExceptT.run do
    ExceptT.mk (MP_TAC (← PART_MATCH f th gl.2) gl)

/- ------------------------------------------------------------------------- -/
/- Algebraic over a subring; transitivity, isomorphism, cardinality and      -/
/- automorphism results for algebraic extensions.  (fieldtheory.ml 3285-3410)-/
/- ------------------------------------------------------------------------- -/

structure AlgebraicExtMisc where
  -- @@FIELDS
  ALGEBRAIC_FROM_SUBRING_GENERATED : thm
  ALGEBRAIC_EXTENSION_ISOMORPHISM : thm
  ALGEBRAIC_EXTENSION_REFL : thm
  ALGEBRAIC_EXTENSION_TRANS : thm
  ALGEBRAIC_EXTENSION_TRANS_EQ : thm
  CARD_LE_ALGEBRAIC_EXTENSION : thm
  CARD_EQ_ALGEBRAIC_EXTENSION : thm
  RING_AUTOMORPHISM_OF_ALGEBRAIC_EXTENSION : thm
  RING_AUTOMORPHISM_FROBENIUS_GEN : thm
  deriving Inhabited

@[nospecialize]
def setupAlgebraicExtMisc [HolBase] (D : FieldTheoryDeps) (BSubfieldQuotients : SubfieldQuotients) (BFieldExtension : FieldExtension) (BFiniteExtension : FiniteExtension) (BAlgebraicExtension : AlgebraicExtension) (BAlgebraicOverBasics : AlgebraicOverBasics) (BAlgebraicExtensionProps : AlgebraicExtensionProps) :
    ExceptT String IO AlgebraicExtMisc := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_TAC, TAUT, .. } := D
  let { CARD_EQ_IMP_LE, CARD_EQ_POLY_RING_FINITE, CARD_LE_ANTISYM,
        CARD_LE_FINITE_INFINITE, CARD_LE_IMAGE, CARD_LE_REFL, CARD_LE_SUBSET,
        CARD_LE_TRANS, CARD_LE_UNIONS, CARD_MUL2_ABSORB_LE, CONTRAPOS_THM,
        DE_MORGAN_THM, .. } := D.core1
  let { FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING, FINITE_1, FINITE_IMAGE,
        FINITE_NUMSEG_LE, FORALL_FUN_FROM_1, FORALL_IN_GSPEC, FORALL_IN_IMAGE,
        FUN_EQ_THM, IMAGE_SUBSET, .. } := D.core2
  let { IMP_CONJ, IMP_CONJ_ALT, INFINITE_CARD_LE, INSERT_SUBSET, IN_ELIM_THM,
        IN_INSERT, IN_INTER, IN_RING_POLYNOMIAL_CARRIER_COMPOSE, I_THM,
        LEFT_IMP_EXISTS_THM, LE_REFL, .. } := D.core3
  let { MONOMIAL_DEG_UNIVARIATE, MONO_EXISTS, NOT_EXISTS_THM, POLY_0, POLY_CLAUSES,
        POLY_DEG_GE_EQ, POLY_EQ_0_MONOMORPHIC_IMAGE, POLY_EVAL,
        POLY_EVAL_HOMOMORPHIC_IMAGE, .. } := D.core4
  let { POLY_EXTEND_EQ, POLY_EXTEND_EVALUATE, POLY_EXTEND_FROM_SUBRING_GENERATED,
        POLY_EXTEND_HOMOMORPHIC_IMAGE, POLY_EXTEND_INTO_SUBRING_GENERATED,
        POLY_MONOMIAL_IN_CARRIER, POLY_RING, POLY_ROOT_BOUND,
        POLY_SUBRING_GENERATED_CLAUSES, RIGHT_AND_FORALL_THM,
        RING_0_IN_SUBRING_GENERATED, RING_CARRIER_POLY_SUBRING_GENERATED,
        RING_CARRIER_SUBRING_GENERATED_SUBSET, .. } := D.core5
  let { RING_ISOMORPHISM_I, RING_ISOMORPHISM_MONOMORPHISM_ALT, RING_MONOMORPHISM_ALT,
        RING_MONOMORPHISM_ALT_EQ, RING_MONOMORPHISM_EQ_0, RING_MONOMORPHISM_FROBENIUS,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MONOMORPHISM_POLY_RINGS, .. } := D.core6
  let { RING_POLYNOMIAL, SIMPLE_IMAGE_GEN, SUBRING_GENERATED,
        SUBRING_GENERATED_BY_SUBRING_GENERATED, .. } := D.core7
  let { SUBRING_GENERATED_INC, SUBRING_SUBRING_GENERATED, SUBSET, SUBSET_RESTRICT,
        SUBSET_TRANS, SURJECTIVE_IFF_INJECTIVE, UNION_SUBSET, UNIV_NOT_EMPTY, le_c, .. } := D.core8
  let { o_ASSOC, o_DEF, o_THM, poly_eval, ring_automorphism, ring_homomorphism,
        ring_monomorphism, ring_polynomial, ring_powerseries, .. } := D.core9
  let { FROBENIUS_FIXED_FIELD, .. } := BSubfieldQuotients
  let { FIELD_EXTENSION_FROM_SUBRING_GENERATED, FIELD_EXTENSION_IMP_HOMOMORPHISM,
        FIELD_EXTENSION_IMP_MONOMORPHISM, FIELD_EXTENSION_IMP_SUBSET,
        FIELD_EXTENSION_TRANS, field_extension, .. } := BFieldExtension
  let { FINITE_EXTENSION_ISOMORPHISM, FINITE_EXTENSION_TRANS, finite_extension, .. } := BFiniteExtension
  let { ALGEBRAIC_IMP_FIELD_EXTENSION, algebraic_extension, algebraic_over, .. } := BAlgebraicExtension
  let { ALGEBRAIC_EXTENSION, ALGEBRAIC_EXTENSION_ALT, FINITE_IMP_ALGEBRAIC_EXTENSION, .. } := BAlgebraicOverBasics
  let { FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION,
        FINITE_SIMPLE_ALGEBRAIC_EXTENSION, .. } := BAlgebraicExtensionProps
  -- @@SCOPE END

  let ALGEBRAIC_FROM_SUBRING_GENERATED ← prove
   r"!(h:A->B) k l s x.
        field_extension (k,subring_generated l s) h /\
        algebraic_over(k,subring_generated l s) h x
        ==> algebraic_over(k,l) h x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [algebraic_over] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP (← REWRITE_RULE [SUBSET]
          RING_CARRIER_SUBRING_GENERATED_SUBSET)) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"p:(1->num)->A") THEN
    REWRITE_TAC [SUBRING_GENERATED] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [← SYM th])) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC POLY_EXTEND_INTO_SUBRING_GENERATED THEN
    ASM_MESON_TAC [FIELD_EXTENSION_IMP_HOMOMORPHISM])

  let ALGEBRAIC_EXTENSION_ISOMORPHISM ← prove
   r"!(f:A->B) k l.
        (field k \/ field l) /\ ring_isomorphism (k,l) f
        ==> algebraic_extension (k,l) f"
   (MESON_TAC [FINITE_EXTENSION_ISOMORPHISM, FINITE_IMP_ALGEBRAIC_EXTENSION])

  let ALGEBRAIC_EXTENSION_REFL ← prove
   r"!k:A ring. algebraic_extension (k,k) I <=> field k"
   (MESON_TAC [ALGEBRAIC_EXTENSION, field_extension,
              ALGEBRAIC_EXTENSION_ISOMORPHISM, RING_ISOMORPHISM_I])

  let ALGEBRAIC_EXTENSION_TRANS ← prove
   r"!(f:A->B) (g:B->C) k l m.
        algebraic_extension (k,l) f /\ algebraic_extension (l,m) g
        ==> algebraic_extension (k,m) (g o f)"
   (← do
    let a4 ← TAUT (← q r"p \/ ~q <=> q ==> p")
    let a3 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    let a2 ← TAUT
      (← q r"(p /\ r ==> s) /\ q ==> (p /\ (q ==> r) ==> s)")
    let a1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [algebraic_extension] THEN STRIP_TAC THEN
    MATCH_MP_TAC a1 THEN CONJ_TAC THENL
     [ASM_MESON_TAC [FIELD_EXTENSION_TRANS], DISCH_TAC] THEN
    X_GEN_TAC (← q r"z:C") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [algebraic_over] o SPEC (← q r"z:C")) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"p:(1->num)->B") THEN STRIP_TAC THEN MP_TAC (← ISPECL
     [← q r"f:A->B", ← q r"g:B->C", ← q r"k:A ring",
      ← q r"subring_generated l
        (IMAGE (f:A->B) (ring_carrier k) UNION
         {p(\i:1. n) |n| n <= poly_deg l p})",
      ← q r"subring_generated m (z INSERT IMAGE (g:B->C)
       (ring_carrier(subring_generated l
        (IMAGE (f:A->B) (ring_carrier k) UNION
         {p(\i:1. n) |n| n <= poly_deg l p}))))"]
      FINITE_EXTENSION_TRANS) THEN
    ANTS_TAC THENL
     [ALL_TAC,
      DISCH_THEN (MP_TAC o MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION) THEN
      REWRITE_TAC [algebraic_extension, RIGHT_AND_FORALL_THM] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"z:C")) THEN MATCH_MP_TAC a2 THEN
      REWRITE_TAC [ALGEBRAIC_FROM_SUBRING_GENERATED] THEN
      MATCH_MP_TAC SUBRING_GENERATED_INC THEN
      ASM_REWRITE_TAC [INSERT_SUBSET, IN_INSERT] THEN
      TRANS_TAC SUBSET_TRANS (← q r"IMAGE (g:B->C) (ring_carrier l)") THEN
      SIMP_TAC [IMAGE_SUBSET, RING_CARRIER_SUBRING_GENERATED_SUBSET] THEN
      RULE_ASSUM_TAC (REWRITE_RULE
       [field_extension, ring_monomorphism, ring_homomorphism]) THEN
      ASM SET_TAC []] THEN
    MATCH_MP_TAC a3 THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION THEN
      ASM_REWRITE_TAC [FORALL_IN_GSPEC] THEN
      ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
      SIMP_TAC [FINITE_IMAGE, FINITE_NUMSEG_LE] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC [POLY_MONOMIAL_IN_CARRIER],
      DISCH_TAC] THEN
    MATCH_MP_TAC FINITE_SIMPLE_ALGEBRAIC_EXTENSION THEN CONJ_TAC THENL
     [ASM_MESON_TAC [FIELD_EXTENSION_FROM_SUBRING_GENERATED,
                    finite_extension, field_extension],
      ASM_REWRITE_TAC [algebraic_over]] THEN
    EXISTS_TAC (← q r"p:(1->num)->B") THEN
    ASM_REWRITE_TAC [POLY_EXTEND_FROM_SUBRING_GENERATED] THEN
    ASM_REWRITE_TAC [POLY_SUBRING_GENERATED_CLAUSES] THEN
    ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
    ASM_SIMP_TAC [RING_CARRIER_POLY_SUBRING_GENERATED, IN_ELIM_THM,
                 SUBRING_SUBRING_GENERATED, IN_INTER] THEN
    REWRITE_TAC [FORALL_FUN_FROM_1] THEN X_GEN_TAC (← q r"m:num") THEN
    ASM_CASES_TAC (← q r"m:num <= poly_deg l (p:(1->num)->B)") THENL
     [MATCH_MP_TAC SUBRING_GENERATED_INC THEN
      CONJ_TAC THENL [REWRITE_TAC [UNION_SUBSET], ASM SET_TAC []] THEN
      REWRITE_TAC [SUBSET, FORALL_IN_GSPEC, FORALL_IN_IMAGE] THEN
      CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [POLY_MONOMIAL_IN_CARRIER]] THEN
      RULE_ASSUM_TAC (REWRITE_RULE
       [field_extension, ring_monomorphism, ring_homomorphism]) THEN
      ASM SET_TAC [],
      POP_ASSUM MP_TAC THEN
      ASM_SIMP_TAC [POLY_DEG_GE_EQ, RING_POLYNOMIAL] THEN
      SIMP_TAC [DE_MORGAN_THM, NOT_EXISTS_THM, a4] THEN
      SIMP_TAC [MONOMIAL_DEG_UNIVARIATE, LE_REFL, RING_0_IN_SUBRING_GENERATED]]))

  let ALGEBRAIC_EXTENSION_TRANS_EQ ← prove
   r"!(f:A->B) (g:B->C) k l m.
        field_extension (k,l) f /\ field_extension (l,m) g
        ==> (algebraic_extension (k,m) (g o f) <=>
             algebraic_extension (k,l) f /\
             algebraic_extension (l,m) g)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN
    REWRITE_TAC [ALGEBRAIC_EXTENSION_TRANS] THEN
    ASM_REWRITE_TAC [ALGEBRAIC_EXTENSION] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (fun th => tactic_of do pure (CONJ_TAC THEN MP_TAC th)) THENL
     [DISCH_TAC THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(g:B->C) y")) THEN ANTS_TAC THENL
       [REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET)) THEN
        ASM SET_TAC [],
        MATCH_MP_TAC MONO_EXISTS] THEN
      X_GEN_TAC (← q r"p:(1->num)->A") THEN
      ASM_SIMP_TAC [POLY_EXTEND_EVALUATE, FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC [← GSYM o_ASSOC, ← GSYM poly_eval] THEN
      MP_TAC (← ISPECL [← q r"l:B ring", ← q r"m:C ring", ← q r"y:B", ← q r"g:B->C",
                     ← q r"(f:A->B) o (p:(1->num)->A)"]
          POLY_EVAL_HOMOMORPHIC_IMAGE) THEN
      ASM_SIMP_TAC [FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN ANTS_TAC THENL
       [ASM_MESON_TAC [IN_RING_POLYNOMIAL_CARRIER_COMPOSE,
                      FIELD_EXTENSION_IMP_HOMOMORPHISM],
        DISCH_THEN (fun th => tactic_of do pure (SUBST1_TAC (← SYM th))) THEN
        ASM_MESON_TAC [POLY_EVAL, RING_MONOMORPHISM_ALT,
                      FIELD_EXTENSION_IMP_MONOMORPHISM]],
      DISCH_TAC THEN X_GEN_TAC (← q r"z:C") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"z:C")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"p:(1->num)->A") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"(f:A->B) o (p:(1->num)->A)") THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC [IN_RING_POLYNOMIAL_CARRIER_COMPOSE,
                      FIELD_EXTENSION_IMP_HOMOMORPHISM],
        ASM_MESON_TAC [POLY_EQ_0_MONOMORPHIC_IMAGE, RING_POLYNOMIAL, POLY_CLAUSES,
                      FIELD_EXTENSION_IMP_MONOMORPHISM],
        FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [← SYM th])) THEN
        ASM_SIMP_TAC [POLY_EXTEND_EVALUATE, FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
        REWRITE_TAC [o_ASSOC]]])

  let CARD_LE_ALGEBRAIC_EXTENSION ← prove
   r"!(f:A->B) k l (m:C->bool).
        algebraic_extension (k,l) f /\ INFINITE m /\ ring_carrier k <=_c m
        ==> ring_carrier l <=_c m"
   (← do
    pure (REPEAT STRIP_TAC THEN TRANS_TAC CARD_LE_TRANS
     (← q r"UNIONS { {x | x IN ring_carrier l /\
                    poly_eval l ((f:A->B) o p) x = ring_0 l} |
               p IN ring_carrier (poly_ring k (:1)) /\
               ~(p = ring_0 (poly_ring k (:1)))}") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_LE_SUBSET THEN
      FIRST_ASSUM (MP_TAC o CONJUNCT2 o REWRITE_RULE [ALGEBRAIC_EXTENSION_ALT]) THEN
      SET_TAC [],
      MATCH_MP_TAC CARD_LE_UNIONS] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ALGEBRAIC_EXTENSION, field_extension]) THEN
    ASM_REWRITE_TAC [FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
      wPart (fun c => do lhand c) (fun c => do lhand c) CARD_LE_IMAGE THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_TRANS) THEN
      TRANS_TAC CARD_LE_TRANS (← q r"ring_carrier (poly_ring (k:A ring) (:1))") THEN
      SIMP_TAC [CARD_LE_SUBSET, SUBSET_RESTRICT] THEN
      TRANS_TAC CARD_LE_TRANS (← q r"ring_carrier(k:A ring) *_c (:num)") THEN
      ASM_SIMP_TAC [CARD_MUL2_ABSORB_LE, ← GSYM INFINITE_CARD_LE] THEN
      MATCH_MP_TAC CARD_EQ_IMP_LE THEN MATCH_MP_TAC CARD_EQ_POLY_RING_FINITE THEN
      ASM_REWRITE_TAC [FINITE_1, UNIV_NOT_EMPTY] THEN
      ASM_MESON_TAC [FIELD_IMP_NONTRIVIAL_RING],
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC CARD_LE_FINITE_INFINITE THEN ASM_REWRITE_TAC [] THEN
      wPartWhole (fun c => do lhand (← rand c)) POLY_ROOT_BOUND THEN
      ANTS_TAC THENL [ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN], SIMP_TAC []] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC [IN_RING_POLYNOMIAL_CARRIER_COMPOSE, ring_monomorphism],
        FIRST_X_ASSUM (MP_TAC o check (is_neg o concl))] THEN
      REWRITE_TAC [CONTRAPOS_THM, FUN_EQ_THM, o_THM] THEN
      REWRITE_TAC [POLY_RING, POLY_0] THEN
      RULE_ASSUM_TAC (REWRITE_RULE
       [POLY_RING, ring_polynomial, ring_powerseries, IN_ELIM_THM]) THEN
      ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0]]))

  let CARD_EQ_ALGEBRAIC_EXTENSION ← prove
   r"!(h:A->B) k l.
        algebraic_extension (k,l) h /\ INFINITE(ring_carrier k)
        ==> ring_carrier l =_c ring_carrier k"
   (REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN REPEAT STRIP_TAC THENL
     [MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"ring_carrier k:A->bool"]
          CARD_LE_ALGEBRAIC_EXTENSION) THEN
      ASM_REWRITE_TAC [CARD_LE_REFL],
      FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
      FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_MONOMORPHISM) THEN
      REWRITE_TAC [le_c] THEN EXISTS_TAC (← q r"h:A->B") THEN
      RULE_ASSUM_TAC (REWRITE_RULE [ring_monomorphism, ring_homomorphism]) THEN
      ASM SET_TAC []])

  let RING_AUTOMORPHISM_OF_ALGEBRAIC_EXTENSION ← prove
   r"!(h:A->B) k l f.
        algebraic_extension(k,l) h /\
        ring_monomorphism(l,l) f /\
        (!x. x IN ring_carrier k ==> f(h x) = h x)
        ==> ring_automorphism l f"
   (REWRITE_TAC [algebraic_extension] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [RING_ISOMORPHISM_MONOMORPHISM_ALT, ring_automorphism] THEN
    REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:B")) THEN ASM_REWRITE_TAC [algebraic_over] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"p:(1->num)->A") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    ABBREV_TAC (← q r"s = {x | x IN ring_carrier l /\
                         poly_extend (k,l) (h:A->B) (\v:1. x) p = ring_0 l}") THEN
    MP_TAC (← ISPECL [← q r"s:B->bool", ← q r"f:B->B"] SURJECTIVE_IFF_INJECTIVE) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [← SYM th])) THEN
        ASM_SIMP_TAC [POLY_EXTEND_EVALUATE, RING_MONOMORPHISM_IMP_HOMOMORPHISM,
                     ← GSYM poly_eval] THEN
        wPartWhole (fun c => do lhand (← rand c)) POLY_ROOT_BOUND THEN
        ANTS_TAC THENL [ALL_TAC, MESON_TAC []] THEN
        MP_TAC (← ISPECL [← q r"k:A ring", ← q r"l:B ring", ← q r"h:A->B", ← q r"(:1)"]
          RING_MONOMORPHISM_POLY_RINGS) THEN
        ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN
        REWRITE_TAC [RING_MONOMORPHISM_ALT_EQ, ring_homomorphism] THEN
        ASM SET_TAC [],
        EXPAND_TAC "s" THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
        X_GEN_TAC (← q r"y:B") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN
        MP_TAC (← ISPECL [← q r"k:A ring", ← q r"l:B ring", ← q r"l:B ring", ← q r"h:A->B",
                       ← q r"(:1)", ← q r"(\v. y):1->B", ← q r"f:B->B", ← q r"p:(1->num)->A"]
          POLY_EXTEND_HOMOMORPHIC_IMAGE) THEN
        ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM, o_DEF] THEN
        ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
        RULE_ASSUM_TAC (REWRITE_RULE [ring_monomorphism, ring_homomorphism]) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
        CONJ_TAC THENL [ASM SET_TAC [], MATCH_MP_TAC POLY_EXTEND_EQ] THEN
        EXISTS_TAC (← q r"(:1)") THEN ASM_SIMP_TAC [] THEN ASM SET_TAC []],
      RULE_ASSUM_TAC (REWRITE_RULE [ring_monomorphism, ring_homomorphism]) THEN
      ASM SET_TAC []])

  let RING_AUTOMORPHISM_FROBENIUS_GEN ← prove
   r"!k:A ring.
        prime(ring_char k) /\
        algebraic_extension(subfield_generated k {ring_0 k},k) I
        ==> ring_automorphism k (\x. ring_pow k x (ring_char k))"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ]
      RING_AUTOMORPHISM_OF_ALGEBRAIC_EXTENSION)) THEN
    FIRST_X_ASSUM (MP_TAC o CONJUNCT1 o REWRITE_RULE [algebraic_extension]) THEN
    REWRITE_TAC [field_extension, I_THM] THEN STRIP_TAC THEN
    ASM_SIMP_TAC [RING_MONOMORPHISM_FROBENIUS, FIELD_IMP_INTEGRAL_DOMAIN] THEN
    ASM_SIMP_TAC [← GSYM FROBENIUS_FIXED_FIELD, IN_ELIM_THM])

  -- @@RETURN BEGIN
  return { ALGEBRAIC_FROM_SUBRING_GENERATED, ALGEBRAIC_EXTENSION_ISOMORPHISM,
           ALGEBRAIC_EXTENSION_REFL, ALGEBRAIC_EXTENSION_TRANS,
           ALGEBRAIC_EXTENSION_TRANS_EQ, CARD_LE_ALGEBRAIC_EXTENSION,
           CARD_EQ_ALGEBRAIC_EXTENSION, RING_AUTOMORPHISM_OF_ALGEBRAIC_EXTENSION,
           RING_AUTOMORPHISM_FROBENIUS_GEN }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Algebraic elements form a field etc.  (fieldtheory.ml 3411-3739)          -/
/- ------------------------------------------------------------------------- -/

structure AlgebraicField where
  -- @@FIELDS
  ALGEBRAIC_OVER_0 : thm
  ALGEBRAIC_OVER_1 : thm
  ALGEBRAIC_OVER_NEG : thm
  ALGEBRAIC_OVER_INV : thm
  ALGEBRAIC_OVER_ADD : thm
  ALGEBRAIC_OVER_MUL : thm
  ALGEBRAIC_OVER_SUB : thm
  ALGEBRAIC_OVER_DIV : thm
  ALGEBRAIC_OVER_POW : thm
  SUBRING_OF_ALGEBRAIC_OVER : thm
  SUBFIELD_OF_ALGEBRAIC_OVER : thm
  ALGEBRAIC_OVER_SUBFIELD_GENERATED_ALGEBRAIC : thm
  FIELD_ALGEBRAIC_EXTENSION : thm
  SUBFIELD_OF_ALGEBRAIC_EXTENSION : thm
  FIELD_ALGEBRAIC_OVER : thm
  SUBRING_SUBFIELD_ALGEBRAIC_OVER : thm
  ALGEBRAIC_OVER_TRANS : thm
  ALGEBRAIC_OVER_ALGEBRAIC_EXTENSION : thm
  deriving Inhabited

@[nospecialize]
def setupAlgebraicField [HolBase] (D : FieldTheoryDeps) (BSubfields : Subfields) (BSubfieldGenerated : SubfieldGenerated) (BFieldExtension : FieldExtension) (BAlgebraicExtension : AlgebraicExtension) (BAlgebraicOverBasics : AlgebraicOverBasics) (BAlgebraicExtensionProps : AlgebraicExtensionProps) (BAlgebraicExtMisc : AlgebraicExtMisc) :
    ExceptT String IO AlgebraicField := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, SET_RULE, SET_TAC, TAUT, .. } := D
  let { AND_FORALL_THM, CARRIER_SUBRING_GENERATED_SUBRING, EMPTY_SUBSET, .. } := D.core1
  let { FIELD_IMP_NONTRIVIAL_RING, FINITE_EMPTY, FINITE_INSERT, FORALL_IN_IMAGE,
        FORALL_IN_INSERT, FORALL_IN_UNION, .. } := D.core2
  let { INSERT_SUBSET, IN_ELIM_THM, IN_INSERT, IN_UNION, .. } := D.core3
  let { MONO_AND, MONO_EXISTS, NOT_IN_EMPTY, .. } := D.core4
  let { RIGHT_FORALL_IMP_THM, RING_0, RING_1, RING_ADD, RING_ADD_IN_SUBRING_GENERATED,
        RING_CARRIER_SUBRING_GENERATED_SUBSET, .. } := D.core5
  let { RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_1, RING_INV, RING_MUL, .. } := D.core6
  let { RING_MUL_IN_SUBRING_GENERATED, RING_NEG, RING_NEG_IN_SUBRING_GENERATED,
        SUBRING_GENERATED, SUBRING_GENERATED_BY_SUBRING_GENERATED, .. } := D.core7
  let { SUBRING_GENERATED_INC, SUBRING_GENERATED_INC_GEN, SUBRING_GENERATED_MINIMAL,
        SUBRING_SUBRING_GENERATED, SUBSET, TRIVIAL_RING_10,
        TRIVIAL_RING_SUBRING_GENERATED, UNION_SUBSET, field, .. } := D.core8
  let { ring_div, ring_homomorphism, ring_monomorphism, ring_pow, ring_sub, subring_of, .. } := D.core9
  let { IN_SUBFIELD_INV, SUBFIELD_OF_FIELD_INV, subfield_of, .. } := BSubfields
  let { SUBFIELD_GENERATED_MINIMAL, SUBRING_EQ_SUBFIELD_GENERATED,
        SUBRING_SUBSET_SUBFIELD_GENERATED, .. } := BSubfieldGenerated
  let { FIELD_EXTENSION_IMP_SUBSET, FIELD_EXTENSION_INTO_SUBRING_GENERATED,
        field_extension, .. } := BFieldExtension
  let { ALGEBRAIC_OVER_IMAGE, ALGEBRAIC_OVER_IMAGE_SUBSET, ALGEBRAIC_OVER_IN_CARRIER,
        ALGEBRAIC_OVER_SUBRING_GENERATED, algebraic_extension, algebraic_over, .. } := BAlgebraicExtension
  let { FINITE_IMP_ALGEBRAIC_EXTENSION, .. } := BAlgebraicOverBasics
  let { ALGEBRAIC_OVER_FROM_MONOMORPHIC_IMAGE, FIELD_SIMPLE_ALGEBRAIC_EXTENSION,
        FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION,
        FINITE_SIMPLE_ALGEBRAIC_EXTENSION, .. } := BAlgebraicExtensionProps
  let { ALGEBRAIC_EXTENSION_TRANS, ALGEBRAIC_FROM_SUBRING_GENERATED, .. } := BAlgebraicExtMisc
  -- @@SCOPE END

  let ALGEBRAIC_OVER_0 ← prove
   r"!(h:A->B) k l.
        field_extension (k,l) h ==> algebraic_over(k,l) h (ring_0 l)"
   (MESON_TAC [ALGEBRAIC_OVER_IMAGE, field_extension, ring_monomorphism,
              RING_HOMOMORPHISM_0, RING_0])

  let ALGEBRAIC_OVER_1 ← prove
   r"!(h:A->B) k l.
        field_extension (k,l) h ==> algebraic_over(k,l) h (ring_1 l)"
   (MESON_TAC [ALGEBRAIC_OVER_IMAGE, field_extension, ring_monomorphism,
              RING_HOMOMORPHISM_1, RING_1])

  let (ALGEBRAIC_OVER_NEG, ALGEBRAIC_OVER_INV) ← CONJ_PAIR (← prove
   r"(!(h:A->B) k l a.
        field_extension (k,l) h /\
        algebraic_over (k,l) h a
        ==> algebraic_over (k,l) h (ring_neg l a)) /\
   (!(h:A->B) k l a.
        field_extension (k,l) h /\
        algebraic_over (k,l) h a
        ==> algebraic_over (k,l) h (ring_inv l a))"
   (REWRITE_TAC [AND_FORALL_THM, ← TAUT
     (← q r"(p ==> q) /\ (p ==> r) <=> p ==> q /\ r")] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"a:B"]
       FINITE_SIMPLE_ALGEBRAIC_EXTENSION) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION) THEN
    REWRITE_TAC [algebraic_extension] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ALGEBRAIC_FROM_SUBRING_GENERATED THEN
    EXISTS_TAC (← q r"a INSERT IMAGE (h:A->B) (ring_carrier k)") THEN
    ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
     [MATCH_MP_TAC RING_NEG_IN_SUBRING_GENERATED,
      MATCH_MP_TAC IN_SUBFIELD_INV THEN
      ASM_SIMP_TAC [subfield_of, FIELD_SIMPLE_ALGEBRAIC_EXTENSION,
                   SUBRING_SUBRING_GENERATED,
                   SUBRING_GENERATED_BY_SUBRING_GENERATED]] THEN
    MATCH_MP_TAC SUBRING_GENERATED_INC THEN
    ASM_REWRITE_TAC [UNION_SUBSET, INSERT_SUBSET, EMPTY_SUBSET,
                    IN_UNION, IN_INSERT, NOT_IN_EMPTY] THEN
    RULE_ASSUM_TAC (REWRITE_RULE
     [algebraic_over, field_extension,
      ring_monomorphism, ring_homomorphism]) THEN
    ASM SET_TAC []))

  let (ALGEBRAIC_OVER_ADD, ALGEBRAIC_OVER_MUL) ← CONJ_PAIR (← prove
   r"(!(h:A->B) k l a b.
        field_extension (k,l) h /\
        algebraic_over (k,l) h a /\ algebraic_over (k,l) h b
        ==> algebraic_over (k,l) h (ring_add l a b)) /\
   (!(h:A->B) k l a b.
        field_extension (k,l) h /\
        algebraic_over (k,l) h a /\ algebraic_over (k,l) h b
        ==> algebraic_over (k,l) h (ring_mul l a b))"
   (REWRITE_TAC [AND_FORALL_THM, ← TAUT
     (← q r"(p ==> q) /\ (p ==> r) <=> p ==> q /\ r")] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"{a:B,b}"]
       FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION) THEN
    ASM_REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY] THEN
    ASM_REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
    DISCH_THEN (MP_TAC o MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION) THEN
    REWRITE_TAC [algebraic_extension] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ALGEBRAIC_FROM_SUBRING_GENERATED THEN
    EXISTS_TAC (← q r"IMAGE (h:A->B) (ring_carrier k) UNION {a, b}") THEN
    ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
     [MATCH_MP_TAC RING_ADD_IN_SUBRING_GENERATED,
      MATCH_MP_TAC RING_MUL_IN_SUBRING_GENERATED] THEN
    CONJ_TAC THEN MATCH_MP_TAC SUBRING_GENERATED_INC THEN
    ASM_REWRITE_TAC [UNION_SUBSET, INSERT_SUBSET, EMPTY_SUBSET,
                    IN_UNION, IN_INSERT, NOT_IN_EMPTY] THEN
    RULE_ASSUM_TAC (REWRITE_RULE
     [algebraic_over, field_extension,
      ring_monomorphism, ring_homomorphism]) THEN
    ASM SET_TAC []))

  let ALGEBRAIC_OVER_SUB ← prove
   r"!(h:A->B) k l a b.
        field_extension (k,l) h /\
        algebraic_over (k,l) h a /\ algebraic_over (k,l) h b
        ==> algebraic_over (k,l) h (ring_sub l a b)"
   (SIMP_TAC [ring_sub, ALGEBRAIC_OVER_NEG, ALGEBRAIC_OVER_ADD])

  let ALGEBRAIC_OVER_DIV ← prove
   r"!(h:A->B) k l a b.
        field_extension (k,l) h /\
        algebraic_over (k,l) h a /\ algebraic_over (k,l) h b
        ==> algebraic_over (k,l) h (ring_div l a b)"
   (SIMP_TAC [ring_div, ALGEBRAIC_OVER_INV, ALGEBRAIC_OVER_MUL])

  let ALGEBRAIC_OVER_POW ← prove
   r"!(h:A->B) k l a n.
        field_extension (k,l) h /\ algebraic_over (k,l) h a
        ==> algebraic_over (k,l) h (ring_pow l a n)"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [ring_pow] THEN
    ASM_MESON_TAC [ALGEBRAIC_OVER_1, ALGEBRAIC_OVER_MUL])

  let SUBRING_OF_ALGEBRAIC_OVER ← prove
   r"!(h:A->B) k l.
        field_extension (k,l) h
        ==> {x | algebraic_over (k,l) h x} subring_of l"
   (REWRITE_TAC [subring_of, SUBSET, IN_ELIM_THM] THEN
    MESON_TAC [ALGEBRAIC_OVER_0, ALGEBRAIC_OVER_1, ALGEBRAIC_OVER_NEG,
              ALGEBRAIC_OVER_ADD, ALGEBRAIC_OVER_MUL, ALGEBRAIC_OVER_IN_CARRIER,
              RING_0, RING_1, RING_NEG, RING_ADD, RING_MUL])

  let SUBFIELD_OF_ALGEBRAIC_OVER ← prove
   r"!(h:A->B) k l.
        field_extension (k,l) h
        ==> {x | algebraic_over (k,l) h x} subfield_of l"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_OF_FIELD_INV THEN
    ASM_SIMP_TAC [SUBRING_OF_ALGEBRAIC_OVER] THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    ASM_SIMP_TAC [IN_ELIM_THM, RING_INV] THEN ASM_MESON_TAC [ALGEBRAIC_OVER_INV])

  let ALGEBRAIC_OVER_SUBFIELD_GENERATED_ALGEBRAIC ← prove
   r"!(h:A->B) k l s.
        field_extension (k,l) h /\
        (!x. x IN s ==> algebraic_over(k,l) h x)
        ==> !x. x IN ring_carrier
                  (subfield_generated l (IMAGE h (ring_carrier k) UNION s))
                ==> algebraic_over(k,l) h x"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC [← SET_RULE (← q r"(!x. x IN s ==> P x) <=> s SUBSET {x | P x}")] THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN
    ASM_SIMP_TAC [SUBFIELD_OF_ALGEBRAIC_OVER] THEN
    ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_IN_UNION, IN_ELIM_THM] THEN
    ASM_MESON_TAC [ALGEBRAIC_OVER_IMAGE])

  let FIELD_ALGEBRAIC_EXTENSION ← prove
   r"!(h:A->B) k l s.
        field_extension(k,l) h /\ (!x. x IN s ==> algebraic_over(k,l) h x)
        ==> field(subring_generated l (IMAGE h (ring_carrier k) UNION s))"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [field, ← GSYM TRIVIAL_RING_10, TRIVIAL_RING_SUBRING_GENERATED] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC [FIELD_IMP_NONTRIVIAL_RING, field_extension],
      REWRITE_TAC [← CONJUNCT2 SUBRING_GENERATED]] THEN
    X_GEN_TAC (← q r"a:B") THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"s:B->bool"]
          ALGEBRAIC_OVER_SUBFIELD_GENERATED_ALGEBRAIC) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o SPEC (← q r"a:B")) THEN ANTS_TAC THENL
     [ASM_MESON_TAC [SUBSET, SUBRING_SUBSET_SUBFIELD_GENERATED], DISCH_TAC] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"a:B"]
            FIELD_SIMPLE_ALGEBRAIC_EXTENSION) THEN
    ASM_REWRITE_TAC [field, ← CONJUNCT2 SUBRING_GENERATED] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"a:B") o CONJUNCT2) THEN ASM_REWRITE_TAC [] THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [SUBSET, RING_CARRIER_SUBRING_GENERATED_SUBSET,
                    SUBRING_GENERATED_INC_GEN, IN_INSERT],
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"y:B") THEN
      MATCH_MP_TAC MONO_AND THEN REWRITE_TAC [] THEN
      SPEC_TAC (← q r"y:B", ← q r"y:B") THEN REWRITE_TAC [← GSYM SUBSET] THEN
      MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN
      ASM_REWRITE_TAC [INSERT_SUBSET, SUBRING_SUBRING_GENERATED] THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET) THEN
      ASM SET_TAC []])

  let SUBFIELD_OF_ALGEBRAIC_EXTENSION ← prove
   r"!(h:A->B) k l s.
        field_extension(k,l) h /\ (!x. x IN s ==> algebraic_over(k,l) h x)
        ==> ring_carrier(subring_generated l (IMAGE h (ring_carrier k) UNION s))
            subfield_of l"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [subfield_of, SUBRING_SUBRING_GENERATED] THEN
    REWRITE_TAC [SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
    ASM_SIMP_TAC [FIELD_ALGEBRAIC_EXTENSION])

  let FIELD_ALGEBRAIC_OVER ← prove
   r"!(h:A->B) k l.
        field_extension (k,l) h
        ==> field(subring_generated l {x | algebraic_over (k,l) h x})"
   (MESON_TAC [subfield_of, SUBFIELD_OF_ALGEBRAIC_OVER])

  let SUBRING_SUBFIELD_ALGEBRAIC_OVER ← prove
   r"!(h:A->B) k l.
        field_extension (k,l) h
        ==> subring_generated l {x | algebraic_over (k,l) h x} =
            subfield_generated l {x | algebraic_over (k,l) h x}"
   (SIMP_TAC [SUBRING_EQ_SUBFIELD_GENERATED, FIELD_ALGEBRAIC_OVER])

  let ALGEBRAIC_OVER_TRANS ← prove
   r"!(f:A->B) (g:B->C) k l m z.
        algebraic_extension(k,l) f /\ field_extension(l,m) g /\
        algebraic_over(l,m) g z
        ==> algebraic_over(k,m) (g o f) z"
   (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL
     [← q r"f:A->B", ← q r"g:B->C", ← q r"k:A ring", ← q r"l:B ring",
      ← q r"subring_generated m {x | algebraic_over(l,m) (g:B->C) x}"]
     ALGEBRAIC_EXTENSION_TRANS) THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [algebraic_extension] THEN
    ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING, ALGEBRAIC_OVER_IMAGE_SUBSET,
                 SUBRING_OF_ALGEBRAIC_OVER, SUBFIELD_OF_ALGEBRAIC_OVER,
                 FIELD_EXTENSION_INTO_SUBRING_GENERATED,
                 ALGEBRAIC_OVER_SUBRING_GENERATED, IN_ELIM_THM] THEN
    ASM_MESON_TAC [ALGEBRAIC_FROM_SUBRING_GENERATED])

  let ALGEBRAIC_OVER_ALGEBRAIC_EXTENSION ← prove
   r"!(f:A->B) (g:B->C) k l m x.
        algebraic_extension (k,l) f /\
        field_extension (l,m) g
        ==> (algebraic_over (k,m) (g o f) x <=> algebraic_over (l,m) g x)"
   (ASM_MESON_TAC [ALGEBRAIC_OVER_FROM_MONOMORPHIC_IMAGE, ALGEBRAIC_OVER_TRANS,
                  algebraic_extension, field_extension, ring_monomorphism])

  -- @@RETURN BEGIN
  return { ALGEBRAIC_OVER_0, ALGEBRAIC_OVER_1, ALGEBRAIC_OVER_NEG, ALGEBRAIC_OVER_INV,
           ALGEBRAIC_OVER_ADD, ALGEBRAIC_OVER_MUL, ALGEBRAIC_OVER_SUB,
           ALGEBRAIC_OVER_DIV, ALGEBRAIC_OVER_POW, SUBRING_OF_ALGEBRAIC_OVER,
           SUBFIELD_OF_ALGEBRAIC_OVER, ALGEBRAIC_OVER_SUBFIELD_GENERATED_ALGEBRAIC,
           FIELD_ALGEBRAIC_EXTENSION, SUBFIELD_OF_ALGEBRAIC_EXTENSION,
           FIELD_ALGEBRAIC_OVER, SUBRING_SUBFIELD_ALGEBRAIC_OVER, ALGEBRAIC_OVER_TRANS,
           ALGEBRAIC_OVER_ALGEBRAIC_EXTENSION }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Extensions involving finite fields etc.  (fieldtheory.ml 3744-3838)       -/
/- ------------------------------------------------------------------------- -/

structure FiniteExt where
  -- @@FIELDS
  FINITE_EQ_FIELD_EXTENSION : thm
  HAS_SIZE_FINITE_EXTENSION : thm
  FINITE_FINITE_FIELD_EXTENSION : thm
  CARD_FINITE_EXTENSION : thm
  FIELD_EXTENSION_FROM_PRIME_SUBRING : thm
  FINITE_INTEGRAL_DOMAIN_SIZE : thm
  deriving Inhabited

@[nospecialize]
def setupFiniteExt [HolBase] (D : FieldTheoryDeps) (BFieldExtension : FieldExtension) (BRingSpan : RingSpan) (BLinearAlgebra : LinearAlgebra) (BFinitary : Finitary) (BFiniteExtension : FiniteExtension) :
    ExceptT String IO FiniteExt := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, .. } := D
  let { CARD_PRIME_SUBRING, CARRIER_SUBRING_GENERATED_SUBRING, CONJ_ACI, EXP, .. } := D.core1
  let { FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING, FIELD_PRIME_SUBRING,
        FINITE_HAS_SIZE, FINITE_INTEGRAL_DOMAIN_EQ_FIELD, FINITE_PRIME_SUBRING,
        FUN_EQ_THM, HAS_SIZE, HAS_SIZE_FUNSPACE, HAS_SIZE_IMAGE_INJ, .. } := D.core2
  let { IMP_CONJ, IMP_CONJ_ALT, INTEGRAL_DOMAIN_CHAR, IN_ELIM_THM, I_DEF, .. } := D.core3
  let { MONO_FORALL, .. } := D.core4
  let { PRIME_SUBRING, RESTRICTION, RING_CHAR_FINITE, .. } := D.core5
  let { RING_MONOMORPHISM_INCLUSION, .. } := D.core6
  let { RING_SUM_EQ, SIMPLE_IMAGE_GEN, .. } := D.core7
  let { SUBSET_REFL, TRIVIAL_RING_HAS_SIZE_1, .. } := D.core8
  let { ring_monomorphism, .. } := D.core9
  let { FIELD_EXTENSION_IMP_HOMOMORPHISM, field_extension, .. } := BFieldExtension
  let { RING_SPAN_FINITE, RING_SPAN_SELF, .. } := BRingSpan
  let { ring_basis, ring_spanning, .. } := BLinearAlgebra
  let { RING_INDEPENDENT_FINITE_EQ, .. } := BFinitary
  let { FINITE_EXTENSION_BASIS, FINITE_IMP_FIELD_EXTENSION, finite_extension, .. } := BFiniteExtension
  -- @@SCOPE END

  let FINITE_EQ_FIELD_EXTENSION ← prove
   r"!(h:A->B) k l.
        FINITE(ring_carrier l)
        ==> (finite_extension(k,l) h <=> field_extension(k,l) h)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN
    REWRITE_TAC [FINITE_IMP_FIELD_EXTENSION] THEN
    REWRITE_TAC [finite_extension] THEN
    ASM_MESON_TAC [RING_SPAN_SELF, SUBSET_REFL])

  let HAS_SIZE_FINITE_EXTENSION ← prove
   r"!(h:A->B) k l b.
        field_extension (k,l) h /\ ring_basis (k,l) h b /\
        FINITE(ring_carrier k) /\ FINITE b
        ==> ring_carrier l HAS_SIZE CARD(ring_carrier k) EXP CARD b"
   (← do
    let a1 ← SET_RULE (← q
      r"!g. (!x. f(g x) = f x) /\ (!x. P x ==> P(g x) /\ Q(g x))
          ==> IMAGE f {x | P x} = IMAGE f {x | P x /\ Q x}")
    pure (REWRITE_TAC [ring_basis, ring_spanning] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     (← q r"ring_span (k,l) (h:A->B) b =
      IMAGE (\c. ring_sum l b (\x. ring_mul l (h (c x)) x))
            { c | (!x. x IN b ==> c x IN ring_carrier k) /\
                  (!x. ~(x IN b) ==> c x = ARB) }")
    SUBST1_TAC THENL
     [ASM_SIMP_TAC [RING_SPAN_FINITE, FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
      GEN_REWRITE_TAC LAND_CONV [SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC a1 THEN
      EXISTS_TAC (← q r"\c:B->A. RESTRICTION b c") THEN
      SIMP_TAC [RESTRICTION] THEN GEN_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
      SIMP_TAC [],
      MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN REWRITE_TAC [IN_ELIM_THM] THEN
      ASM_SIMP_TAC [← GSYM FINITE_HAS_SIZE, HAS_SIZE_FUNSPACE] THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"b:B->bool"]
          RING_INDEPENDENT_FINITE_EQ) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [ASM_MESON_TAC [field_extension, ring_monomorphism], ALL_TAC] THEN
      REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
      REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
      ASM_MESON_TAC []]))

  let FINITE_FINITE_FIELD_EXTENSION ← prove
   r"!(h:A->B) k l.
        FINITE(ring_carrier k)
        ==> (finite_extension(k,l) h <=>
             field_extension(k,l) h /\ FINITE(ring_carrier l))"
   (MESON_TAC [FINITE_EQ_FIELD_EXTENSION, FINITE_EXTENSION_BASIS,
              HAS_SIZE, HAS_SIZE_FINITE_EXTENSION, ring_basis])

  let CARD_FINITE_EXTENSION ← prove
   r"!(h:A->B) k l b.
        field_extension (k,l) h /\ ring_basis (k,l) h b /\
        FINITE(ring_carrier k) /\ FINITE b
        ==> CARD(ring_carrier l) = CARD(ring_carrier k) EXP CARD b"
   (MESON_TAC [HAS_SIZE, HAS_SIZE_FINITE_EXTENSION])

  let FIELD_EXTENSION_FROM_PRIME_SUBRING ← prove
   r"!r:A ring.
    field_extension (subring_generated r {ring_of_int r n | n IN (:int)},r)
                    I <=>
    field r /\ prime(ring_char r)"
   (REWRITE_TAC [field_extension, FIELD_PRIME_SUBRING, I_DEF] THEN
    REWRITE_TAC [RING_MONOMORPHISM_INCLUSION, CONJ_ACI])

  let FINITE_INTEGRAL_DOMAIN_SIZE ← prove
   r"!k:A ring.
        integral_domain k /\ FINITE(ring_carrier k)
        ==> ?p n. prime p /\ ~(n = 0) /\ CARD(ring_carrier k) = p EXP n"
   (SIMP_TAC [IMP_CONJ_ALT, FINITE_INTEGRAL_DOMAIN_EQ_FIELD] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"ring_char(k:A ring)") THEN
    MP_TAC (← ISPEC (← q r"k:A ring") INTEGRAL_DOMAIN_CHAR) THEN
    ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, RING_CHAR_FINITE] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"finite_extension (subring_generated k {ring_of_int k n | n IN (:int)},k)
                       (I:A->A)")
    MP_TAC THENL
     [ASM_SIMP_TAC [FINITE_EQ_FIELD_EXTENSION, FIELD_EXTENSION_FROM_PRIME_SUBRING],
      REWRITE_TAC [FINITE_EXTENSION_BASIS]] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN (← q r"b:A->bool") STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"b:A->bool") o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          CARD_FINITE_EXTENSION)) THEN
    ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING, PRIME_SUBRING] THEN
    ASM_SIMP_TAC [FINITE_PRIME_SUBRING, CARD_PRIME_SUBRING, RING_CHAR_FINITE] THEN
    DISCH_TAC THEN EXISTS_TAC (← q r"CARD(b:A->bool)") THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [EXP, TRIVIAL_RING_HAS_SIZE_1, HAS_SIZE,
                  FIELD_IMP_NONTRIVIAL_RING])

  -- @@RETURN BEGIN
  return { FINITE_EQ_FIELD_EXTENSION, HAS_SIZE_FINITE_EXTENSION,
           FINITE_FINITE_FIELD_EXTENSION, CARD_FINITE_EXTENSION,
           FIELD_EXTENSION_FROM_PRIME_SUBRING, FINITE_INTEGRAL_DOMAIN_SIZE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Algebraic dependence and a corresponding notion of algebraic span,        -/
/- leading to basic results on transcendence bases and transcendence degree. -/
/-                                                                           -/
/- We special-case 0 in span to avoid excluding k's being the trivial ring.  -/
/- Because of the way polynomial rings are defined, all polynomials are      -/
/- considered zero over the trivial ring so the "non-trivial polynomial"     -/
/- part is degenerately false. For fields this is irrelevant, and there      -/
/- it is also equivalent to using "subfield_generated" instead.              -/
/- (fieldtheory.ml 3842-4013)                                                -/
/- ------------------------------------------------------------------------- -/

structure AlgDepDefs where
  -- @@FIELDS
  algebraically_dependent : thm
  algebraically_independent : thm
  algebraic_span : thm
  algebraically_spanning : thm
  transcendence_basis : thm
  ALGEBRAICALLY_DEPENDENT_IMP_SUBSET : thm
  ALGEBRAICALLY_INDEPENDENT_IMP_SUBSET : thm
  TRANSCENDENCE_BASIS_IMP_SUBSET : thm
  ALGEBRAICALLY_DEPENDENT_ALT : thm
  ALGEBRAIC_SPAN : thm
  ALGEBRAIC_SPAN_FIELD : thm
  ALGEBRAIC_SPAN_RANGE : thm
  ALGEBRAIC_SPAN_RESTRICT : thm
  ALGEBRAIC_SPAN_SUBSET : thm
  RING_SPAN_SUBSET_ALGEBRAIC_SPAN : thm
  ALGEBRAIC_SPAN_SUPERSET : thm
  ALGEBRAIC_SPAN_MONO : thm
  ALGEBRAIC_EXTENSION_SUBFIELD_GENERATED_ALGEBRAIC : thm
  ALGEBRAIC_EXTENSION_SUBRING_GENERATED_ALGEBRAIC : thm
  deriving Inhabited

@[nospecialize]
def setupAlgDepDefs [HolBase] (D : FieldTheoryDeps) (BSubfieldGenerated : SubfieldGenerated) (BFieldExtension : FieldExtension) (BRingSpan : RingSpan) (BFinitary : Finitary) (BAlgebraicExtension : AlgebraicExtension) (BAlgebraicField : AlgebraicField) :
    ExceptT String IO AlgDepDefs := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, TAUT, define, new_definition, .. } := D
  let { EXTENSION, .. } := D.core1
  let { FIELD_IMP_NONTRIVIAL_RING, FORALL_IN_GSPEC, IMAGE_I, .. } := D.core2
  let { IMP_CONJ_ALT, INSERT_SUBSET, IN_ELIM_THM, IN_INSERT, IN_POLY_RING_CARRIER,
        I_DEF, I_THM, LEFT_IMP_EXISTS_THM, .. } := D.core3
  let { MONO_AND, MONO_EXISTS, POLY_CONST_EQ, POLY_DEG_0, POLY_DEG_EQ_0, .. } := D.core4
  let { POLY_EXTEND_CONST, POLY_EXTEND_FROM_SUBRING_GENERATED, POLY_RING,
        POLY_SUBRING_GENERATED_CLAUSES, RING_0, RING_0_IN_SUBRING_GENERATED,
        RING_CARRIER_POLY_SUBRING_GENERATED_MONO, .. } := D.core5
  let { RING_HOMOMORPHISM_INCLUSION, RING_MONOMORPHISM_EQ_0,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, .. } := D.core6
  let { SUBRING_GENERATED, .. } := D.core7
  let { SUBRING_GENERATED_RESTRICT, SUBRING_GENERATED_UNION_LEFT, SUBSET, SUBSET_TRANS,
        TRIVIAL_RING_SUBRING_GENERATED, .. } := D.core8
  let { poly_0, .. } := D.core9
  let { CARRIER_SUBFIELD_GENERATED_SUBFIELD, .. } := BSubfieldGenerated
  let { FIELD_EXTENSION_INTO_SUBFIELD_GENERATED, FIELD_EXTENSION_REFL, .. } := BFieldExtension
  let { RING_SPAN_SUPERSET, .. } := BRingSpan
  let { RING_SPAN_SUBSET_SUBRING_GENERATED, .. } := BFinitary
  let { ALGEBRAIC_OVER_IMAGE_GEN, ALGEBRAIC_OVER_IMAGE_SUBSET,
        ALGEBRAIC_OVER_IN_CARRIER, ALGEBRAIC_OVER_SUBFIELD_GENERATED,
        ALGEBRAIC_OVER_SUBFIELD_SUBRING_GENERATED, algebraic_extension, algebraic_over, .. } := BAlgebraicExtension
  let { SUBFIELD_OF_ALGEBRAIC_OVER, SUBRING_SUBFIELD_ALGEBRAIC_OVER, .. } := BAlgebraicField
  -- @@SCOPE END

  let algebraically_dependent ← new_definition
   r"algebraically_dependent (k,l) (h:A->B) s <=>
        s SUBSET ring_carrier l /\
        ?p. p IN ring_carrier(poly_ring k s) /\
            ~(p = ring_0(poly_ring k s)) /\
            poly_extend(k,l) h (\x. x) p = ring_0 l"

  let algebraically_independent ← define
   r"algebraically_independent (k,l) (h:A->B) s <=>
        s SUBSET ring_carrier l /\ ~(algebraically_dependent (k,l) h s)"

  let algebraic_span ← new_definition
   r"algebraic_span (k,l) (h:A->B) s =
      ring_0 l INSERT
      {x | algebraic_over
            (subring_generated l (IMAGE h (ring_carrier k) UNION s),l) I x}"

  let algebraically_spanning ← define
   r"algebraically_spanning (k,l) (h:A->B) s <=>
  s SUBSET ring_carrier l /\
  !y. y IN ring_carrier l
      ==> algebraic_over
           (subring_generated l (IMAGE h (ring_carrier k) UNION s),l) I y"

  let transcendence_basis ← define
   r"transcendence_basis (k,l) (h:A->B) s <=>
        algebraically_spanning (k,l) h s /\
        algebraically_independent (k,l) h s"

  let ALGEBRAICALLY_DEPENDENT_IMP_SUBSET ← prove
   r"!(h:A->B) k l s.
        algebraically_dependent (k,l) h s ==> s SUBSET ring_carrier l"
   (SIMP_TAC [algebraically_dependent])

  let ALGEBRAICALLY_INDEPENDENT_IMP_SUBSET ← prove
   r"!(h:A->B) k l s.
        algebraically_independent (k,l) h s ==> s SUBSET ring_carrier l"
   (SIMP_TAC [algebraically_independent])

  let TRANSCENDENCE_BASIS_IMP_SUBSET ← prove
   r"!(h:A->B) k l s.
        transcendence_basis (k,l) h s ==> s SUBSET ring_carrier l"
   (SIMP_TAC [transcendence_basis, algebraically_independent])

  let ALGEBRAICALLY_DEPENDENT_ALT ← prove
   r"!(h:A->B) k l s.
        ring_monomorphism(k,l) h
        ==> (algebraically_dependent (k,l) h s <=>
             s SUBSET ring_carrier l /\
             ?p. p IN ring_carrier(poly_ring k s) /\
                 ~(poly_deg k p = 0) /\
                 poly_extend(k,l) h (\x. x) p = ring_0 l)"
   (← do
    let a1 ← TAUT (← q r"(r ==> ~q) ==> p ==> q ==> ~r")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [algebraically_dependent] THEN
    EQ_TAC THENL [ALL_TAC, MESON_TAC [POLY_DEG_0, POLY_RING]] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"p:(B->num)->A") THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [IN_POLY_RING_CARRIER]) THEN
    ASM_SIMP_TAC [POLY_DEG_EQ_0] THEN
    MATCH_MP_TAC a1 THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [POLY_EXTEND_CONST, RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
    REWRITE_TAC [POLY_RING, poly_0, POLY_CONST_EQ] THEN
    ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0]))

  let ALGEBRAIC_SPAN ← prove
   r"!(h:A->B) k l s.
    ~(trivial_ring l)
    ==> algebraic_span (k,l) h s =
         {x | algebraic_over
              (subring_generated l (IMAGE h (ring_carrier k) UNION s),l) I x}"
   (← do
    let a1 ← SET_RULE (← q r"a INSERT s = s <=> a IN s")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [algebraic_span] THEN
    REWRITE_TAC [a1, IN_ELIM_THM] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM I_THM] THEN
    MATCH_MP_TAC ALGEBRAIC_OVER_IMAGE_GEN THEN
    ASM_REWRITE_TAC [TRIVIAL_RING_SUBRING_GENERATED, ← CONJUNCT2 SUBRING_GENERATED,
            RING_0_IN_SUBRING_GENERATED, RING_HOMOMORPHISM_INCLUSION, I_DEF]))

  let ALGEBRAIC_SPAN_FIELD ← prove
   r"!(h:A->B) k l s.
    field l
    ==> algebraic_span (k,l) h s =
         {x | algebraic_over
             (subfield_generated l (IMAGE h (ring_carrier k) UNION s),l) I x}"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [ALGEBRAIC_SPAN, FIELD_IMP_NONTRIVIAL_RING] THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"y:B") THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC ALGEBRAIC_OVER_SUBFIELD_SUBRING_GENERATED THEN
    ASM_REWRITE_TAC [FIELD_EXTENSION_REFL])

  let ALGEBRAIC_SPAN_RANGE ← prove
   r"!(h:A->B) k l s.
        algebraic_span (k,l) h s =
        algebraic_span (subring_generated l (IMAGE h (ring_carrier k)),l) I s"
   (REWRITE_TAC [algebraic_span] THEN
    REWRITE_TAC [IMAGE_I, SUBRING_GENERATED_UNION_LEFT])

  let ALGEBRAIC_SPAN_RESTRICT ← prove
   r"!(h:A->B) k l s.
        algebraic_span (k,l) h s =
        algebraic_span (k,l) h (ring_carrier l INTER s)"
   (← do
    let a1 ← SET_RULE (← q r"s INTER (u UNION s INTER v) = s INTER (u UNION v)")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [algebraic_span] THEN
    ONCE_REWRITE_TAC [SUBRING_GENERATED_RESTRICT] THEN
    REWRITE_TAC [a1]))

  let ALGEBRAIC_SPAN_SUBSET ← prove
   r"!(h:A->B) k l s. algebraic_span (k,l) h s SUBSET ring_carrier l"
   (REWRITE_TAC [algebraic_span, INSERT_SUBSET, RING_0] THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN MESON_TAC [ALGEBRAIC_OVER_IN_CARRIER])

  let RING_SPAN_SUBSET_ALGEBRAIC_SPAN ← prove
   r"!(h:A->B) k l s. ring_span (k,l) h s SUBSET algebraic_span (k,l) h s"
   (REPEAT GEN_TAC THEN
    wPart (fun c => do lhand c) (fun c => do lhand c)
      RING_SPAN_SUBSET_SUBRING_GENERATED THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] SUBSET_TRANS) THEN
    REWRITE_TAC [algebraic_span] THEN REWRITE_TAC [SUBSET, IN_INSERT] THEN
    X_GEN_TAC (← q r"x:B") THEN ASM_CASES_TAC (← q r"x:B = ring_0 l") THEN
    ASM_REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM I_THM] THEN
    MATCH_MP_TAC ALGEBRAIC_OVER_IMAGE_GEN THEN
    ASM_REWRITE_TAC [SUBRING_GENERATED] THEN
    REWRITE_TAC [I_DEF, RING_HOMOMORPHISM_INCLUSION])

  let ALGEBRAIC_SPAN_SUPERSET ← prove
   r"!(h:A->B) k l s.
        s SUBSET ring_carrier l ==> s SUBSET algebraic_span (k,l) h s"
   (MESON_TAC [RING_SPAN_SUPERSET, RING_SPAN_SUBSET_ALGEBRAIC_SPAN,
              SUBSET_TRANS])

  let ALGEBRAIC_SPAN_MONO ← prove
   r"!(h:A->B) k l s t.
    s SUBSET t ==> algebraic_span (k,l) h s SUBSET algebraic_span (k,l) h t"
   (← do
    let a2 ← SET_RULE (← q r"s SUBSET t ==> x IN s ==> x IN t")
    let a1 ← SET_RULE (← q r"s SUBSET t ==> a INSERT s SUBSET a INSERT t")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [algebraic_span] THEN
    MATCH_MP_TAC a1 THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM, algebraic_over,
                POLY_SUBRING_GENERATED_CLAUSES,
                POLY_EXTEND_FROM_SUBRING_GENERATED] THEN
    X_GEN_TAC (← q r"y:B") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"p:(1->num)->B") THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC [] THEN
    MATCH_MP_TAC a2 THEN
    MATCH_MP_TAC RING_CARRIER_POLY_SUBRING_GENERATED_MONO THEN
    ASM SET_TAC []))

  let ALGEBRAIC_EXTENSION_SUBFIELD_GENERATED_ALGEBRAIC ← prove
   r"!(h:A->B) k l.
        field_extension(k,l) h
        ==> algebraic_extension
             (k,subfield_generated l {x | algebraic_over (k,l) h x}) h"
   (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [algebraic_extension] THEN
    ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD,
                 SUBFIELD_OF_ALGEBRAIC_OVER] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
      ASM_SIMP_TAC [SUBFIELD_OF_ALGEBRAIC_OVER, ALGEBRAIC_OVER_IMAGE_SUBSET],
      REWRITE_TAC [FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN
      MATCH_MP_TAC ALGEBRAIC_OVER_SUBFIELD_GENERATED THEN
      ASM_SIMP_TAC [ALGEBRAIC_OVER_IMAGE_SUBSET, IN_ELIM_THM]])

  let ALGEBRAIC_EXTENSION_SUBRING_GENERATED_ALGEBRAIC ← prove
   r"!(h:A->B) k l.
        field_extension(k,l) h
        ==> algebraic_extension
             (k,subring_generated l {x | algebraic_over (k,l) h x}) h"
   (MESON_TAC [SUBRING_SUBFIELD_ALGEBRAIC_OVER,
              ALGEBRAIC_EXTENSION_SUBFIELD_GENERATED_ALGEBRAIC])

  -- @@RETURN BEGIN
  return { algebraically_dependent, algebraically_independent, algebraic_span,
           algebraically_spanning, transcendence_basis,
           ALGEBRAICALLY_DEPENDENT_IMP_SUBSET, ALGEBRAICALLY_INDEPENDENT_IMP_SUBSET,
           TRANSCENDENCE_BASIS_IMP_SUBSET, ALGEBRAICALLY_DEPENDENT_ALT, ALGEBRAIC_SPAN,
           ALGEBRAIC_SPAN_FIELD, ALGEBRAIC_SPAN_RANGE, ALGEBRAIC_SPAN_RESTRICT,
           ALGEBRAIC_SPAN_SUBSET, RING_SPAN_SUBSET_ALGEBRAIC_SPAN,
           ALGEBRAIC_SPAN_SUPERSET, ALGEBRAIC_SPAN_MONO,
           ALGEBRAIC_EXTENSION_SUBFIELD_GENERATED_ALGEBRAIC,
           ALGEBRAIC_EXTENSION_SUBRING_GENERATED_ALGEBRAIC }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Properties of algebraic span and (in)dependence: idempotence, finitary    -/
/- character, singletons, monotonicity.  (fieldtheory.ml 4014-4190)          -/
/- ------------------------------------------------------------------------- -/

structure AlgDepSpan where
  -- @@FIELDS
  ALGEBRAIC_SPAN_SPAN : thm
  ALGEBRAIC_SPAN_FINITARY : thm
  ALGEBRAIC_SPAN_EMPTY : thm
  ALGEBRAICALLY_INDEPENDENT_EMPTY : thm
  ALGEBRAICALLY_DEPENDENT_SING : thm
  ALGEBRAICALLY_INDEPENDENT_SING : thm
  ALGEBRAICALLY_DEPENDENT_MONO : thm
  ALGEBRAICALLY_DEPENDENT_OVER_SUBRING_GENERATED_MONO : thm
  ALGEBRAICALLY_INDEPENDENT_MONO : thm
  ALGEBRAICALLY_INDEPENDENT_OVER_SUBRING_GENERATED_MONO : thm
  ALGEBRAICALLY_INDEPENDENT_IMP_TRANSCENDENTAL : thm
  ALGEBRAICALLY_INDEPENDENT_IMP_DISJOINT : thm
  deriving Inhabited

@[nospecialize]
def setupAlgDepSpan [HolBase] (D : FieldTheoryDeps) (BSubfieldGenerated : SubfieldGenerated) (BSubfieldGenerated1 : SubfieldGenerated1) (BFieldExtension : FieldExtension) (BAlgebraicExtension : AlgebraicExtension) (BAlgebraicExtensionProps : AlgebraicExtensionProps) (BAlgebraicField : AlgebraicField) (BAlgDepDefs : AlgDepDefs) :
    ExceptT String IO AlgDepSpan := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, .. } := D
  let { EMPTY_SUBSET, EQ_IMP, EXISTS_IN_IMAGE, .. } := D.core1
  let { FINITE_EMPTY, FINITE_INTER, IMAGE_I, .. } := D.core2
  let { IMP_CONJ, INTER_SUBSET, IN_ELIM_THM, IN_INSERT,
        IN_POLY_RING_SUBRING_GENERATED_FINITARY, IN_SING, I_O_ID, .. } := D.core3
  let { MONO_AND, MONO_EXISTS, POLY_CONST_EQ, .. } := D.core4
  let { POLY_EXTEND_CONST, POLY_EXTEND_EQ, POLY_EXTEND_FROM_SUBRING_GENERATED,
        POLY_RING, POLY_RING_MONO, POLY_SUBRING_GENERATED_CLAUSES,
        RIGHT_AND_EXISTS_THM, RING_CARRIER_POLY_SUBRING_GENERATED_MONO, .. } := D.core5
  let { RING_ISOMORPHISM_IMP_EPIMORPHISM, RING_ISOMORPHISM_POLY_RING_TRIVIAL,
        RING_MONOMORPHISM_EQ_0, RING_MONOMORPHISM_IMP_HOMOMORPHISM, .. } := D.core6
  let { SING_SUBSET, .. } := D.core7
  let { SUBSET, SUBSET_ANTISYM, SUBSET_TRANS, SWAP_EXISTS_THM, UNION_EMPTY, .. } := D.core8
  let { poly_0, ring_epimorphism, ring_homomorphism, ring_monomorphism, .. } := D.core9
  let { FIELD_SUBFIELD_GENERATED, SUBRING_GENERATED_BY_SUBFIELD_GENERATED, .. } := BSubfieldGenerated
  let { SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET, .. } := BSubfieldGenerated1
  let { FIELD_EXTENSION_FROM_SUBRING_GENERATED, FIELD_EXTENSION_REFL, field_extension, .. } := BFieldExtension
  let { ALGEBRAIC_OVER, ALGEBRAIC_OVER_IMAGE, ALGEBRAIC_OVER_IMAGE_SUBSET,
        algebraic_over, transcendental_over, .. } := BAlgebraicExtension
  let { ALGEBRAIC_OVER_RANGE, .. } := BAlgebraicExtensionProps
  let { ALGEBRAIC_OVER_TRANS, .. } := BAlgebraicField
  let { ALGEBRAIC_EXTENSION_SUBFIELD_GENERATED_ALGEBRAIC, ALGEBRAIC_SPAN,
        ALGEBRAIC_SPAN_FIELD, ALGEBRAIC_SPAN_MONO, ALGEBRAIC_SPAN_RESTRICT,
        ALGEBRAIC_SPAN_SUPERSET, algebraic_span, algebraically_dependent,
        algebraically_independent, .. } := BAlgDepDefs
  -- @@SCOPE END

  let ALGEBRAIC_SPAN_SPAN ← prove
   r"!(h:A->B) k l s.
        field_extension(k,l) h
        ==> algebraic_span (k,l) h (algebraic_span (k,l) h s) =
            algebraic_span (k,l) h s"
   (← do
    let a2 ← SET_RULE (← q r"s = t UNION s <=> t SUBSET s")
    let a1 ← SET_RULE (← q r"(ring_carrier l INTER s:B->bool) SUBSET ring_carrier l")
    pure (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [ALGEBRAIC_SPAN_RESTRICT] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [ALGEBRAIC_SPAN_RESTRICT] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    ASM_SIMP_TAC [ALGEBRAIC_SPAN_MONO, ALGEBRAIC_SPAN_SUPERSET, INTER_SUBSET] THEN
    MP_TAC a1 THEN
    SPEC_TAC (← q r"ring_carrier l INTER s:B->bool", ← q r"s:B->bool") THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [ALGEBRAIC_SPAN_FIELD] THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN
    MP_TAC (← ISPECL
     [← q r"I:B->B", ← q r"I:B->B",
      ← q r"subfield_generated l (IMAGE (h:A->B) (ring_carrier k) UNION s)",
      ← q r"subfield_generated l
         (IMAGE h (ring_carrier k) UNION
          {x | algebraic_over
                 (subfield_generated l (IMAGE (h:A->B) (ring_carrier k) UNION s),
                  l) I x})",
      ← q r"l:B ring", ← q r"x:B"] ALGEBRAIC_OVER_TRANS) THEN
    ASM_REWRITE_TAC [I_O_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [MP_TAC (← ISPECL
       [← q r"I:B->B",
        ← q r"subfield_generated l (IMAGE (h:A->B) (ring_carrier k) UNION s)",
        ← q r"l:B ring"] ALGEBRAIC_EXTENSION_SUBFIELD_GENERATED_ALGEBRAIC) THEN
      ANTS_TAC THENL
       [ALL_TAC,
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC [a2] THEN
        MP_TAC (← ISPECL
         [← q r"I:B->B",
          ← q r"subfield_generated l (IMAGE (h:A->B) (ring_carrier k) UNION s)",
          ← q r"l:B ring"] ALGEBRAIC_OVER_IMAGE_SUBSET) THEN
        ANTS_TAC THENL
         [ALL_TAC,
          REWRITE_TAC [IMAGE_I] THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ]
            SUBSET_TRANS) THEN
          wPart (fun c => do rand c) (fun c => do rand (← rand c))
            SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET THEN
          RULE_ASSUM_TAC (REWRITE_RULE [ring_monomorphism, ring_homomorphism]) THEN
          ASM SET_TAC []]],
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    MATCH_MP_TAC FIELD_EXTENSION_FROM_SUBRING_GENERATED THEN
    REWRITE_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    REWRITE_TAC [FIELD_EXTENSION_REFL] THEN
    ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED]))

  let ALGEBRAIC_SPAN_FINITARY ← prove
   r"!(h:A->B) k l s a.
        a IN algebraic_span (k,l) h s
        ==> ?t. FINITE t /\ t SUBSET s /\ a IN algebraic_span (k,l) h t"
   (REPEAT GEN_TAC THEN REWRITE_TAC [algebraic_span, IN_INSERT] THEN
    ASM_CASES_TAC (← q r"a:B = ring_0 l") THEN ASM_REWRITE_TAC [] THENL
     [ASM_MESON_TAC [FINITE_EMPTY, EMPTY_SUBSET], ALL_TAC] THEN
    REWRITE_TAC [algebraic_over, IN_ELIM_THM, POLY_SUBRING_GENERATED_CLAUSES] THEN
    REWRITE_TAC [POLY_EXTEND_FROM_SUBRING_GENERATED] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN
    GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"p:(1->num)->B") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP IN_POLY_RING_SUBRING_GENERATED_FINITARY) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"t:B->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"s INTER t:B->bool") THEN
    ASM_SIMP_TAC [FINITE_INTER, INTER_SUBSET] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE (← q
     r"x IN s ==> s SUBSET t ==> x IN t"))) THEN
    MATCH_MP_TAC RING_CARRIER_POLY_SUBRING_GENERATED_MONO THEN
    ASM SET_TAC [])

  let ALGEBRAIC_SPAN_EMPTY ← prove
   r"!(h:A->B) k l.
     ring_monomorphism(k,l) h /\ ~trivial_ring l
     ==> algebraic_span (k,l) h {} = {x | algebraic_over (k,l) h x}"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [ALGEBRAIC_SPAN, UNION_EMPTY] THEN
    ASM_SIMP_TAC [← GSYM ALGEBRAIC_OVER_RANGE])

  let ALGEBRAICALLY_INDEPENDENT_EMPTY ← prove
   r"!(h:A->B) k l.
    ring_monomorphism(k,l) h ==> algebraically_independent (k,l) h {}"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC
     [algebraically_independent, algebraically_dependent, EMPTY_SUBSET] THEN
    SUBGOAL_THEN
     (← q r"ring_epimorphism(k,poly_ring k {}) (poly_const k:A->(B->num)->A)")
    MP_TAC THENL
     [MESON_TAC [RING_ISOMORPHISM_POLY_RING_TRIVIAL,
                RING_ISOMORPHISM_IMP_EPIMORPHISM],
      REWRITE_TAC [ring_epimorphism]] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    REWRITE_TAC [EMPTY_SUBSET, EXISTS_IN_IMAGE] THEN
    DISCH_THEN (CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC [POLY_EXTEND_CONST, RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
    REWRITE_TAC [POLY_RING, poly_0, POLY_CONST_EQ] THEN
    ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0])

  let ALGEBRAICALLY_DEPENDENT_SING ← prove
   r"!(h:A->B) k l x.
        algebraically_dependent (k,l) h {x} <=>
        algebraic_over (k,l) h x"
   (REPEAT GEN_TAC THEN MP_TAC (← ISPECL
     [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"x:B", ← q r"x:B"] ALGEBRAIC_OVER) THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [algebraically_dependent, SING_SUBSET] THEN
    EQ_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"p:(B->num)->A") THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC POLY_EXTEND_EQ THEN EXISTS_TAC (← q r"{x:B}") THEN
    ASM_SIMP_TAC [IN_SING])

  let ALGEBRAICALLY_INDEPENDENT_SING ← prove
   r"!(h:A->B) k l x.
        algebraically_independent (k,l) h {x} <=>
        transcendental_over (k,l) h x"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [algebraically_independent, transcendental_over,
                ALGEBRAICALLY_DEPENDENT_SING, SING_SUBSET])

  let ALGEBRAICALLY_DEPENDENT_MONO ← prove
   r"!(h:A->B) k l s t.
     algebraically_dependent (k,l) h s /\ s SUBSET t /\ t SUBSET ring_carrier l
     ==> algebraically_dependent (k,l) h t"
   (REWRITE_TAC [algebraically_dependent] THEN REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC [← CONJUNCT2 POLY_RING] THEN
    ASM_MESON_TAC [POLY_RING_MONO])

  let ALGEBRAICALLY_DEPENDENT_OVER_SUBRING_GENERATED_MONO ← prove
   r"!(h:A->B) k l s t d.
        algebraically_dependent (subring_generated k s,l) h d /\ s SUBSET t
        ==> algebraically_dependent (subring_generated k t,l) h d"
   (REWRITE_TAC [algebraically_dependent, POLY_EXTEND_FROM_SUBRING_GENERATED] THEN
    REWRITE_TAC [POLY_SUBRING_GENERATED_CLAUSES] THEN
    MESON_TAC [RING_CARRIER_POLY_SUBRING_GENERATED_MONO, SUBSET])

  let ALGEBRAICALLY_INDEPENDENT_MONO ← prove
   r"!(h:A->B) k l s t.
        algebraically_independent (k,l) h t /\ s SUBSET t
        ==> algebraically_independent (k,l) h s"
   (REWRITE_TAC [algebraically_independent] THEN
    ASM_MESON_TAC [ALGEBRAICALLY_DEPENDENT_MONO, SUBSET_TRANS])

  let ALGEBRAICALLY_INDEPENDENT_OVER_SUBRING_GENERATED_MONO ← prove
   r"!(h:A->B) k l s t d.
        algebraically_independent (subring_generated k t,l) h d /\ s SUBSET t
        ==> algebraically_independent (subring_generated k s,l) h d"
   (REWRITE_TAC [algebraically_independent] THEN
    MESON_TAC [ALGEBRAICALLY_DEPENDENT_OVER_SUBRING_GENERATED_MONO])

  let ALGEBRAICALLY_INDEPENDENT_IMP_TRANSCENDENTAL ← prove
   r"!(h:A->B) k l s x.
        field_extension (k,l) h /\
        algebraically_independent (k,l) h s /\ x IN s
        ==> transcendental_over (k,l) h x"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM ALGEBRAICALLY_INDEPENDENT_SING] THEN
    MATCH_MP_TAC ALGEBRAICALLY_INDEPENDENT_MONO THEN
    ASM_MESON_TAC [SING_SUBSET])

  let ALGEBRAICALLY_INDEPENDENT_IMP_DISJOINT ← prove
   r"!(h:A->B) k l s.
        field_extension (k,l) h /\ algebraically_independent (k,l) h s
        ==> DISJOINT (IMAGE h (ring_carrier k)) s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← SET_RULE (← q
     r"DISJOINT (IMAGE f r) s <=> !a. a IN r ==> ~(f a IN s)")] THEN
    ASM_MESON_TAC [ALGEBRAIC_OVER_IMAGE, transcendental_over,
                  ALGEBRAICALLY_INDEPENDENT_IMP_TRANSCENDENTAL])

  -- @@RETURN BEGIN
  return { ALGEBRAIC_SPAN_SPAN, ALGEBRAIC_SPAN_FINITARY, ALGEBRAIC_SPAN_EMPTY,
           ALGEBRAICALLY_INDEPENDENT_EMPTY, ALGEBRAICALLY_DEPENDENT_SING,
           ALGEBRAICALLY_INDEPENDENT_SING, ALGEBRAICALLY_DEPENDENT_MONO,
           ALGEBRAICALLY_DEPENDENT_OVER_SUBRING_GENERATED_MONO,
           ALGEBRAICALLY_INDEPENDENT_MONO,
           ALGEBRAICALLY_INDEPENDENT_OVER_SUBRING_GENERATED_MONO,
           ALGEBRAICALLY_INDEPENDENT_IMP_TRANSCENDENTAL,
           ALGEBRAICALLY_INDEPENDENT_IMP_DISJOINT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Algebraic dependence and span: finitary characterisation, insertion and   -/
/- span characterisations, and the exchange property.  (fieldtheory.ml       -/
/- 4192-4519)                                                                 -/
/- ------------------------------------------------------------------------- -/

structure AlgSpanDepIndep where
  -- @@FIELDS
  ALGEBRAICALLY_DEPENDENT_FINITARY : thm
  RING_MONOMORPHISM_POLY_EXTEND : thm
  ALGEBRAICALLY_DEPENDENT_FROM_INSERT : thm
  ALGEBRAICALLY_DEPENDENT_INSERT : thm
  ALGEBRAICALLY_INDEPENDENT_INSERT : thm
  ALGEBRAICALLY_DEPENDENT_SPAN : thm
  ALGEBRAICALLY_INDEPENDENT_SPAN : thm
  ALGEBRAIC_SPAN_EXCHANGE : thm
  ALGEBRAICALLY_SPANNING : thm
  deriving Inhabited

@[nospecialize]
def setupAlgSpanDepIndep [HolBase] (D : FieldTheoryDeps) (BSubfields : Subfields) (BSubfieldGenerated : SubfieldGenerated) (BFieldExtension : FieldExtension) (BAlgebraicExtension : AlgebraicExtension) (BAlgebraicExtensionProps : AlgebraicExtensionProps) (BAlgDepDefs : AlgDepDefs) (BAlgDepSpan : AlgDepSpan) :
    ExceptT String IO AlgSpanDepIndep := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, SET_RULE, SET_TAC, TAUT, .. } := D
  let { CARD_PSUBSET, CONJ_ASSOC, CONJ_SYM, EMPTY_SUBSET, .. } := D.core1
  let { FIELD_IMP_NONTRIVIAL_RING, FINITE_DELETE, FINITE_HAS_SIZE, FINITE_INSERT,
        FINITE_SUBSET, FORALL_IN_IMAGE, FORALL_UNWIND_THM1, FUN_EQ_THM, HAS_SIZE,
        IMAGE_POLY_EXTEND, .. } := D.core2
  let { IMP_CONJ, IMP_IMP, INSERT_SUBSET, IN_DELETE, IN_ELIM_THM, IN_INSERT, IN_SING,
        LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, .. } := D.core3
  let { MEMBER_NOT_EMPTY, MONO_EXISTS, NOT_EXISTS_THM, NOT_IMP, .. } := D.core4
  let { POLY_EXTEND_EQ, POLY_EXTEND_EXTEND, POLY_EXTEND_FROM_SUBRING_GENERATED,
        POLY_RING, POLY_RING_IN_FINITE_VARIABLES, POLY_SUBRING_GENERATED_CLAUSES,
        PSUBSET, RIGHT_FORALL_IMP_THM, RIGHT_IMP_FORALL_THM, .. } := D.core5
  let { RING_HOMOMORPHISM_POLY_EXTEND, RING_ISOMORPHISMS_ISOMORPHISM,
        RING_ISOMORPHISMS_POLY_POLY_RING, RING_ISOMORPHISM_IMP_HOMOMORPHISM,
        RING_ISOMORPHISM_IMP_MONOMORPHISM, RING_MONOMORPHISM_ALT,
        RING_MONOMORPHISM_EQ_0, RING_MONOMORPHISM_IMP_HOMOMORPHISM, .. } := D.core6
  let { SUBRING_GENERATED_BY_SUBRING_GENERATED, .. } := D.core7
  let { SUBRING_SUBRING_GENERATED, SUBSET, SUBSET_TRANS, SWAP_FORALL_THM, num_WF, .. } := D.core8
  let { num_WOP, poly_eval, poly_evaluate, ring_homomorphism, ring_isomorphisms, .. } := D.core9
  let { subfield_of, .. } := BSubfields
  let { FIELD_SUBFIELD_GENERATED, SUBRING_GENERATED_BY_SUBFIELD_GENERATED, .. } := BSubfieldGenerated
  let { FIELD_EXTENSION_REFL, FIELD_EXTENSION_SUBRING_GENERATED, field_extension, .. } := BFieldExtension
  let { ALGEBRAIC_OVER, ALGEBRAIC_OVER_SUBFIELD_SUBRING_GENERATED, algebraic_extension, .. } := BAlgebraicExtension
  let { ALGEBRAIC_OVER_RANGE, .. } := BAlgebraicExtensionProps
  let { ALGEBRAICALLY_DEPENDENT_IMP_SUBSET, ALGEBRAIC_SPAN, ALGEBRAIC_SPAN_MONO,
        ALGEBRAIC_SPAN_RESTRICT, ALGEBRAIC_SPAN_SUBSET, ALGEBRAIC_SPAN_SUPERSET,
        algebraically_dependent, algebraically_independent, algebraically_spanning, .. } := BAlgDepDefs
  let { ALGEBRAICALLY_DEPENDENT_MONO, ALGEBRAICALLY_INDEPENDENT_EMPTY,
        ALGEBRAIC_SPAN_FINITARY, ALGEBRAIC_SPAN_SPAN, .. } := BAlgDepSpan
  -- @@SCOPE END

  let ALGEBRAICALLY_DEPENDENT_FINITARY ← prove
   r"!(h:A->B) k l s.
        algebraically_dependent (k,l) h s <=>
        s SUBSET ring_carrier l /\
        ?t. FINITE t /\ t SUBSET s /\ algebraically_dependent (k,l) h t"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [ONCE_REWRITE_TAC [algebraically_dependent],
      MESON_TAC [ALGEBRAICALLY_DEPENDENT_MONO, algebraically_dependent]] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN (← q r"p:(B->num)->A") STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP POLY_RING_IN_FINITE_VARIABLES) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:B->bool") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    CONJ_TAC THENL [ASM SET_TAC [], EXISTS_TAC (← q r"p:(B->num)->A")] THEN
    ASM_MESON_TAC [← CONJUNCT2 POLY_RING])

  let RING_MONOMORPHISM_POLY_EXTEND ← prove
   r"!r r' s (h:A->B).
        ring_homomorphism(r,r') h /\ s SUBSET ring_carrier r'
        ==> (ring_monomorphism (poly_ring r s,r')
                               (poly_extend(r,r') h (\x. x)) <=>
             algebraically_independent (r,r') h s)"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [algebraically_independent] THEN
    ASM_REWRITE_TAC [RING_MONOMORPHISM_ALT, algebraically_dependent] THEN
    MATCH_MP_TAC (← TAUT (← q r"p /\ (q <=> q') ==> (p /\ q <=> q')")) THEN
    CONJ_TAC THENL [ALL_TAC, MESON_TAC []] THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_POLY_EXTEND THEN ASM SET_TAC [])

  let ALGEBRAICALLY_DEPENDENT_FROM_INSERT ← prove
   r"!(h:A->B) k l s a.
        field_extension(k,l) h /\ ~algebraically_dependent (k,l) h s
        ==> (algebraically_dependent (k,l) h (a INSERT s) <=>
             ~(a IN s) /\ s SUBSET ring_carrier l /\
             a IN algebraic_span (k,l) h s)"
   (← do
    let a5 ← SET_RULE (← q r"IMAGE (\x. x) s UNION t = t UNION s")
    let a4 ← MESON []
      (← q r"(!x. P x) ==> (?x. P x ==> Q x) ==> (?x. Q x)")
    let a3 ← SET_RULE (← q r"s UNION {a} = a INSERT s")
    let a2 ← SET_RULE (← q r"DISJOINT s {a} <=> ~(a IN s)")
    let aTAUT ← TAUT
     (← q r"(p' <=> p) /\ (q <=> q') ==> (q <=> p) ==> (p' <=> q')")
    let a1 ← SET_RULE (← q r"a IN s ==> a INSERT s = s")
    -- `W(fun (asl,w) -> let ft,gt = dest_pair(rand(lhand w)) in
    --     ABBREV_TAC(mk_eq(mk_var("f",type_of ft),ft)) THEN
    --     ABBREV_TAC(mk_eq(mk_var("g",type_of gt),gt)))`
    let abbrevFG : tactic := fun gl => tactic_of (do
      let w := gl.2
      let mkEq ← ExceptT.mk (mk_eq : IO _)
      let (ft, gt) ← liftExcept (do HolMath.Pair.dest_pair (← rand (← lhand w)))
      let eqf ← liftExcept (mkEq (mk_var "f" (type_of ft), ft))
      let eqg ← liftExcept (mkEq (mk_var "g" (type_of gt), gt))
      pure (ABBREV_TAC eqf THEN ABBREV_TAC eqg)) gl
    pure (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    ASM_CASES_TAC (← q r"(s:B->bool) SUBSET ring_carrier l") THEN
    ASM_REWRITE_TAC [] THENL
      [ALL_TAC, ASM_MESON_TAC [algebraically_dependent, INSERT_SUBSET]] THEN
    ASM_CASES_TAC (← q r"(a:B) IN ring_carrier l") THENL
     [ALL_TAC,
      ASM_REWRITE_TAC [algebraically_dependent, INSERT_SUBSET] THEN
      ASM SET_TAC [ALGEBRAIC_SPAN_SUBSET]] THEN
    ASM_CASES_TAC (← q r"(a:B) IN s") THEN
    ASM_SIMP_TAC [a1] THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"l:B ring", ← q r"s:B->bool",
                   ← q r"h:A->B"] RING_MONOMORPHISM_POLY_EXTEND) THEN
    ASM_REWRITE_TAC [algebraically_independent] THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"poly_extend (k,l) (h:A->B) (\x. x)",
                   ← q r"poly_ring (k:A ring) (s:B->bool)", ← q r"l:B ring",
                   ← q r"a:B", ← q r"a:B"] ALGEBRAIC_OVER) THEN
    MATCH_MP_TAC aTAUT THEN
    CONJ_TAC THENL
     [MP_TAC (← ISPECL
       [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"s:B->bool", ← q r"{a:B}",
        ← q r"\x:B. x"] POLY_EXTEND_EXTEND) THEN
      MP_TAC (← ISPECL [← q r"k:A ring", ← q r"s:B->bool", ← q r"{a:B}"]
        RING_ISOMORPHISMS_POLY_POLY_RING) THEN
      ASM_REWRITE_TAC [a2] THEN
      REWRITE_TAC [a3] THEN
      abbrevFG THEN
      FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
      REWRITE_TAC [] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
      DISCH_TAC THEN DISCH_TAC THEN
      ASM_REWRITE_TAC [algebraically_dependent, INSERT_SUBSET] THEN
      EQ_TAC THENL
       [DISCH_THEN (X_CHOOSE_THEN (← q r"p:(B->num)->A") STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"p:(B->num)->A")) THEN
        ASM_REWRITE_TAC [] THEN DISCH_TAC THEN EXISTS_TAC
         (← q r"(g:((B->num)->A)->(B->num)->(B->num)->A) p") THEN
        ASM_REWRITE_TAC [] THEN
        FIRST_X_ASSUM (fun th => tactic_of do pure (ASSUME_TAC (← elThm 1
          (CONJUNCTS (← GEN_REWRITE_RULE I [RING_ISOMORPHISMS_ISOMORPHISM] th))))) THEN
        FIRST_ASSUM (MP_TAC o MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM) THEN
        REWRITE_TAC [ring_homomorphism, SUBSET, FORALL_IN_IMAGE] THEN
        DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN ASM_SIMP_TAC [] THEN
        FIRST_ASSUM (MP_TAC o MATCH_MP RING_ISOMORPHISM_IMP_MONOMORPHISM) THEN
        DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          RING_MONOMORPHISM_EQ_0)) THEN
        ASM_SIMP_TAC [] THEN DISCH_THEN (K ALL_TAC),
        DISCH_THEN (X_CHOOSE_THEN (← q r"p:(B->num)->(B->num)->A") STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP a4) THEN
        EXISTS_TAC (← q r"(f:((B->num)->(B->num)->A)->(B->num)->A) p") THEN
        FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [ring_isomorphisms]) THEN
        REWRITE_TAC [ring_homomorphism, SUBSET, FORALL_IN_IMAGE] THEN
        STRIP_TAC THEN ASM_SIMP_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
        CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC]] THEN
      FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [← SYM th])) THEN
      MATCH_MP_TAC POLY_EXTEND_EQ THEN EXISTS_TAC (← q r"{a:B}") THEN
      ASM_SIMP_TAC [IN_SING],
      ASM_SIMP_TAC [ALGEBRAIC_SPAN, FIELD_IMP_NONTRIVIAL_RING, IN_ELIM_THM] THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"s:B->bool", ← q r"\x:B. x"]
            IMAGE_POLY_EXTEND) THEN
      REWRITE_TAC [a5] THEN
      ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      DISCH_THEN (MP_TAC o AP_TERM (← q r"subring_generated (l:B ring)")) THEN
      REWRITE_TAC [SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      REWRITE_TAC [POLY_EXTEND_FROM_SUBRING_GENERATED] THEN
      REWRITE_TAC [POLY_SUBRING_GENERATED_CLAUSES] THEN
      REWRITE_TAC [← GSYM poly_evaluate, ← GSYM poly_eval] THEN
      MATCH_MP_TAC ALGEBRAIC_OVER_RANGE THEN ASM_REWRITE_TAC []]))

  let ALGEBRAICALLY_DEPENDENT_INSERT ← prove
   r"!(h:A->B) k l s a.
        field_extension(k,l) h
        ==> (algebraically_dependent (k,l) h (a INSERT s) <=>
             a IN ring_carrier l /\ algebraically_dependent (k,l) h s \/
             ~(a IN s) /\ s SUBSET ring_carrier l /\
             a IN algebraic_span (k,l) h s)"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"algebraically_dependent (k,l) (h:A->B) s") THEN
    ASM_SIMP_TAC [ALGEBRAICALLY_DEPENDENT_FROM_INSERT] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP ALGEBRAICALLY_DEPENDENT_IMP_SUBSET) THEN
    ASM_CASES_TAC (← q r"(a:B) IN ring_carrier l") THEN ASM_REWRITE_TAC [] THENL
     [MATCH_MP_TAC ALGEBRAICALLY_DEPENDENT_MONO THEN ASM SET_TAC [],
      ASM_REWRITE_TAC [algebraically_dependent, INSERT_SUBSET] THEN
      ASM_CASES_TAC (← q r"(a:B) IN s") THENL [ASM SET_TAC [], ALL_TAC] THEN
      ASM SET_TAC [ALGEBRAIC_SPAN_SUBSET]])

  let ALGEBRAICALLY_INDEPENDENT_INSERT ← prove
   r"!(h:A->B) k l s a.
        field_extension(k,l) h
        ==> (algebraically_independent (k,l) h (a INSERT s) <=>
             algebraically_independent (k,l) h s /\
             a IN ring_carrier l /\
             (a IN s \/ ~(a IN algebraic_span (k,l) h s)))"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [algebraically_independent, ALGEBRAICALLY_DEPENDENT_INSERT] THEN
    ASM SET_TAC [ALGEBRAICALLY_DEPENDENT_IMP_SUBSET, ALGEBRAIC_SPAN_SUBSET])

  let ALGEBRAICALLY_DEPENDENT_SPAN ← prove
   r"!k l (h:A->B) s.
        field_extension(k,l) h
        ==> (algebraically_dependent (k,l) h s <=>
             s SUBSET ring_carrier l /\
             ?a. a IN s /\ a IN algebraic_span (k,l) h (s DELETE a))"
   (← do
    let b1 ← SET_RULE (← q r"a IN s ==> s DELETE a PSUBSET s")
    let b2 ← SET_RULE (← q r"a IN s ==> a INSERT (s DELETE a) = s")
    let b3 ← TAUT (← q r"p /\ q ==> (p <=> q)")
    let b4 ← SET_RULE
     (← q r"t SUBSET s DELETE a ==> (a INSERT t) DELETE a = t")
    let b5 ← MESON [HAS_SIZE]
     (← q r"((!s. FINITE s ==> P s) ==> (!s. P s)) /\
    (!n s. s HAS_SIZE n ==> P s)
    ==> !s. P s")
    pure (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC b5 THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I
          [ALGEBRAICALLY_DEPENDENT_FINITARY]) THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"t:B->bool") STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"t:B->bool")) THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:B") THEN
        ASM_MESON_TAC [ALGEBRAIC_SPAN_MONO, SUBSET, IN_DELETE],
        FIRST_X_ASSUM (MP_TAC o MATCH_MP ALGEBRAIC_SPAN_FINITARY) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"t:B->bool") STRIP_ASSUME_TAC) THEN
        MATCH_MP_TAC ALGEBRAICALLY_DEPENDENT_MONO THEN
        EXISTS_TAC (← q r"(a:B) INSERT t") THEN CONJ_TAC THENL
         [ALL_TAC, ASM SET_TAC []] THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(a:B) INSERT t")) THEN
        ASM_REWRITE_TAC [FINITE_INSERT] THEN DISCH_THEN SUBST1_TAC THEN
        CONJ_TAC THENL [ASM SET_TAC [], EXISTS_TAC (← q r"a:B")] THEN
        FIRST_ASSUM (SUBST1_TAC o MATCH_MP b4) THEN
        ASM_REWRITE_TAC [IN_INSERT]],
      MATCH_MP_TAC num_WF] THEN
    X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN
    X_GEN_TAC (← q r"s:B->bool") THEN REWRITE_TAC [HAS_SIZE] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    ASM_CASES_TAC (← q r"(s:B->bool) SUBSET ring_carrier l") THEN ASM_REWRITE_TAC []
    THENL [ALL_TAC, ASM_REWRITE_TAC [algebraically_dependent]] THEN
    ASM_CASES_TAC
     (← q r"?t. t PSUBSET s /\ algebraically_dependent (k,l) (h:A->B) t")
    THENL
     [FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"t:B->bool") STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC b3 THEN
      CONJ_TAC THENL [ASM SET_TAC [ALGEBRAICALLY_DEPENDENT_MONO], ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"CARD(t:B->bool)")) THEN
      ASM_SIMP_TAC [CARD_PSUBSET] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"t:B->bool")) THEN ANTS_TAC THENL
       [ASM_MESON_TAC [HAS_SIZE, PSUBSET, FINITE_SUBSET],
        ASM_REWRITE_TAC []] THEN
       DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
       MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:B") THEN
       ASM_MESON_TAC [ALGEBRAIC_SPAN_MONO, PSUBSET, SUBSET, IN_DELETE],
       FIRST_X_ASSUM (fun th => tactic_of do
         let _ ← SPEC (← q r"0") th; pure ALL_TAC)] THEN
    EQ_TAC THENL
     [ASM_CASES_TAC (← q r"s:B->bool = {}") THEN
      ASM_SIMP_TAC [← REWRITE_RULE [algebraically_independent, EMPTY_SUBSET]
                    ALGEBRAICALLY_INDEPENDENT_EMPTY] THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:B") THEN DISCH_TAC,
      DISCH_THEN (X_CHOOSE_THEN (← q r"a:B") STRIP_ASSUME_TAC)] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"s DELETE (a:B)", ← q r"a:B"]
          ALGEBRAICALLY_DEPENDENT_FROM_INSERT) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"s DELETE (a:B)") o
      GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    ASM_SIMP_TAC [b2] THEN
    ASM_SIMP_TAC [b1, IN_DELETE] THEN
    ASM SET_TAC []))

  let ALGEBRAICALLY_INDEPENDENT_SPAN ← prove
   r"!k l (h:A->B) s.
        field_extension(k,l) h
        ==> (algebraically_independent (k,l) h s <=>
             s SUBSET ring_carrier l /\
             !a. a IN s ==> ~(a IN algebraic_span (k,l) h (s DELETE a)))"
   (SIMP_TAC [algebraically_independent, ALGEBRAICALLY_DEPENDENT_SPAN] THEN
    SET_TAC [])

  let ALGEBRAIC_SPAN_EXCHANGE ← prove
   r"!(h:A->B) k l s a b.
        field_extension(k,l) h /\
        a IN algebraic_span (k,l) h (b INSERT s) /\
        ~(a IN algebraic_span (k,l) h s)
        ==> b IN algebraic_span (k,l) h (a INSERT s)"
   (← do
    let e8 ← TAUT (← q r"(p <=> q /\ r) ==> ~r ==> ~p")
    let e7 ← SET_RULE (← q r"!t. t SUBSET s /\ x IN t ==> x IN s")
    let e6 ← SET_RULE (← q r"s SUBSET t ==> x IN s ==> x IN t")
    let e5 ← SET_RULE (← q r"s DELETE a PSUBSET s <=> a IN s")
    let e4 ← TAUT (← q r"p ==> ~(q /\ r) <=> q ==> p ==> ~r")
    let e3 ← SET_RULE
     (← q r"ring_carrier l INTER (s:B->bool) SUBSET ring_carrier l")
    let e2 ← SET_RULE
     (← q r"b IN s ==> s INTER (b INSERT t) = b INSERT (s INTER t)")
    let e1 ← SET_RULE
     (← q r"~(b IN s) ==> s INTER (b INSERT t) = s INTER t")
    pure (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [ALGEBRAIC_SPAN_RESTRICT] THEN
    ASM_CASES_TAC (← q r"(b:B) IN ring_carrier l") THENL
     [ALL_TAC,
      ASM_MESON_TAC [e1]] THEN
    ASM_CASES_TAC (← q r"(a:B) IN ring_carrier l") THENL
     [ASM_SIMP_TAC [e2],
      ASM_MESON_TAC [ALGEBRAIC_SPAN_SUBSET, SUBSET]] THEN
    MP_TAC e3 THEN
    SPEC_TAC (← q r"ring_carrier l INTER (s:B->bool)", ← q r"s:B->bool") THEN
    X_GEN_TAC (← q r"s:B->bool") THEN
    ASM_CASES_TAC (← q r"a:B = b") THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"(a:B) IN s") THENL
     [MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"s:B->bool"]
          ALGEBRAIC_SPAN_SUPERSET) THEN
      ASM SET_TAC [],
      REPEAT STRIP_TAC] THEN
    SUBGOAL_THEN
     (← q r"?n t. t HAS_SIZE n /\ t SUBSET s /\
          a IN algebraic_span (k,l) (h:A->B) (b INSERT t)")
    MP_TAC THENL
     [FIRST_ASSUM (MP_TAC o MATCH_MP ALGEBRAIC_SPAN_FINITARY) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"t:B->bool") STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [← q r"CARD(t DELETE (b:B))", ← q r"t DELETE (b:B)"] THEN
      ASM_REWRITE_TAC [← GSYM FINITE_HAS_SIZE, FINITE_DELETE] THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring",
                     ← q r"t:B->bool", ← q r"(b:B) INSERT (t DELETE b)"]
          ALGEBRAIC_SPAN_MONO) THEN
      ASM SET_TAC [],
      GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
    REWRITE_TAC [LEFT_AND_EXISTS_THM, NOT_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [CONJ_SYM] HAS_SIZE, ← GSYM CONJ_ASSOC] THEN
    GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
    REWRITE_TAC [IMP_CONJ, FORALL_UNWIND_THM1] THEN
    X_GEN_TAC (← q r"t:B->bool") THEN REPLICATE_TAC 3 DISCH_TAC THEN
    REWRITE_TAC [RIGHT_IMP_FORALL_THM] THEN
    REWRITE_TAC [e4] THEN
    GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
    REWRITE_TAC [FORALL_UNWIND_THM1] THEN
    REWRITE_TAC [IMP_IMP, ← GSYM CONJ_ASSOC] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"(t:B->bool) SUBSET ring_carrier l") ASSUME_TAC THENL
     [ASM SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~algebraically_dependent (k,l) (h:A->B) t") ASSUME_TAC THENL
     [ASM_SIMP_TAC [ALGEBRAICALLY_DEPENDENT_SPAN] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"c:B") STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"t DELETE (c:B)")) THEN
      ASM_SIMP_TAC [CARD_PSUBSET, FINITE_DELETE, NOT_IMP, e5] THEN
      CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      FIRST_ASSUM (fun th => tactic_of do pure (ONCE_REWRITE_TAC
       [← GSYM (← MATCH_MP ALGEBRAIC_SPAN_SPAN th)])) THEN
      UNDISCH_TAC (← q r"a IN algebraic_span (k,l) (h:A->B) (b INSERT t)") THEN
      SPEC_TAC (← q r"a:B", ← q r"a:B") THEN REWRITE_TAC [← GSYM SUBSET] THEN
      MATCH_MP_TAC ALGEBRAIC_SPAN_MONO THEN
      TRANS_TAC SUBSET_TRANS (← q r"c INSERT (b INSERT (t DELETE c)):B->bool") THEN
      CONJ_TAC THENL [ASM SET_TAC [], ONCE_REWRITE_TAC [INSERT_SUBSET]] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC (← q r"c IN algebraic_span (k,l) (h:A->B) (t DELETE c)") THEN
        MATCH_MP_TAC e6 THEN
        MATCH_MP_TAC ALGEBRAIC_SPAN_MONO THEN ASM SET_TAC [],
        MATCH_MP_TAC ALGEBRAIC_SPAN_SUPERSET THEN ASM SET_TAC []],
      FIRST_X_ASSUM (fun th => tactic_of do
        let _ ← liftExcept (check (fun t => is_forall (concl t)) th); pure ALL_TAC)] THEN
    MATCH_MP_TAC e7 THEN
    EXISTS_TAC (← q r"algebraic_span (k,l) (h:A->B) (a INSERT t)") THEN CONJ_TAC THENL
     [MATCH_MP_TAC ALGEBRAIC_SPAN_MONO THEN ASM SET_TAC [], ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"(a:B) INSERT t", ← q r"b:B"]
          ALGEBRAICALLY_DEPENDENT_FROM_INSERT) THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"t:B->bool", ← q r"a:B"]
          ALGEBRAICALLY_DEPENDENT_FROM_INSERT) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o MATCH_MP e8) THEN
    ANTS_TAC THENL
     [MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"t:B->bool", ← q r"s:B->bool"]
          ALGEBRAIC_SPAN_MONO) THEN
      ASM SET_TAC [],
      DISCH_TAC THEN ASM_REWRITE_TAC []] THEN
    DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← EQ_IMP_RULE th).1)) THEN
    ANTS_TAC THEN
    ASM_SIMP_TAC [ALGEBRAICALLY_DEPENDENT_SPAN, INSERT_SUBSET] THEN
    EXISTS_TAC (← q r"a:B") THEN ASM_REWRITE_TAC [IN_INSERT] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"(b:B) INSERT t",
                   ← q r"(b INSERT a INSERT t) DELETE (a:B)"]
          ALGEBRAIC_SPAN_MONO) THEN
    ASM SET_TAC []))

  let ALGEBRAICALLY_SPANNING ← prove
   r"!(h:A->B) k l s.
        field_extension (k,l) h
        ==> (algebraically_spanning (k,l) (h:A->B) s <=>
             s SUBSET ring_carrier l /\
             algebraic_extension
              (subfield_generated l (IMAGE h (ring_carrier k) UNION s),l) I)"
   (← do
    let a1 ← TAUT (← q r"q ==> (p /\ r <=> p /\ q /\ r)")
    pure (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    REWRITE_TAC [algebraically_spanning, algebraic_extension] THEN
    ASM_SIMP_TAC [ALGEBRAIC_OVER_SUBFIELD_SUBRING_GENERATED,
                  FIELD_EXTENSION_REFL] THEN
    MATCH_MP_TAC a1 THEN
    ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    ASM_REWRITE_TAC [FIELD_EXTENSION_SUBRING_GENERATED] THEN
    REWRITE_TAC [subfield_of, SUBRING_SUBRING_GENERATED] THEN
    REWRITE_TAC [SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
    REWRITE_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED]))

  -- @@RETURN BEGIN
  return { ALGEBRAICALLY_DEPENDENT_FINITARY, RING_MONOMORPHISM_POLY_EXTEND,
           ALGEBRAICALLY_DEPENDENT_FROM_INSERT, ALGEBRAICALLY_DEPENDENT_INSERT,
           ALGEBRAICALLY_INDEPENDENT_INSERT, ALGEBRAICALLY_DEPENDENT_SPAN,
           ALGEBRAICALLY_INDEPENDENT_SPAN, ALGEBRAIC_SPAN_EXCHANGE,
           ALGEBRAICALLY_SPANNING }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- The algebraic matroid of a field extension, transcendence bases and       -/
/- the monomorphic-image invariance of algebraic dependence.  (fieldtheory.ml-/
/- 4521-4668)                                                                 -/
/- ------------------------------------------------------------------------- -/

structure AlgebraicMatroid where
  -- @@FIELDS
  algebraic_matroid : thm
  ALGEBRAIC_MATROID : thm
  ALGEBRAIC_MATROID_INDEPENDENT : thm
  ALGEBRAIC_MATROID_DEPENDENT : thm
  ALGEBRAIC_MATROID_SPANNING : thm
  ALGEBRAIC_MATROID_BASIS : thm
  TRANSCENDENCE_BASIS_EXISTS : thm
  ALGEBRAICALLY_SPANNING_CONTAINS_TRANSCENDENCE_BASIS : thm
  TRANSCENDENCE_BASES_CARD_EQ : thm
  ALGEBRAICALLY_DEPENDENT_MONOMORPHIC_IMAGE : thm
  deriving Inhabited

@[nospecialize]
def setupAlgebraicMatroid [HolBase] (D : FieldTheoryDeps) (BFieldExtension : FieldExtension) (BAlgDepDefs : AlgDepDefs) (BAlgDepSpan : AlgDepSpan) (BAlgSpanDepIndep : AlgSpanDepIndep) :
    ExceptT String IO AlgebraicMatroid := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_TAC, TAUT, new_definition, .. } := D
  let { ETA_AX, .. } := D.core1
  let { FIELD_IMP_NONTRIVIAL_RING, FUN_EQ_THM, IMAGE_ID, .. } := D.core2
  let { INJECTIVE_ON_LEFT_INVERSE, IN_POLY_RING_CARRIER, MATROID_BASES_CARD_EQ,
        MATROID_BASIS_EXISTS, .. } := D.core3
  let { MATROID_SPANNING_ALT, MATROID_SPANNING_CONTAINS_BASIS, PAIR_EQ, .. } := D.core4
  let { POLY_EXTEND, POLY_EXTEND_EQ, POLY_EXTEND_HOMOMORPHIC_IMAGE,
        POLY_EXTEND_REINDEX, .. } := D.core5
  let { RING_ISOMORPHISMS_ISOMORPHISM, RING_ISOMORPHISMS_POLY_REINDEX,
        RING_ISOMORPHISM_IMP_MONOMORPHISM, RING_MONOMORPHISM_EQ_0,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, .. } := D.core6
  let { SUBSET, matroid_basis, matroid_dependent, matroid_independent, matroid_set,
        matroid_span, matroid_tybij, .. } := D.core8
  let { o_DEF, ring_homomorphism, ring_monomorphism, .. } := D.core9
  let { field_extension, .. } := BFieldExtension
  let { ALGEBRAICALLY_DEPENDENT_IMP_SUBSET, ALGEBRAIC_SPAN, ALGEBRAIC_SPAN_MONO,
        ALGEBRAIC_SPAN_SUBSET, ALGEBRAIC_SPAN_SUPERSET, algebraically_dependent,
        algebraically_independent, algebraically_spanning, transcendence_basis, .. } := BAlgDepDefs
  let { ALGEBRAIC_SPAN_FINITARY, ALGEBRAIC_SPAN_SPAN, .. } := BAlgDepSpan
  let { ALGEBRAICALLY_DEPENDENT_SPAN, ALGEBRAIC_SPAN_EXCHANGE, .. } := BAlgSpanDepIndep
  -- @@SCOPE END

  let algebraic_matroid ← new_definition
   r"algebraic_matroid (k,l) (h:A->B) =
     matroid(ring_carrier l,algebraic_span (k,l) h)"

  let ALGEBRAIC_MATROID ← prove
   r"!(h:A->B) k l.
        field_extension (k,l) h
        ==> matroid_set(algebraic_matroid (k,l) h) = ring_carrier l /\
            matroid_span(algebraic_matroid (k,l) h) = algebraic_span (k,l) h"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC [matroid_set, matroid_span] THEN
    REWRITE_TAC [← GSYM PAIR_EQ, algebraic_matroid] THEN
    REWRITE_TAC [← GSYM (← CONJUNCT2 matroid_tybij)] THEN
    ASM_SIMP_TAC [ALGEBRAIC_SPAN_SUBSET, ALGEBRAIC_SPAN_SUPERSET,
                 ALGEBRAIC_SPAN_MONO, ALGEBRAIC_SPAN_SPAN,
                 ALGEBRAIC_SPAN_FINITARY, ALGEBRAIC_SPAN_EXCHANGE])

  let ALGEBRAIC_MATROID_INDEPENDENT ← prove
   r"!(h:A->B) k l.
        field_extension (k,l) h
        ==> (matroid_independent(algebraic_matroid (k,l) h) =
             algebraically_independent (k,l) h)"
   (SIMP_TAC [FUN_EQ_THM, matroid_independent, ALGEBRAIC_MATROID] THEN
    SIMP_TAC [ALGEBRAICALLY_DEPENDENT_SPAN, algebraically_independent] THEN
    MESON_TAC [])

  let ALGEBRAIC_MATROID_DEPENDENT ← prove
   r"!(h:A->B) k l.
        field_extension (k,l) h
        ==> (matroid_dependent(algebraic_matroid (k,l) h) =
             algebraically_dependent (k,l) h)"
   (REWRITE_TAC [FUN_EQ_THM] THEN
    MESON_TAC [matroid_dependent, algebraically_independent,
              ALGEBRAIC_MATROID_INDEPENDENT, ALGEBRAIC_MATROID,
              ALGEBRAICALLY_DEPENDENT_IMP_SUBSET])

  let ALGEBRAIC_MATROID_SPANNING ← prove
   r"!(h:A->B) k l.
        field_extension (k,l) h
        ==> (matroid_spanning(algebraic_matroid (k,l) h) =
             algebraically_spanning (k,l) h)"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [MATROID_SPANNING_ALT, ALGEBRAIC_MATROID, FUN_EQ_THM] THEN
    REWRITE_TAC [algebraically_spanning, SUBSET] THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    ASM_SIMP_TAC [ALGEBRAIC_SPAN, FIELD_IMP_NONTRIVIAL_RING] THEN
    SET_TAC [])

  let ALGEBRAIC_MATROID_BASIS ← prove
   r"!(h:A->B) k l.
        field_extension (k,l) h
        ==> (matroid_basis(algebraic_matroid (k,l) h) =
             transcendence_basis (k,l) h)"
   (SIMP_TAC [FUN_EQ_THM, matroid_basis, transcendence_basis,
             ALGEBRAIC_MATROID_INDEPENDENT, ALGEBRAIC_MATROID_SPANNING])

  let TRANSCENDENCE_BASIS_EXISTS ← prove
   r"!(h:A->B) k l.
        field_extension (k,l) h ==> ?b. transcendence_basis (k,l) h b"
   (SIMP_TAC [← GSYM ALGEBRAIC_MATROID_BASIS, MATROID_BASIS_EXISTS])

  let ALGEBRAICALLY_SPANNING_CONTAINS_TRANSCENDENCE_BASIS ← prove
   r"!(h:A->B) k l.
        field_extension (k,l) h /\ algebraically_spanning (k,l) h b
        ==> ?c. c SUBSET b /\ transcendence_basis (k,l) h c"
   (MESON_TAC [MATROID_SPANNING_CONTAINS_BASIS, ALGEBRAIC_MATROID_SPANNING,
              ALGEBRAIC_MATROID_BASIS])

  let TRANSCENDENCE_BASES_CARD_EQ ← prove
   r"!(h:A->B) k l b b'.
        field_extension (k,l) h /\
        transcendence_basis (k,l) h b /\ transcendence_basis (k,l) h b'
        ==> b =_c b'"
   (MESON_TAC [ALGEBRAIC_MATROID_BASIS, MATROID_BASES_CARD_EQ])

  let ALGEBRAICALLY_DEPENDENT_MONOMORPHIC_IMAGE ← prove
   r"!(f:A->B) (g:B->C) k l m s.
        s SUBSET ring_carrier l /\
        ring_homomorphism(k,l) f /\
        ring_monomorphism(l,m) g
        ==> (algebraically_dependent (k,m) (g o f) (IMAGE g s) <=>
             algebraically_dependent (k,l) f s)"
   (← do
    let a1 ← TAUT (← q r"p /\ q /\ (p ==> r) ==> p /\ q /\ r")
    pure (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o CONJUNCT2 o REWRITE_RULE [ring_monomorphism]) THEN
    REWRITE_TAC [INJECTIVE_ON_LEFT_INVERSE] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"h:C->B")) THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"s:B->bool", ← q r"IMAGE (g:B->C) s",
                   ← q r"g:B->C", ← q r"h:C->B"]
          RING_ISOMORPHISMS_POLY_REINDEX) THEN
    ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN STRIP_TAC THEN
    REWRITE_TAC [algebraically_dependent] THEN
    SUBGOAL_THEN (← q r"IMAGE (g:B->C) s SUBSET ring_carrier m") ASSUME_TAC THENL
     [RULE_ASSUM_TAC (REWRITE_RULE [ring_monomorphism, ring_homomorphism]) THEN
      ASM SET_TAC [],
      ASM_REWRITE_TAC []] THEN
    SUBGOAL_THEN
     (← q r"BIJ (g:B->C) s (IMAGE g s) /\ BIJ (h:C->B) (IMAGE g s) s")
    STRIP_ASSUME_TAC THENL
      [RULE_ASSUM_TAC (REWRITE_RULE [ring_monomorphism, ring_homomorphism]) THEN
      ASM SET_TAC [],
      ASM_REWRITE_TAC []] THEN
    FIRST_X_ASSUM (ASSUME_TAC o
      GEN_REWRITE_RULE I [RING_ISOMORPHISMS_ISOMORPHISM]) THEN
    EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q r"p:(C->num)->A") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"poly_reindex (k:A ring) p (g:B->C) (s:B->bool)
                             (IMAGE (g:B->C) s)") THEN
      FIRST_X_ASSUM (ASSUME_TAC o CONJUNCT1 o CONJUNCT2),

      DISCH_THEN (X_CHOOSE_THEN (← q r"q:(B->num)->A") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"poly_reindex (k:A ring) q (h:C->B)
                             (IMAGE (g:B->C) s) (s:B->bool)") THEN
      FIRST_X_ASSUM (ASSUME_TAC o CONJUNCT1)] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_ISOMORPHISM_IMP_MONOMORPHISM) THEN
    (MATCH_MP_TAC a1 THEN
     REPEAT CONJ_TAC THENL
      [FIRST_ASSUM (MP_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
       REWRITE_TAC [ring_homomorphism] THEN ASM SET_TAC [],
       ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0],
       ALL_TAC]) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [IN_POLY_RING_CARRIER])
    THENL
     [MP_TAC (← ISPECL [← q r"(g:B->C) o (f:A->B)", ← q r"k:A ring", ← q r"m:C ring", ← q r"s:B->bool",
                     ← q r"IMAGE (g:B->C) s", ← q r"p:(C->num)->A", ← q r"g:B->C", ← q r"\x:C. x"]
       POLY_EXTEND_REINDEX) THEN
      ASM_REWRITE_TAC [] THEN
      ABBREV_TAC (← q r"q = poly_reindex (k:A ring) (p:(C->num)->A) (g:B->C) (s:B->bool)
          (IMAGE (g:B->C) s)"),
      MP_TAC (← ISPECL [← q r"(g:B->C) o (f:A->B)", ← q r"k:A ring", ← q r"m:C ring",
                     ← q r"IMAGE (g:B->C) s", ← q r"s:B->bool", ← q r"q:(B->num)->A",
                     ← q r"h:C->B", ← q r"g:B->C"]
          POLY_EXTEND_REINDEX) THEN
       ASM_REWRITE_TAC [] THEN
       ABBREV_TAC
        (← q r"p = poly_reindex (k:A ring) (q:(B->num)->A) (h:C->B) (IMAGE g s) s")] THEN
    DISCH_THEN (fun th => tactic_of do pure (DISCH_TAC THEN MP_TAC th)) THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"l:B ring", ← q r"m:C ring",
                   ← q r"f:A->B", ← q r"s:B->bool", ← q r"\x:B. x", ← q r"g:B->C",
                   ← q r"q:(B->num)->A"]
      POLY_EXTEND_HOMOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC [o_DEF, IMAGE_ID, RING_MONOMORPHISM_IMP_HOMOMORPHISM] THENL
     [ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0, POLY_EXTEND], ALL_TAC] THEN
    REWRITE_TAC [ETA_AX] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN (← q r"(g:B->C) (ring_0 l) = ring_0 m") SUBST1_TAC THENL
     [ASM_MESON_TAC [ring_monomorphism, ring_homomorphism],
      DISCH_THEN (SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC POLY_EXTEND_EQ THEN
    EXISTS_TAC (← q r"IMAGE (g:B->C) s") THEN ASM SET_TAC []))

  -- @@RETURN BEGIN
  return { algebraic_matroid, ALGEBRAIC_MATROID, ALGEBRAIC_MATROID_INDEPENDENT,
           ALGEBRAIC_MATROID_DEPENDENT, ALGEBRAIC_MATROID_SPANNING,
           ALGEBRAIC_MATROID_BASIS, TRANSCENDENCE_BASIS_EXISTS,
           ALGEBRAICALLY_SPANNING_CONTAINS_TRANSCENDENCE_BASIS,
           TRANSCENDENCE_BASES_CARD_EQ, ALGEBRAICALLY_DEPENDENT_MONOMORPHIC_IMAGE }
  -- @@RETURN END

structure AlgebraicTrans where
  -- @@FIELDS
  ALGEBRAIC_OVER_MONOMORPHIC_IMAGE : thm
  ALGEBRAIC_SPAN_MONOMORPHIC_IMAGE : thm
  ALGEBRAICALLY_INDEPENDENT_TRANS : thm
  ALGEBRAICALLY_SPANNING_TRANS : thm
  TRANSCENDENCE_BASIS_TRANS : thm
  TRANSCENDENCE_BASIS_TOWER_LAW : thm
  TRANSCENDENCE_BASIS_CARD_LE_LEFT : thm
  TRANSCENDENCE_BASIS_CARD_LE_RIGHT : thm
  ALGEBRAIC_EXTENSION_SUBFIELDS_GENERATED : thm
  deriving Inhabited

@[nospecialize]
def setupAlgebraicTrans [HolBase] (D : FieldTheoryDeps) (BSubfieldGenerated : SubfieldGenerated) (BSubfieldGenerated1 : SubfieldGenerated1) (BFieldExtension : FieldExtension) (BAlgebraicExtension : AlgebraicExtension) (BAlgebraicExtensionProps : AlgebraicExtensionProps) (BAlgebraicField : AlgebraicField) (BAlgDepDefs : AlgDepDefs) (BAlgDepSpan : AlgDepSpan) (BAlgSpanDepIndep : AlgSpanDepIndep) (BAlgebraicMatroid : AlgebraicMatroid) :
    ExceptT String IO AlgebraicTrans := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, TAUT, .. } := D
  let { CARD_ADD_CONG, CARD_DISJOINT_UNION, CARD_EQ_IMAGE, CARD_EQ_IMP_LE,
        CARD_EQ_REFL, CARD_EQ_SYM, CARD_EQ_TRANS, CARD_LE_ADDL, CARD_LE_ADDR,
        CARD_LE_TRANS, CONJ_ASSOC, DISJOINT, EMPTY_SUBSET, EMPTY_UNION,
        EXISTS_FINITE_SUBSET_IMAGE, EXISTS_SUBSET_UNION, EXTENSION, .. } := D.core1
  let { FINITE_EMPTY, FINITE_UNION, FORALL_IN_IMAGE, FORALL_IN_UNION, IMAGE_CLAUSES,
        IMAGE_EQ_EMPTY, IMAGE_I, IMAGE_SUBSET, IMAGE_UNION, IMAGE_o, .. } := D.core2
  let { IMP_CONJ, IMP_CONJ_ALT, INTER_SUBSET, IN_ELIM_THM, IN_INSERT, I_DEF, I_O_ID,
        I_THM, .. } := D.core3
  let { MATROID_MINIMALLY_DEPENDENT_SUBSET, MATROID_SPANNING_ALT,
        MATROID_SPAN_UNION_LEFT, MEMBER_NOT_EMPTY, MONO_OR, NOT_EXISTS_THM,
        NOT_IN_EMPTY, .. } := D.core4
  let { RIGHT_AND_EXISTS_THM, RIGHT_EXISTS_AND_THM, .. } := D.core5
  let { RING_HOMOMORPHISM_INCLUSION, RING_MONOMORPHISM_BETWEEN_SUBRINGS,
        RING_MONOMORPHISM_EQ_0, RING_MONOMORPHISM_FROM_SUBRING_GENERATED,
        RING_MONOMORPHISM_I, RING_MONOMORPHISM_IMP_HOMOMORPHISM,
        RING_MONOMORPHISM_INCLUSION, .. } := D.core6
  let { SING_SUBSET, SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE,
        SUBRING_GENERATED_BY_SUBRING_GENERATED, .. } := D.core7
  let { SUBRING_GENERATED_MONO, SUBRING_GENERATED_UNION_LEFT, SUBSET, SUBSET_TRANS,
        UNION_EMPTY, UNION_SUBSET, matroid_spanning, .. } := D.core8
  let { ring_homomorphism, ring_monomorphism, .. } := D.core9
  let { FIELD_SUBFIELD_GENERATED, SUBFIELD_GENERATED_MINIMAL, SUBFIELD_GENERATED_MONO,
        SUBRING_GENERATED_BY_SUBFIELD_GENERATED, SUBRING_SUBSET_SUBFIELD_GENERATED, .. } := BSubfieldGenerated
  let { SUBFIELD_GENERATED_INC, SUBFIELD_OF_SUBFIELD_GENERATED_REV, .. } := BSubfieldGenerated1
  let { FIELD_EXTENSION_IMP_HOMOMORPHISM, FIELD_EXTENSION_IMP_MONOMORPHISM,
        FIELD_EXTENSION_IMP_SUBSET, FIELD_EXTENSION_TRANS, field_extension, .. } := BFieldExtension
  let { ALGEBRAIC_OVER_IMAGE, ALGEBRAIC_OVER_SUBRING_GENERATED,
        ALGEBRAIC_OVER_SUBRING_GENERATED_MONO, algebraic_extension, .. } := BAlgebraicExtension
  let { ALGEBRAIC_OVER_RANGE, .. } := BAlgebraicExtensionProps
  let { SUBFIELD_OF_ALGEBRAIC_OVER, .. } := BAlgebraicField
  let { ALGEBRAIC_SPAN_MONO, ALGEBRAIC_SPAN_RANGE, ALGEBRAIC_SPAN_SUBSET,
        TRANSCENDENCE_BASIS_IMP_SUBSET, algebraic_span, algebraically_independent,
        transcendence_basis, .. } := BAlgDepDefs
  let { ALGEBRAICALLY_DEPENDENT_MONO, ALGEBRAICALLY_DEPENDENT_SING,
        ALGEBRAICALLY_INDEPENDENT_IMP_DISJOINT, .. } := BAlgDepSpan
  let { ALGEBRAICALLY_DEPENDENT_SPAN, .. } := BAlgSpanDepIndep
  let { ALGEBRAICALLY_DEPENDENT_MONOMORPHIC_IMAGE, ALGEBRAIC_MATROID,
        ALGEBRAIC_MATROID_DEPENDENT, ALGEBRAIC_MATROID_SPANNING,
        TRANSCENDENCE_BASES_CARD_EQ, TRANSCENDENCE_BASIS_EXISTS, .. } := BAlgebraicMatroid
  -- @@SCOPE END

  let ALGEBRAIC_OVER_MONOMORPHIC_IMAGE ← prove
   r"!(f:A->B) (g:B->C) k l m z.
        z IN ring_carrier l /\
        ring_homomorphism(k,l) f /\
        ring_monomorphism(l,m) g
        ==> (algebraic_over (k,m) (g o f) (g z) <=>
             algebraic_over (k,l) f z)"
   (REWRITE_TAC [← GSYM ALGEBRAICALLY_DEPENDENT_SING, ← GSYM SING_SUBSET] THEN
    MESON_TAC [ALGEBRAICALLY_DEPENDENT_MONOMORPHIC_IMAGE, IMAGE_CLAUSES])

  let ALGEBRAIC_SPAN_MONOMORPHIC_IMAGE ← prove
   r"!(f:A->B) (g:B->C) k l m s.
        ring_homomorphism(k,l) f /\
        ring_monomorphism(l,m) g /\
        s SUBSET ring_carrier l
        ==> IMAGE g (algebraic_span (k,l) f s) =
            IMAGE g (ring_carrier l) INTER
            algebraic_span (k,m) (g o f) (IMAGE g s)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC (← SET_RULE
     (← q r"(!x. x IN u ==> (g x IN v <=> x IN s)) /\ s SUBSET u
      ==> IMAGE g s = IMAGE g u INTER v")) THEN
    REWRITE_TAC [ALGEBRAIC_SPAN_SUBSET] THEN
    X_GEN_TAC (← q r"z:B") THEN DISCH_TAC THEN
    REWRITE_TAC [algebraic_span] THEN
    REWRITE_TAC [IN_INSERT, IN_ELIM_THM] THEN BINOP_TAC THENL
     [ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0], ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"I:B->B", ← q r"g:B->C",
      ← q r"subring_generated l (IMAGE (f:A->B) (ring_carrier k) UNION s)",
      ← q r"l:B ring", ← q r"m:C ring", ← q r"z:B"]
     ALGEBRAIC_OVER_MONOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC [← REWRITE_RULE [← GSYM I_DEF] RING_HOMOMORPHISM_INCLUSION] THEN
    ASM_REWRITE_TAC [I_O_ID] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC [ALGEBRAIC_OVER_RANGE,
                 RING_MONOMORPHISM_FROM_SUBRING_GENERATED] THEN
    MP_TAC (← ISPECL
     [← q r"l:B ring", ← q r"m:C ring", ← q r"g:B->C",
      ← q r"IMAGE (f:A->B) (ring_carrier k) UNION s"]
          SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM, UNION_SUBSET] THEN
    ANTS_TAC THENL
     [RULE_ASSUM_TAC (REWRITE_RULE [ring_homomorphism]) THEN ASM SET_TAC [],
      DISCH_THEN (SUBST1_TAC o SYM)] THEN
    REWRITE_TAC [SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
    REWRITE_TAC [IMAGE_o, IMAGE_UNION])

  let ALGEBRAICALLY_INDEPENDENT_TRANS ← prove
   r"!(f:A->B) (g:B->C) k l m s t.
        field_extension(k,l) f /\ field_extension(l,m) g /\
        algebraically_independent (k,l) f s /\
        algebraically_independent (l,m) g t
        ==> DISJOINT (IMAGE g s) t /\
            algebraically_independent (k,m) (g o f) (IMAGE g s UNION t)"
   (← do
    let a3 ← TAUT
      (← q r"p /\ q /\ (r /\ s) /\ t <=> r /\ p /\ s /\ q /\ t")
    let a2 ← TAUT (← q r"p /\ q /\ r <=> q /\ p /\ r")
    let a1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [algebraically_independent] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [UNION_SUBSET, CONJ_ASSOC] THEN
    MATCH_MP_TAC a1 THEN CONJ_TAC THENL
     [MP_TAC (← ISPECL [← q r"g:B->C", ← q r"l:B ring", ← q r"m:C ring", ← q r"t:C->bool"]
          ALGEBRAICALLY_INDEPENDENT_IMP_DISJOINT) THEN
      ASM_REWRITE_TAC [algebraically_independent] THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET)) THEN
      ASM SET_TAC [],
      STRIP_TAC] THEN
    MP_TAC (← ISPECL [← q r"f:A->B", ← q r"g:B->C", ← q r"k:A ring", ← q r"l:B ring", ← q r"m:C ring"]
          FIELD_EXTENSION_TRANS) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    ASM_SIMP_TAC [← GSYM ALGEBRAIC_MATROID_DEPENDENT] THEN
    DISCH_THEN (MP_TAC o MATCH_MP MATROID_MINIMALLY_DEPENDENT_SUBSET) THEN
    ASM_SIMP_TAC [ALGEBRAIC_MATROID_DEPENDENT] THEN
    ONCE_REWRITE_TAC [a2] THEN
    REWRITE_TAC [EXISTS_SUBSET_UNION, FINITE_UNION] THEN
    ONCE_REWRITE_TAC [a3] THEN
    REWRITE_TAC [RIGHT_EXISTS_AND_THM, EXISTS_FINITE_SUBSET_IMAGE] THEN
    REWRITE_TAC [FORALL_IN_UNION, FORALL_IN_IMAGE] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM, NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"s':B->bool", ← q r"t':C->bool"] THEN
    ASM_CASES_TAC (← q r"t':C->bool = {}") THEN
    ASM_REWRITE_TAC [EMPTY_UNION, IMAGE_EQ_EMPTY, UNION_EMPTY] THEN
    REWRITE_TAC [NOT_IN_EMPTY, EMPTY_SUBSET, FINITE_EMPTY] THEN STRIP_TAC THENL
     [MP_TAC (← ISPECL
       [← q r"f:A->B", ← q r"g:B->C", ← q r"k:A ring", ← q r"l:B ring", ← q r"m:C ring", ← q r"s:B->bool"]
       ALGEBRAICALLY_DEPENDENT_MONOMORPHIC_IMAGE) THEN
      ASM_SIMP_TAC [FIELD_EXTENSION_IMP_MONOMORPHISM,
                   FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
      ASM_MESON_TAC [IMAGE_SUBSET, ALGEBRAICALLY_DEPENDENT_MONO],
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"c:C")) THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"c:C")) THEN ASM_REWRITE_TAC [] THEN
      ASM_SIMP_TAC [ALGEBRAIC_MATROID] THEN DISCH_TAC THEN
      UNDISCH_TAC (← q r"~algebraically_dependent (l,m) (g:B->C) t") THEN
      ASM_SIMP_TAC [ALGEBRAICALLY_DEPENDENT_SPAN] THEN
      EXISTS_TAC (← q r"c:C") THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [algebraic_span]) THEN
      REWRITE_TAC [algebraic_span, IN_INSERT, IN_ELIM_THM] THEN
      MATCH_MP_TAC MONO_OR THEN REWRITE_TAC [] THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT]
        ALGEBRAIC_OVER_SUBRING_GENERATED_MONO) THEN
      REWRITE_TAC [IMAGE_o] THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET)) THEN
      ASM SET_TAC []]))

  let ALGEBRAICALLY_SPANNING_TRANS ← prove
   r"!(f:A->B) (g:B->C) k l m s t.
      field_extension (k,l) f /\ algebraically_spanning (k,l) f s /\
      field_extension (l,m) g /\ algebraically_spanning (l,m) g t
      ==> algebraically_spanning (k,m) (g o f) (IMAGE g s UNION t)"
   (← do
    let a2 ← SET_RULE (← q r"s SUBSET s' ==> s UNION t SUBSET s' UNION t")
    let a1 ← SET_RULE (← q r"s = t ==> a INSERT s SUBSET a INSERT t")
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"field_extension (k,m) ((g:B->C) o (f:A->B))") ASSUME_TAC THENL
     [ASM_MESON_TAC [FIELD_EXTENSION_TRANS], ALL_TAC] THEN
    ASM_SIMP_TAC [← GSYM ALGEBRAIC_MATROID_SPANNING, MATROID_SPANNING_ALT] THEN
    MAP_EVERY UNDISCH_TAC
     [← q r"algebraically_spanning (l,m) (g:B->C) t",
      ← q r"algebraically_spanning (k,l) (f:A->B) s"] THEN
    ASM_SIMP_TAC [← GSYM ALGEBRAIC_MATROID_SPANNING, matroid_spanning] THEN
    wPart (fun c => funpowM 4 rand c) (fun c => do lhand (← rand c)) MATROID_SPAN_UNION_LEFT THEN
    ASM_SIMP_TAC [ALGEBRAIC_MATROID, UNION_SUBSET] THEN
    DISCH_THEN (fun th => tactic_of do pure (STRIP_TAC THEN STRIP_TAC THEN MP_TAC th)) THEN
    SUBGOAL_THEN (← q r"IMAGE (g:B->C) s SUBSET ring_carrier m") ASSUME_TAC THENL
     [REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET)) THEN
      ASM SET_TAC [],
      ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC] THEN
    TRANS_TAC SUBSET_TRANS
     (← q r"algebraic_span (k,m) (g o f)
       (IMAGE (g:B->C) (algebraic_span (k,l) (f:A->B) s) UNION t)") THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [← SYM th])) THEN
      ONCE_REWRITE_TAC [ALGEBRAIC_SPAN_RANGE] THEN
      REWRITE_TAC [algebraic_span] THEN
      MATCH_MP_TAC a1 THEN
      REWRITE_TAC [IMAGE_I, EXTENSION, IN_ELIM_THM] THEN
      X_GEN_TAC (← q r"z:C") THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [SUBRING_GENERATED_UNION_LEFT] THEN AP_TERM_TAC THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET)) THEN
      REWRITE_TAC [IMAGE_o] THEN ASM SET_TAC [],
      MATCH_MP_TAC ALGEBRAIC_SPAN_MONO THEN
      MATCH_MP_TAC a2 THEN
      ASM_SIMP_TAC [ALGEBRAIC_SPAN_MONOMORPHIC_IMAGE, INTER_SUBSET,
                   FIELD_EXTENSION_IMP_MONOMORPHISM,
                   RING_MONOMORPHISM_IMP_HOMOMORPHISM]]))

  let TRANSCENDENCE_BASIS_TRANS ← prove
   r"!(f:A->B) (g:B->C) k l m s t.
      field_extension (k,l) f /\ transcendence_basis (k,l) f s /\
      field_extension (l,m) g /\ transcendence_basis (l,m) g t
      ==> DISJOINT (IMAGE g s) t /\
          transcendence_basis (k,m) (g o f) (IMAGE g s UNION t)"
   (REWRITE_TAC [transcendence_basis] THEN
    MESON_TAC [ALGEBRAICALLY_INDEPENDENT_TRANS, ALGEBRAICALLY_SPANNING_TRANS])

  let TRANSCENDENCE_BASIS_TOWER_LAW ← prove
   r"!(f:A->B) (g:B->C) k l m b c d.
     field_extension (k,l) f /\ field_extension (l,m) g /\
     transcendence_basis (k,l) f b /\
     transcendence_basis (l,m) g c /\
     transcendence_basis (k,m) (g o f) d
     ==> b +_c c =_c d"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL
     [← q r"(g:B->C) o (f:A->B)", ← q r"k:A ring", ← q r"m:C ring",
      ← q r"IMAGE (g:B->C) b UNION c", ← q r"d:C->bool"]
     TRANSCENDENCE_BASES_CARD_EQ) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [FIELD_EXTENSION_TRANS, TRANSCENDENCE_BASIS_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] CARD_EQ_TRANS)] THEN
    ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN
    TRANS_TAC CARD_EQ_TRANS (← q r"IMAGE (g:B->C) b +_c (c:C->bool)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_DISJOINT_UNION THEN
      ASM_MESON_TAC [TRANSCENDENCE_BASIS_TRANS, DISJOINT],
      MATCH_MP_TAC CARD_ADD_CONG THEN REWRITE_TAC [CARD_EQ_REFL] THEN
      MATCH_MP_TAC CARD_EQ_IMAGE] THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP TRANSCENDENCE_BASIS_IMP_SUBSET)) THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP
      FIELD_EXTENSION_IMP_MONOMORPHISM)) THEN
    REWRITE_TAC [ring_monomorphism] THEN ASM SET_TAC [])

  let TRANSCENDENCE_BASIS_CARD_LE_LEFT ← prove
   r"!(f:A->B) (g:B->C) k l m b c.
     field_extension (k,l) f /\ field_extension (l,m) g /\
     transcendence_basis (k,l) f b /\
     transcendence_basis (k,m) (g o f) c
     ==> b <=_c c"
   (ASM_MESON_TAC [TRANSCENDENCE_BASIS_EXISTS, TRANSCENDENCE_BASIS_TOWER_LAW,
                  CARD_LE_ADDR, CARD_LE_ADDL, CARD_LE_TRANS, CARD_EQ_IMP_LE])

  let TRANSCENDENCE_BASIS_CARD_LE_RIGHT ← prove
   r"!(f:A->B) (g:B->C) k l m b c.
     field_extension (k,l) f /\ field_extension (l,m) g /\
     transcendence_basis (l,m) g b /\
     transcendence_basis (k,m) (g o f) c
     ==> b <=_c c"
   (ASM_MESON_TAC [TRANSCENDENCE_BASIS_EXISTS, TRANSCENDENCE_BASIS_TOWER_LAW,
                  CARD_LE_ADDR, CARD_LE_ADDL, CARD_LE_TRANS, CARD_EQ_IMP_LE])

  let ALGEBRAIC_EXTENSION_SUBFIELDS_GENERATED ← prove
   r"!(f:A->B) (g:B->C) k l m s.
      algebraic_extension (k,l) f /\
      field_extension (l,m) g /\
      s SUBSET ring_carrier m
      ==> algebraic_extension
           (subfield_generated m (IMAGE (g o f) (ring_carrier k) UNION s),
            subfield_generated m (IMAGE g (ring_carrier l) UNION s)) I"
   (← do
    let a2 ← SET_RULE
      (← q r"(!x. x IN s ==> P x) <=> s SUBSET {x | P x}")
    let a1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    pure (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    SUBGOAL_THEN (← q r"field k /\ ring_monomorphism(k,l) (f:A->B)")
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [algebraic_extension, field_extension], ALL_TAC] THEN
    REWRITE_TAC [algebraic_extension] THEN
    MATCH_MP_TAC a1 THEN CONJ_TAC THENL
     [ASM_SIMP_TAC [field_extension, FIELD_SUBFIELD_GENERATED] THEN
      ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
      MATCH_MP_TAC RING_MONOMORPHISM_BETWEEN_SUBRINGS THEN
      REWRITE_TAC [IMAGE_I, RING_MONOMORPHISM_I, IMAGE_o] THEN
      MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN
      RULE_ASSUM_TAC (REWRITE_RULE [ring_monomorphism, ring_homomorphism]) THEN
      ASM SET_TAC [],
      DISCH_TAC THEN REWRITE_TAC [a2]] THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC [UNION_SUBSET],
      MATCH_MP_TAC SUBFIELD_OF_SUBFIELD_GENERATED_REV THEN
      EXISTS_TAC (← q r"IMAGE (g:B->C) (ring_carrier l) UNION s") THEN
      MATCH_MP_TAC SUBFIELD_OF_ALGEBRAIC_OVER THEN ASM_REWRITE_TAC []] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
      X_GEN_TAC (← q r"b:B") THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
      MATCH_MP_TAC ALGEBRAIC_OVER_SUBRING_GENERATED THEN
      REWRITE_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED, IMAGE_I] THEN
      REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC [field_extension, FIELD_SUBFIELD_GENERATED] THEN
        ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
        REWRITE_TAC [I_DEF, RING_MONOMORPHISM_INCLUSION],
        MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN REWRITE_TAC [IMAGE_o] THEN
        RULE_ASSUM_TAC (REWRITE_RULE [ring_monomorphism, ring_homomorphism]) THEN
        ASM SET_TAC [],
        ALL_TAC,
        MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN
        RULE_ASSUM_TAC (REWRITE_RULE [ring_monomorphism, ring_homomorphism]) THEN
        ASM SET_TAC []] THEN
      FIRST_ASSUM (MP_TAC o CONJUNCT2 o REWRITE_RULE [algebraic_extension]) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"b:B")) THEN
      ASM_SIMP_TAC [ALGEBRAIC_OVER_RANGE] THEN DISCH_TAC THEN
      MP_TAC (← ISPECL
       [← q r"I:B->B", ← q r"g:B->C",
        ← q r"subring_generated l (IMAGE (f:A->B) (ring_carrier k))",
        ← q r"l:B ring", ← q r"m:C ring", ← q r"b:B"]
          ALGEBRAIC_OVER_MONOMORPHIC_IMAGE) THEN
      ASM_SIMP_TAC [← REWRITE_RULE [← GSYM I_DEF] RING_HOMOMORPHISM_INCLUSION] THEN
      ASM_SIMP_TAC [RING_MONOMORPHISM_FROM_SUBRING_GENERATED,
                   ALGEBRAIC_OVER_RANGE, I_O_ID] THEN
      ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT]
        ALGEBRAIC_OVER_SUBRING_GENERATED_MONO) THEN
      MP_TAC (← ISPECL
       [← q r"l:B ring", ← q r"m:C ring", ← q r"g:B->C",
        ← q r"IMAGE (f:A->B) (ring_carrier k)"]
          SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
        RULE_ASSUM_TAC (REWRITE_RULE [ring_monomorphism, ring_homomorphism]) THEN
        ASM SET_TAC [],
        DISCH_THEN (SUBST1_TAC o SYM)] THEN
      wPart (fun c => do rand c) (fun c => do rand c) SUBRING_SUBSET_SUBFIELD_GENERATED THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] SUBSET_TRANS) THEN
      MATCH_MP_TAC SUBRING_GENERATED_MONO THEN
      REWRITE_TAC [IMAGE_o] THEN SET_TAC [],
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM I_THM] THEN
      MATCH_MP_TAC ALGEBRAIC_OVER_IMAGE THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN
      REWRITE_TAC [IMAGE_o] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [ring_monomorphism, ring_homomorphism]) THEN
      ASM SET_TAC []]))

  -- @@RETURN BEGIN
  return { ALGEBRAIC_OVER_MONOMORPHIC_IMAGE, ALGEBRAIC_SPAN_MONOMORPHIC_IMAGE,
           ALGEBRAICALLY_INDEPENDENT_TRANS, ALGEBRAICALLY_SPANNING_TRANS,
           TRANSCENDENCE_BASIS_TRANS, TRANSCENDENCE_BASIS_TOWER_LAW,
           TRANSCENDENCE_BASIS_CARD_LE_LEFT, TRANSCENDENCE_BASIS_CARD_LE_RIGHT,
           ALGEBRAIC_EXTENSION_SUBFIELDS_GENERATED }
  -- @@RETURN END

structure AlgebraicOverExt where
  -- @@FIELDS
  ALGEBRAIC_SPAN_OVER_ALGEBRAIC_EXTENSION : thm
  ALGEBRAICALLY_DEPENDENT_OVER_ALGEBRAIC_EXTENSION : thm
  ALGEBRAICALLY_INDEPENDENT_OVER_ALGEBRAIC_EXTENSION : thm
  ALGEBRAICALLY_SPANNING_SPAN : thm
  ALGEBRAICALLY_SPANNING_OVER_ALGEBRAIC_EXTENSION : thm
  TRANSCENDENCE_BASIS_OVER_ALGEBRAIC_EXTENSION : thm
  ALGEBRAICALLY_INDEPENDENT_CARD_LE_SPANNING : thm
  FINITELY_GENERATED_ALGEBRAICALLY_INDEPENDENT_IMP_FINITE : thm
  TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_SPANNING : thm
  TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_INDEPENDENT : thm
  deriving Inhabited

@[nospecialize]
def setupAlgebraicOverExt [HolBase] (D : FieldTheoryDeps) (BSubfieldGenerated : SubfieldGenerated) (BFieldExtension : FieldExtension) (BFiniteExtension : FiniteExtension) (BAlgebraicExtension : AlgebraicExtension) (BAlgebraicExtMisc : AlgebraicExtMisc) (BAlgebraicField : AlgebraicField) (BAlgDepDefs : AlgDepDefs) (BAlgSpanDepIndep : AlgSpanDepIndep) (BAlgebraicMatroid : AlgebraicMatroid) (BAlgebraicTrans : AlgebraicTrans) :
    ExceptT String IO AlgebraicOverExt := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, .. } := D
  let { CARD_LE_FINITE, EXTENSION, .. } := D.core1
  let { FIELD_IMP_NONTRIVIAL_RING, .. } := D.core2
  let { IMP_CONJ, IN_ELIM_THM, I_O_ID, MATROID_INDEPENDENT_CARD_LE_SPANNING, .. } := D.core3
  let { RING_MONOMORPHISM_FROM_SUBRING_GENERATED, RING_MONOMORPHISM_I, .. } := D.core6
  let { SUBSET_ANTISYM_EQ, .. } := D.core8
  let { FIELD_SUBFIELD_GENERATED, SUBRING_GENERATED_BY_SUBFIELD_GENERATED, .. } := BSubfieldGenerated
  let { FIELD_EXTENSION_TRANS, field_extension, .. } := BFieldExtension
  let { finitely_generated_extension, .. } := BFiniteExtension
  let { ALGEBRAIC_IMP_FIELD_EXTENSION, .. } := BAlgebraicExtension
  let { ALGEBRAIC_EXTENSION_REFL, .. } := BAlgebraicExtMisc
  let { ALGEBRAIC_OVER_ALGEBRAIC_EXTENSION, .. } := BAlgebraicField
  let { ALGEBRAIC_SPAN, ALGEBRAIC_SPAN_FIELD, ALGEBRAIC_SPAN_RESTRICT,
        ALGEBRAIC_SPAN_SUBSET, algebraically_independent, algebraically_spanning,
        transcendence_basis, .. } := BAlgDepDefs
  let { ALGEBRAICALLY_DEPENDENT_SPAN, ALGEBRAICALLY_SPANNING, .. } := BAlgSpanDepIndep
  let { ALGEBRAIC_MATROID_INDEPENDENT, ALGEBRAIC_MATROID_SPANNING, .. } := BAlgebraicMatroid
  let { ALGEBRAIC_EXTENSION_SUBFIELDS_GENERATED, .. } := BAlgebraicTrans
  -- @@SCOPE END

  let ALGEBRAIC_SPAN_OVER_ALGEBRAIC_EXTENSION ← prove
   r"!(f:A->B) (g:B->C) k l m s.
        algebraic_extension (k,l) f /\
        field_extension (l,m) g
        ==> algebraic_span (k,m) (g o f) s = algebraic_span (l,m) g s"
   (← do
    let a1 ← SET_RULE
      (← q r"(ring_carrier m INTER s:C->bool) SUBSET ring_carrier m")
    pure (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [ALGEBRAIC_SPAN_RESTRICT] THEN
    MP_TAC a1 THEN
    SPEC_TAC (← q r"ring_carrier m INTER s:C->bool", ← q r"s:C->bool") THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    ASM_SIMP_TAC [ALGEBRAIC_SPAN_FIELD] THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"z:C") THEN
    MP_TAC (← ISPECL
     [← q r"I:C->C", ← q r"I:C->C",
      ← q r"subfield_generated m
         (IMAGE ((g:B->C) o (f:A->B)) (ring_carrier k) UNION s)",
      ← q r"subfield_generated m (IMAGE (g:B->C) (ring_carrier l) UNION s)",
      ← q r"m:C ring", ← q r"z:C"] ALGEBRAIC_OVER_ALGEBRAIC_EXTENSION) THEN
    REWRITE_TAC [I_O_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC [ALGEBRAIC_EXTENSION_SUBFIELDS_GENERATED] THEN
    ASM_SIMP_TAC [field_extension, FIELD_SUBFIELD_GENERATED] THEN
    ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    ASM_SIMP_TAC [RING_MONOMORPHISM_FROM_SUBRING_GENERATED,
                 RING_MONOMORPHISM_I]))

  let ALGEBRAICALLY_DEPENDENT_OVER_ALGEBRAIC_EXTENSION ← prove
   r"!(f:A->B) (g:B->C) k l m s.
        algebraic_extension (k,l) f /\
        field_extension (l,m) g
        ==> (algebraically_dependent (k,m) (g o f) s <=>
             algebraically_dependent (l,m) g s)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A->B", ← q r"g:B->C", ← q r"k:A ring", ← q r"l:B ring", ← q r"m:C ring"]
          FIELD_EXTENSION_TRANS) THEN
    ASM_SIMP_TAC [ALGEBRAIC_IMP_FIELD_EXTENSION, ALGEBRAICALLY_DEPENDENT_SPAN,
                 ALGEBRAIC_SPAN_OVER_ALGEBRAIC_EXTENSION])

  let ALGEBRAICALLY_INDEPENDENT_OVER_ALGEBRAIC_EXTENSION ← prove
   r"!(f:A->B) (g:B->C) k l m s.
        algebraic_extension (k,l) f /\
        field_extension (l,m) g
        ==> (algebraically_independent (k,m) (g o f) s <=>
             algebraically_independent (l,m) g s)"
   (SIMP_TAC [algebraically_independent,
             ALGEBRAICALLY_DEPENDENT_OVER_ALGEBRAIC_EXTENSION])

  let ALGEBRAICALLY_SPANNING_SPAN ← prove
   r"!(h:A->B) k l s.
        ~(trivial_ring l)
        ==> (algebraically_spanning (k,l) h s <=>
             s SUBSET ring_carrier l /\
             algebraic_span (k,l) h s = ring_carrier l)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, ALGEBRAIC_SPAN_SUBSET] THEN
    ASM_SIMP_TAC [algebraically_spanning, ALGEBRAIC_SPAN] THEN SET_TAC [])

  let ALGEBRAICALLY_SPANNING_OVER_ALGEBRAIC_EXTENSION ← prove
   r"!(f:A->B) (g:B->C) k l m s.
        algebraic_extension (k,l) f /\
        field_extension (l,m) g
        ==> (algebraically_spanning (k,m) (g o f) s <=>
             algebraically_spanning (l,m) g s)"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    ASM_SIMP_TAC [ALGEBRAICALLY_SPANNING_SPAN, FIELD_IMP_NONTRIVIAL_RING,
                 ALGEBRAIC_SPAN_OVER_ALGEBRAIC_EXTENSION])

  let TRANSCENDENCE_BASIS_OVER_ALGEBRAIC_EXTENSION ← prove
   r"!(f:A->B) (g:B->C) k l m s.
        algebraic_extension (k,l) f /\
        field_extension (l,m) g
        ==> (transcendence_basis (k,m) (g o f) s <=>
             transcendence_basis (l,m) g s)"
   (SIMP_TAC [transcendence_basis,
             ALGEBRAICALLY_INDEPENDENT_OVER_ALGEBRAIC_EXTENSION,
             ALGEBRAICALLY_SPANNING_OVER_ALGEBRAIC_EXTENSION])

  let ALGEBRAICALLY_INDEPENDENT_CARD_LE_SPANNING ← prove
   r"!(h:A->B) k l b c.
        field_extension (k,l) h /\
        algebraically_independent (k,l) h b /\ algebraically_spanning (k,l) h c
        ==> b <=_c c"
   (REWRITE_TAC [IMP_CONJ] THEN
    SIMP_TAC [← GSYM ALGEBRAIC_MATROID_INDEPENDENT,
             ← GSYM ALGEBRAIC_MATROID_SPANNING] THEN
    MESON_TAC [MATROID_INDEPENDENT_CARD_LE_SPANNING])

  let FINITELY_GENERATED_ALGEBRAICALLY_INDEPENDENT_IMP_FINITE ← prove
   r"!(f:A->B) k l b.
        finitely_generated_extension (k,l) f /\
        algebraically_independent (k,l) f b
        ==> FINITE b"
   (REPEAT GEN_TAC THEN REWRITE_TAC [finitely_generated_extension] THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"c:B->bool") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          CARD_LE_FINITE)) THEN
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ]
          ALGEBRAICALLY_INDEPENDENT_CARD_LE_SPANNING)) THEN
    ASM_SIMP_TAC [ALGEBRAICALLY_SPANNING, ALGEBRAIC_EXTENSION_REFL] THEN
    ASM_MESON_TAC [field_extension])

  let TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_SPANNING ← prove
   r"!(h:A->B) k l s.
        transcendence_basis (k,l) h s ==> algebraically_spanning (k,l) h s"
   (SIMP_TAC [transcendence_basis])

  let TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_INDEPENDENT ← prove
   r"!(h:A->B) k l s.
        transcendence_basis (k,l) h s ==> algebraically_independent (k,l) h s"
   (SIMP_TAC [transcendence_basis])

  -- @@RETURN BEGIN
  return { ALGEBRAIC_SPAN_OVER_ALGEBRAIC_EXTENSION,
           ALGEBRAICALLY_DEPENDENT_OVER_ALGEBRAIC_EXTENSION,
           ALGEBRAICALLY_INDEPENDENT_OVER_ALGEBRAIC_EXTENSION,
           ALGEBRAICALLY_SPANNING_SPAN, ALGEBRAICALLY_SPANNING_OVER_ALGEBRAIC_EXTENSION,
           TRANSCENDENCE_BASIS_OVER_ALGEBRAIC_EXTENSION,
           ALGEBRAICALLY_INDEPENDENT_CARD_LE_SPANNING,
           FINITELY_GENERATED_ALGEBRAICALLY_INDEPENDENT_IMP_FINITE,
           TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_SPANNING,
           TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_INDEPENDENT }
  -- @@RETURN END

structure TotallyTranscendental where
  -- @@FIELDS
  TOTALLY_TRANSCENDENTAL_EXTENSION : thm
  TOTALLY_TRANSCENDENTAL_EXTENSION_ALT : thm
  deriving Inhabited

@[nospecialize]
def setupTotallyTranscendental [HolBase] (D : FieldTheoryDeps) (BSubfields : Subfields) (BSubfieldGenerated : SubfieldGenerated) (BSubfieldGenerated1 : SubfieldGenerated1) (BSubfieldGenerated2 : SubfieldGenerated2) (BSubfieldQuotients : SubfieldQuotients) (BFieldExtension : FieldExtension) (BAlgebraicExtension : AlgebraicExtension) (BAlgebraicExtensionProps : AlgebraicExtensionProps) (BAlgebraicField : AlgebraicField) (BAlgDepDefs : AlgDepDefs) (BAlgDepSpan : AlgDepSpan) (BAlgSpanDepIndep : AlgSpanDepIndep) :
    ExceptT String IO TotallyTranscendental := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, FIELD_TAC, MESON, SET_RULE, SET_TAC, TAUT, .. } := D
  let { CARRIER_SUBRING_GENERATED_SUBRING, CONJ_ASSOC, CONTRAPOS_THM,
        EXISTS_SUBSET_UNION, .. } := D.core1
  let { FINITE_INDUCT_STRONG, FINITE_UNION, FORALL_IN_IMAGE, FORALL_IN_INSERT,
        FUN_EQ_THM, IMAGE_I, IMAGE_POLY_EVAL, .. } := D.core2
  let { IMP_CONJ, IN_ELIM_THM, IN_INSERT, I_DEF, I_O_ID, LEFT_IMP_EXISTS_THM, .. } := D.core3
  let { MONO_EXISTS, NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY, POLY_0, POLY_CONST,
        POLY_CONST_SUBRING_GENERATED, POLY_EVAL, POLY_EVAL_0, POLY_EVAL_CONST, .. } := D.core4
  let { POLY_EXTEND_FROM_SUBRING_GENERATED, POLY_MUL_CONST, POLY_RING,
        POLY_SUBRING_GENERATED_CLAUSES, RIGHT_FORALL_IMP_THM, RING_0,
        RING_CARRIER_POLY_SUBRING_GENERATED_MONO, .. } := D.core5
  let { RING_HOMOMORPHISM_INCLUSION, RING_HOMOMORPHISM_MUL,
        RING_HOMOMORPHISM_POLY_EXTEND, RING_HOMOMORPHISM_SUB, RING_INV_0,
        RING_MONOMORPHISM_BETWEEN_SUBRINGS, RING_MONOMORPHISM_I, RING_MUL, .. } := D.core6
  let { RING_MUL_RZERO, RING_SUB, RING_SUB_EQ_0, SUBRING_GENERATED, .. } := D.core7
  let { SUBRING_GENERATED_INC_GEN, SUBSET, SUBSET_ANTISYM_EQ, UNION_EMPTY, .. } := D.core8
  let { poly_eval, poly_evaluate, ring_div, ring_homomorphism, ring_monomorphism,
        ring_polynomial, ring_powerseries, subring_of, .. } := D.core9
  let { CARRIER_SUBFIELD_OF, IN_SUBFIELD_0, IN_SUBFIELD_INV, IN_SUBFIELD_MUL,
        SUBFIELD_IMP_SUBRING_OF, subfield_of, .. } := BSubfields
  let { CARRIER_SUBFIELD_GENERATED_SUBFIELD, FIELD_SUBFIELD_GENERATED,
        RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBFIELD_GENERATED_MONO,
        SUBFIELD_SUBFIELD_GENERATED, SUBRING_GENERATED_BY_SUBFIELD_GENERATED, .. } := BSubfieldGenerated
  let { SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED, SUBFIELD_GENERATED_IDEMPOT,
        SUBFIELD_GENERATED_INC_GEN, SUBFIELD_GENERATED_UNION_RIGHT, .. } := BSubfieldGenerated1
  let { SUBFIELD_OF_MONOMORPHIC_IMAGE, .. } := BSubfieldGenerated2
  let { IN_SUBFIELD_GENERATED_FINITARY, SUBFIELD_GENERATED_QUOTIENTS, .. } := BSubfieldQuotients
  let { FIELD_EXTENSION_REFL, FIELD_EXTENSION_SUBRING_GENERATED, field_extension, .. } := BFieldExtension
  let { ALGEBRAIC_OVER_IMAGE, ALGEBRAIC_OVER_IN_CARRIER,
        ALGEBRAIC_OVER_SUBFIELD_GENERATED, ALGEBRAIC_OVER_SUBFIELD_SUBRING_GENERATED,
        ALGEBRAIC_OVER_SUBRING_GENERATED_MONO, TRANSCENDENTAL_OVER_IN_CARRIER,
        algebraic_extension, algebraic_over, transcendental_over, .. } := BAlgebraicExtension
  let { ALGEBRAIC_OVER_RANGE, .. } := BAlgebraicExtensionProps
  let { ALGEBRAIC_OVER_ALGEBRAIC_EXTENSION,
        ALGEBRAIC_OVER_SUBFIELD_GENERATED_ALGEBRAIC, .. } := BAlgebraicField
  let { ALGEBRAIC_SPAN_FIELD, .. } := BAlgDepDefs
  let { ALGEBRAICALLY_INDEPENDENT_MONO, .. } := BAlgDepSpan
  let { ALGEBRAICALLY_INDEPENDENT_INSERT, .. } := BAlgSpanDepIndep
  -- @@SCOPE END

  let TOTALLY_TRANSCENDENTAL_EXTENSION ← (do
    let baselemma ← (do
      let b2 ← SET_RULE (← q r"s UNION {a} = a INSERT s")
      let b1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
      prove
       r"!k l a z:A.
              field l /\ k subfield_of l /\
              transcendental_over (subfield_generated l k,l) I a /\
              algebraic_over (subfield_generated l k,l) I z /\
              z IN ring_carrier(subfield_generated l (a INSERT k))
              ==> z IN k"
       (REPEAT STRIP_TAC THEN
        MP_TAC (← ISPECL [← q r"l:A ring", ← q r"a INSERT k:A->bool", ← q r"z:A"]
              SUBFIELD_GENERATED_QUOTIENTS) THEN
        ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, LEFT_IMP_EXISTS_THM] THEN
        FIRST_ASSUM (ASSUME_TAC o MATCH_MP TRANSCENDENTAL_OVER_IN_CARRIER) THEN
        ASM_SIMP_TAC [← GSYM IMAGE_POLY_EVAL, SUBFIELD_IMP_SUBRING_OF] THEN
        REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE] THEN
        X_GEN_TAC (← q r"p:(1->num)->A") THEN STRIP_TAC THEN
        X_GEN_TAC (← q r"q:(1->num)->A") THEN STRIP_TAC THEN REPEAT DISCH_TAC THEN
        ASM_CASES_TAC (← q r"(z:A) IN k") THEN ASM_REWRITE_TAC [] THEN
        MP_TAC (← ISPECL
         [← q r"I:A->A", ← q r"I:A->A",
          ← q r"subfield_generated l k:A ring", ← q r"subfield_generated l ((z:A) INSERT k)",
          ← q r"l:A ring", ← q r"a:A"]
         ALGEBRAIC_OVER_ALGEBRAIC_EXTENSION) THEN
        REWRITE_TAC [I_O_ID, NOT_IMP] THEN REPEAT CONJ_TAC THENL
         [REWRITE_TAC [algebraic_extension] THEN
          MATCH_MP_TAC b1 THEN CONJ_TAC THENL
           [ASM_SIMP_TAC [field_extension, FIELD_SUBFIELD_GENERATED] THEN
            ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
            MATCH_MP_TAC RING_MONOMORPHISM_BETWEEN_SUBRINGS THEN
            REWRITE_TAC [IMAGE_I, RING_MONOMORPHISM_I] THEN
            MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN SET_TAC [],
            DISCH_THEN (MP_TAC o SPEC (← q r"{z:A}") o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
              ALGEBRAIC_OVER_SUBFIELD_GENERATED_ALGEBRAIC)) THEN
            ASM_REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY, IMAGE_I] THEN
            ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
            REWRITE_TAC [b2,
                        SUBFIELD_GENERATED_IDEMPOT] THEN
            DISCH_THEN MATCH_MP_TAC THEN
            MATCH_MP_TAC ALGEBRAIC_OVER_SUBFIELD_GENERATED THEN
            ASM_SIMP_TAC [IMAGE_I, CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
            ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
            ASM_REWRITE_TAC [FIELD_EXTENSION_SUBRING_GENERATED] THEN
            ASM_SIMP_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED,
                         CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
            SET_TAC []],
          ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
          ASM_REWRITE_TAC [FIELD_EXTENSION_SUBRING_GENERATED] THEN
          ASM_SIMP_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED,
                       SUBFIELD_SUBFIELD_GENERATED],
          FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [transcendental_over]) THEN
          SIMP_TAC [] THEN DISCH_THEN (K ALL_TAC)] THEN
        ASM_SIMP_TAC [ALGEBRAIC_OVER_SUBFIELD_SUBRING_GENERATED,
                     FIELD_EXTENSION_REFL] THEN
        ASM_REWRITE_TAC [algebraic_over] THEN
        EXISTS_TAC
         (← q r"ring_sub (poly_ring (subring_generated l (z INSERT k)) (:1)) p
                   (ring_mul ((poly_ring (subring_generated l (z INSERT k)) (:1)))
                             (poly_const (subring_generated l (z INSERT k)) (z:A))
                             q)") THEN
        MP_TAC (← ISPECL [← q r"l:A ring", ← q r"k:A->bool", ← q r"(z:A) INSERT k", ← q r"(:1)"]
              RING_CARRIER_POLY_SUBRING_GENERATED_MONO) THEN
        ANTS_TAC THENL [SET_TAC [], GEN_REWRITE_TAC LAND_CONV [SUBSET]] THEN
        DISCH_THEN (fun th => tactic_of do pure (
          MP_TAC (← SPEC (← q r"q:(1->num)->A") th) THEN MP_TAC (← SPEC (← q r"p:(1->num)->A") th))) THEN
        ASM_REWRITE_TAC [] THEN DISCH_TAC THEN DISCH_TAC THEN
        MP_TAC (← ISPECL [← q r"subring_generated l (z INSERT k):A ring", ← q r"(:1)", ← q r"z:A"]
              POLY_CONST) THEN
        DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← EQ_IMP_RULE th).2)) THEN ANTS_TAC THENL
         [MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
          ASM SET_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET],
          DISCH_TAC] THEN
        ASM_SIMP_TAC [RING_SUB, RING_MUL, RING_0, RING_SUB_EQ_0] THEN
        FIRST_ASSUM (ASSUME_TAC o MATCH_MP ALGEBRAIC_OVER_IN_CARRIER) THEN
        CONJ_TAC THENL
         [ALL_TAC,
          MP_TAC (← ISPECL [← q r"subring_generated l (z INSERT k):A ring", ← q r"l:A ring",
                         ← q r"(:1)", ← q r"I:A->A", ← q r"(\v. a):1->A"]
              RING_HOMOMORPHISM_POLY_EXTEND) THEN
          ASM_REWRITE_TAC [← REWRITE_RULE [← GSYM I_DEF] RING_HOMOMORPHISM_INCLUSION] THEN
          DISCH_TAC THEN
          FIRST_ASSUM (fun th => tactic_of do
            pure (ASM_SIMP_TAC [← MATCH_MP RING_HOMOMORPHISM_SUB th, RING_MUL])) THEN
          FIRST_ASSUM (fun th => tactic_of do
            pure (ASM_SIMP_TAC [← MATCH_MP RING_HOMOMORPHISM_MUL th])) THEN
          REWRITE_TAC [POLY_EXTEND_FROM_SUBRING_GENERATED] THEN
          REWRITE_TAC [← GSYM poly_evaluate, ← GSYM poly_eval] THEN
          REWRITE_TAC [POLY_SUBRING_GENERATED_CLAUSES] THEN
          ASM_SIMP_TAC [POLY_CONST_SUBRING_GENERATED, POLY_EVAL_CONST] THEN
          EXPAND_TAC "z" THEN
          UNDISCH_TAC (← q r"~(poly_eval l (q:(1->num)->A) a = ring_0 l)") THEN
          MP_TAC (← ISPECL [← q r"l:A ring", ← q r"q:(1->num)->A", ← q r"a:A"] POLY_EVAL) THEN
          MP_TAC (← ISPECL [← q r"l:A ring", ← q r"p:(1->num)->A", ← q r"a:A"] POLY_EVAL) THEN
          FIELD_TAC] THEN
        DISCH_THEN (MP_TAC o AP_TERM
         (← q r"\p. p IN ring_carrier
                 (poly_ring (subring_generated l k:A ring) (:1))")) THEN
        ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [POLY_RING, IN_ELIM_THM] THEN STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [ring_polynomial]) THEN
        REWRITE_TAC [ring_powerseries, ← GSYM CONJ_ASSOC] THEN
        DISCH_THEN (MP_TAC o CONJUNCT1) THEN
        SUBGOAL_THEN (← q r"~(z:A = ring_0 l)")
          (fun th => ASSUME_TAC th THEN MP_TAC th) THENL
          [ASM_MESON_TAC [IN_SUBFIELD_0], EXPAND_TAC "z"] THEN
        ASM_CASES_TAC (← q r"q:(1->num)->A = poly_0 l") THENL
         [REWRITE_TAC [ring_div] THEN ASM_SIMP_TAC [POLY_EVAL_0] THEN
          ASM_SIMP_TAC [RING_MUL_RZERO, RING_INV_0, POLY_EVAL],
          DISCH_THEN (K ALL_TAC) THEN POP_ASSUM MP_TAC] THEN
        ASM_REWRITE_TAC [] THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [FUN_EQ_THM] THEN
        REWRITE_TAC [POLY_0, NOT_FORALL_THM] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"m:1->num") THEN DISCH_TAC THEN
        MP_TAC (← ISPECL
         [← q r"subring_generated l (z INSERT k):A ring",
          ← q r"z:A", ← q r"q:(1->num)->A"] POLY_MUL_CONST) THEN
        ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [IN_INSERT],
            RULE_ASSUM_TAC (REWRITE_RULE [POLY_RING, IN_ELIM_THM]) THEN
            ASM_REWRITE_TAC []],
          DISCH_THEN SUBST1_TAC] THEN
        ASM_SIMP_TAC [← CONJUNCT2 SUBRING_GENERATED, CARRIER_SUBRING_GENERATED_SUBRING,
                     SUBFIELD_IMP_SUBRING_OF] THEN
        UNDISCH_TAC (← q r"~((z:A) IN k)") THEN REWRITE_TAC [CONTRAPOS_THM] THEN
        DISCH_TAC THEN
        SUBGOAL_THEN (← q r"(q:(1->num)->A) m IN k /\ q m IN ring_carrier l")
        STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC
           (← q r"q IN ring_carrier (poly_ring (subring_generated l k:A ring) (:1))") THEN
          REWRITE_TAC [POLY_RING, IN_ELIM_THM,
                      ring_polynomial, ring_powerseries] THEN
          RULE_ASSUM_TAC (REWRITE_RULE [subfield_of]) THEN
          ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING] THEN
          RULE_ASSUM_TAC (REWRITE_RULE [subring_of]) THEN ASM SET_TAC [],
          ALL_TAC] THEN
        SUBGOAL_THEN
         (← q r"z:A = ring_mul l (ring_inv l (q m)) (ring_mul l z (q(m:1->num)))")
        SUBST1_TAC THENL
         [UNDISCH_TAC (← q r"~((q:(1->num)->A) m = ring_0 l)") THEN
          UNDISCH_TAC (← q r"(q:(1->num)->A) m IN ring_carrier l") THEN
          UNDISCH_TAC (← q r"(z:A) IN ring_carrier l") THEN
          UNDISCH_TAC (← q r"field(l:A ring)") THEN
          SPEC_TAC (← q r"(q:(1->num)->A) m", ← q r"qm:A") THEN
          POP_ASSUM_LIST (K ALL_TAC) THEN FIELD_TAC,
          MATCH_MP_TAC IN_SUBFIELD_MUL THEN ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC IN_SUBFIELD_INV THEN ASM_REWRITE_TAC []]))
    let m6 ← SET_RULE (← q r"{a} UNION s UNION b = s UNION a INSERT b")
    let m5 ← SET_RULE (← q r"a INSERT s = {a} UNION s")
    let m4 ← SET_RULE (← q r"s = t ==> x IN s ==> x IN t")
    let m3 ← SET_RULE (← q r"x IN s ==> s SUBSET t ==> x IN t")
    let m2 ← TAUT (← q r"p /\ q /\ r <=> q /\ p /\ r")
    let m1 ← MESON []
     (← q r"(!f k l x. (!b. FINITE b ==> P f k l b x) ==> !b. P f k l b x) /\
        (!b. FINITE b ==> !f k l x. P f k l b x)
         ==> !f k l b x. P f k l b x")
    prove
     r"!(f:A->B) k l b x.
            field_extension (k,l) f /\
            algebraically_independent (k,l) f b /\
            algebraic_over (k,l) f x /\
            x IN ring_carrier
                  (subfield_generated l (IMAGE f (ring_carrier k) UNION b))
            ==> x IN IMAGE f (ring_carrier k)"
     (MATCH_MP_TAC m1 THEN
      CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN
        MP_TAC (← ISPECL [← q r"l:B ring", ← q r"IMAGE (f:A->B) (ring_carrier k) UNION b",
                       ← q r"x:B"] IN_SUBFIELD_GENERATED_FINITARY) THEN
        ANTS_TAC THENL
         [ASM_MESON_TAC [field_extension, FIELD_SUBFIELD_GENERATED],
          ONCE_REWRITE_TAC [m2]] THEN
        REWRITE_TAC [EXISTS_SUBSET_UNION, FINITE_UNION] THEN
        REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [← q r"u:B->bool", ← q r"c:B->bool"] THEN STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"c:B->bool")) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
        CONJ_TAC THENL
         [ASM_MESON_TAC [ALGEBRAICALLY_INDEPENDENT_MONO], ALL_TAC] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP m3) THEN
        MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN ASM SET_TAC [],
        ALL_TAC] THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
       [REPEAT GEN_TAC THEN
        REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        MATCH_MP_TAC m4 THEN
        REWRITE_TAC [UNION_EMPTY] THEN
        MATCH_MP_TAC CARRIER_SUBFIELD_GENERATED_SUBFIELD THEN
        MATCH_MP_TAC SUBFIELD_OF_MONOMORPHIC_IMAGE THEN
        ASM_MESON_TAC [CARRIER_SUBFIELD_OF, field_extension],
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [← q r"a:B", ← q r"b:B->bool"] THEN STRIP_TAC THEN
      MAP_EVERY X_GEN_TAC [← q r"f:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"y:B"] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC [ALGEBRAICALLY_INDEPENDENT_INSERT] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC (← q r"l:B ring") THEN
      ASM_REWRITE_TAC [] THEN
      FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
      MP_TAC (← ISPECL
       [← q r"ring_carrier (subfield_generated l
           (IMAGE (f:A->B) (ring_carrier k) UNION b))",
        ← q r"l:B ring", ← q r"a:B", ← q r"y:B"] baselemma) THEN
      ASM_REWRITE_TAC [SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN
      DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED],
        UNDISCH_TAC (← q r"~(a IN algebraic_span (k,l) (f:A->B) b)") THEN
        ASM_SIMP_TAC [ALGEBRAIC_SPAN_FIELD, transcendental_over, IN_ELIM_THM,
                     SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED],
        ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
        MATCH_MP_TAC ALGEBRAIC_OVER_SUBRING_GENERATED_MONO THEN
        EXISTS_TAC (← q r"IMAGE (f:A->B) (ring_carrier k)") THEN
        ASM_SIMP_TAC [← GSYM ALGEBRAIC_OVER_RANGE] THEN
        REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
        RULE_ASSUM_TAC (REWRITE_RULE [ring_monomorphism, ring_homomorphism]) THEN
        ASM SET_TAC [],
        ONCE_REWRITE_TAC [m5] THEN
        REWRITE_TAC [SUBFIELD_GENERATED_UNION_RIGHT] THEN
        ASM_REWRITE_TAC [m6]]))

  let TOTALLY_TRANSCENDENTAL_EXTENSION_ALT ← prove
   r"!(f:A->B) k l b.
          field_extension (k,l) f /\
          algebraically_independent (k,l) f b /\
          subfield_generated l (IMAGE f (ring_carrier k) UNION b) = l
          ==> {x | algebraic_over (k,l) f x} = IMAGE f (ring_carrier k)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN REWRITE_TAC [IN_ELIM_THM] THEN
    CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [ALGEBRAIC_OVER_IMAGE]] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC TOTALLY_TRANSCENDENTAL_EXTENSION THEN
    MAP_EVERY EXISTS_TAC [← q r"l:B ring", ← q r"b:B->bool"] THEN
    ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [ALGEBRAIC_OVER_IN_CARRIER])

  -- @@RETURN BEGIN
  return { TOTALLY_TRANSCENDENTAL_EXTENSION, TOTALLY_TRANSCENDENTAL_EXTENSION_ALT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- A loose end about finitely generated extensions that seems to involve a   -/
/- bit more work than expected. This proof is mainly taken from that of      -/
/- theorem 24.9 in Isaacs: "Algebra: A Graduate Course".                     -/
/- ------------------------------------------------------------------------- -/

structure FinitelyGeneratedTransEq where
  -- @@FIELDS
  FINITELY_GENERATED_EXTENSION_TRANS_EQ : thm
  deriving Inhabited

@[nospecialize]
def setupFinitelyGeneratedTransEq [HolBase] (D : FieldTheoryDeps) (BSubfields : Subfields) (BSubfieldGenerated : SubfieldGenerated) (BSubfieldGenerated1 : SubfieldGenerated1) (BFieldExtension : FieldExtension) (BRingMatroid : RingMatroid) (BLinearAlgebra : LinearAlgebra) (BFinitary : Finitary) (BFiniteExtension : FiniteExtension) (BAlgebraicExtension : AlgebraicExtension) (BAlgebraicExtensionProps : AlgebraicExtensionProps) (BAlgebraicExtMisc : AlgebraicExtMisc) (BAlgDepDefs : AlgDepDefs) (BAlgDepSpan : AlgDepSpan) (BAlgSpanDepIndep : AlgSpanDepIndep) (BAlgebraicMatroid : AlgebraicMatroid) (BAlgebraicTrans : AlgebraicTrans) (BAlgebraicOverExt : AlgebraicOverExt) (BTotallyTranscendental : TotallyTranscendental) :
    ExceptT String IO FinitelyGeneratedTransEq := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, MESON, SET_RULE, SET_TAC, .. } := D
  let { AND_FORALL_THM, CARD_LE_FINITE, CONTRAPOS_THM, .. } := D.core1
  let { FINITE_IMAGE, FINITE_IMAGE_INJ_EQ, FINITE_NUMSEG_LT, FINITE_SUBSET_NUMSEG,
        FORALL_AND_THM, FORALL_FINITE_SUBSET_IMAGE, FORALL_IN_IMAGE, FUN_EQ_THM,
        IMAGE_CLAUSES, IMAGE_I, IMAGE_SUBSET, IMAGE_o, .. } := D.core2
  let { IMP_CONJ, INFINITE, IN_ELIM_THM, IN_NUMSEG, IN_UNION, I_O_ID,
        LEFT_IMP_EXISTS_THM, LE_SUC_LT, LT, LT_CASES, MATROID_DIMENSION_GE_FINITE_CARD, .. } := D.core3
  let { MATROID_INDEPENDENT_FINITARY, MATROID_INDEPENDENT_MONO, MONO_AND, MONO_EXISTS,
        NOT_LE, NOT_LT, NUMSEG_CLAUSES_LT, .. } := D.core4
  let { PSUBSET, PSUBSET_ALT, PSUBSET_TRANS, .. } := D.core5
  let { RING_HOMOMORPHISM_BETWEEN_SUBRINGS, RING_MONOMORPHISM_BETWEEN_SUBRINGS,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MONOMORPHISM_INTO_SUBRING, .. } := D.core6
  let { SIMPLE_IMAGE_GEN, SKOLEM_THM, .. } := D.core7
  let { SUBRING_GENERATED_RING_CARRIER, SUBSET, SUBSET_ANTISYM, SUBSET_REFL,
        SUBSET_TRANS, SUBSET_UNIV, TRANSITIVE_STEPWISE_LT, UNION_SUBSET, WF_REC,
        WF_num, WLOG_LT, num_INDUCTION, num_INFINITE, num_WF, .. } := D.core8
  let { o_THM, ring_homomorphism, ring_monomorphism, subring_of, .. } := D.core9
  let { subfield_of, .. } := BSubfields
  let { CARRIER_SUBFIELD_GENERATED_SUBFIELD, FIELD_SUBFIELD_GENERATED,
        RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBFIELD_GENERATED_MINIMAL,
        SUBFIELD_GENERATED_MONO, SUBFIELD_SUBFIELD_GENERATED,
        SUBFIELD_SUBFIELD_GENERATED_EQ, SUBRING_GENERATED_BY_SUBFIELD_GENERATED, .. } := BSubfieldGenerated
  let { SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED, SUBFIELD_GENERATED_IDEMPOT,
        SUBFIELD_GENERATED_INC, SUBFIELD_GENERATED_INC_GEN, .. } := BSubfieldGenerated1
  let { FIELD_EXTENSION_FROM_SUBRING_GENERATED, FIELD_EXTENSION_IMP_HOMOMORPHISM,
        FIELD_EXTENSION_IMP_MONOMORPHISM, FIELD_EXTENSION_IMP_SUBSET,
        FIELD_EXTENSION_INTO_SUBFIELD_GENERATED, FIELD_EXTENSION_SUBRING_GENERATED,
        FIELD_EXTENSION_TRANS, field_extension, .. } := BFieldExtension
  let { RING_MATROID, .. } := BRingMatroid
  let { RING_INDEPENDENT_EMPTY, RING_MATROID_INDEPENDENT, .. } := BLinearAlgebra
  let { RING_INDEPENDENT_INSERT, RING_SPAN_SUBSET_SUBFIELD_GENERATED, .. } := BFinitary
  let { FINITELY_GENERATED_EXTENSION, FINITELY_GENERATED_EXTENSION_TRANS,
        FINITELY_GENERATED_IMP_FIELD_EXTENSION, FINITE_EXTENSION_RING_MATROID,
        finitely_generated_extension, .. } := BFiniteExtension
  let { ALGEBRAIC_IMP_FIELD_EXTENSION, ALGEBRAIC_OVER_IN_CARRIER,
        ALGEBRAIC_OVER_SUBRING_GENERATED, algebraic_extension, .. } := BAlgebraicExtension
  let { ALGEBRAIC_OVER_FROM_MONOMORPHIC_IMAGE,
        FINITE_EQ_FINITELY_GENERATED_ALGEBRAIC_EXTENSION, .. } := BAlgebraicExtensionProps
  let { ALGEBRAIC_FROM_SUBRING_GENERATED, .. } := BAlgebraicExtMisc
  let { TRANSCENDENCE_BASIS_IMP_SUBSET, transcendence_basis, .. } := BAlgDepDefs
  let { ALGEBRAICALLY_INDEPENDENT_OVER_SUBRING_GENERATED_MONO, .. } := BAlgDepSpan
  let { ALGEBRAICALLY_SPANNING, .. } := BAlgSpanDepIndep
  let { TRANSCENDENCE_BASIS_EXISTS, .. } := BAlgebraicMatroid
  let { ALGEBRAIC_OVER_MONOMORPHIC_IMAGE, TRANSCENDENCE_BASIS_CARD_LE_LEFT, .. } := BAlgebraicTrans
  let { ALGEBRAICALLY_INDEPENDENT_OVER_ALGEBRAIC_EXTENSION,
        FINITELY_GENERATED_ALGEBRAICALLY_INDEPENDENT_IMP_FINITE,
        TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_INDEPENDENT,
        TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_SPANNING, .. } := BAlgebraicOverExt
  let { TOTALLY_TRANSCENDENTAL_EXTENSION, .. } := BTotallyTranscendental
  -- @@SCOPE END

  let FINITELY_GENERATED_EXTENSION_TRANS_EQ ← (do
    let choice_lemma ← prove
     r"!P (s:A->bool).
            (!t. FINITE t /\ t SUBSET s ==> ?y. y IN s /\ P y t)
            ==> ?f. (!n. f n IN s) /\ (!n. P (f n) {f i | i < n})"
     (REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"?f:num->A. !n. f n = @y. y IN s /\ P y {f i | i < n}")
      MP_TAC THENL
       [MATCH_MP_TAC (← MATCH_MP WF_REC WF_num) THEN
        REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC [],
        MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC [AND_FORALL_THM] THEN
        GEN_TAC THEN DISCH_THEN (ASSUME_TAC o GSYM) THEN MATCH_MP_TAC num_WF THEN
        X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"{(f:num->A) i | i < n}")) THEN
        ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
        ASM_SIMP_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM,
                     FINITE_IMAGE, FINITE_NUMSEG_LT] THEN
        DISCH_THEN (MP_TAC o SELECT_RULE) THEN
        ASM_REWRITE_TAC [← GSYM SIMPLE_IMAGE_GEN]])
    let main_lemma ← (do
      let n5 ← SET_RULE (← q r"x IN s ==> !t. s SUBSET t ==> x IN t")
      let n4 ← ARITH_RULE (← q r"n < SUC n")
      let n3 ← SET_RULE (← q r"s SUBSET s' ==> s UNION t SUBSET s' UNION t")
      let n2 ← SET_RULE (← q r"~(s SUBSET t) <=> ?x. x IN s /\ ~(x IN t)")
      let n1 ← MESON []
       (← q r"(?b. P b /\ Q b /\ R b) <=> ~(!b. P b /\ Q b ==> ~R b)")
      let loc_ynumb ← q r"y:num->B"
      prove
       r"!(f:A->B) (g:B->C) k l m.
              algebraic_extension (k,l) f /\
              field_extension (l,m) g /\
              finitely_generated_extension (k,m) (g o f)
              ==> finitely_generated_extension (k,l) f"
       (REPEAT STRIP_TAC THEN
        FIRST_ASSUM (MP_TAC o MATCH_MP TRANSCENDENCE_BASIS_EXISTS o
              MATCH_MP FINITELY_GENERATED_IMP_FIELD_EXTENSION) THEN
        DISCH_THEN (X_CHOOSE_TAC (← q r"b:C->bool")) THEN
        FIRST_ASSUM (ASSUME_TAC o MATCH_MP TRANSCENDENCE_BASIS_IMP_SUBSET) THEN
        MP_TAC (← ISPECL
         [← q r"f:A->B", ← q r"g:B->C", ← q r"k:A ring", ← q r"l:B ring", ← q r"m:C ring", ← q r"b:C->bool"]
         ALGEBRAICALLY_INDEPENDENT_OVER_ALGEBRAIC_EXTENSION) THEN
        ASM_SIMP_TAC [TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_INDEPENDENT] THEN
        DISCH_TAC THEN
        FIRST_ASSUM (ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
        SUBGOAL_THEN (← q r"field(k:A ring) /\ field(l:B ring) /\ field(m:C ring)")
        STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [field_extension], ALL_TAC] THEN
        ASM_REWRITE_TAC [FINITELY_GENERATED_EXTENSION] THEN REWRITE_TAC [n1] THEN
        REWRITE_TAC [n2] THEN
        DISCH_THEN (MP_TAC o MATCH_MP choice_lemma) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"y:num->B") STRIP_ASSUME_TAC) THEN
        ABBREV_TAC (← q r"A n = ring_carrier
                  (subfield_generated l
                  (IMAGE (f:A->B) (ring_carrier k) UNION {y i | i < n}))") THEN
        SUBGOAL_THEN
         (← q r"(!n. A n subfield_of (l:B ring)) /\
          (!n. IMAGE (f:A->B) (ring_carrier k) SUBSET A n) /\
          (!m n. m < n ==> A m PSUBSET A n)")
        MP_TAC THEN POP_ASSUM MP_TAC THENL
         [DISCH_THEN (fun th => tactic_of do
            pure (ONCE_REWRITE_TAC [← GSYM th] THEN ASSUME_TAC th)) THEN
          REWRITE_TAC [SUBFIELD_SUBFIELD_GENERATED_EQ] THEN
          CONJ_TAC THENL [ASM_MESON_TAC [FIELD_SUBFIELD_GENERATED], ALL_TAC] THEN
          CONJ_TAC THENL
           [GEN_TAC THEN REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN
            MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
            REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET)) THEN
            ASM SET_TAC [],
            ALL_TAC] THEN
          MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
          REWRITE_TAC [PSUBSET_TRANS] THEN X_GEN_TAC (← q r"n:num") THEN
          REWRITE_TAC [PSUBSET_ALT] THEN CONJ_TAC THENL
           [MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN
            REWRITE_TAC [LT] THEN SET_TAC [],
            EXISTS_TAC (← q r"(y:num->B) n") THEN CONJ_TAC THENL
             [MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN, ASM_REWRITE_TAC []] THEN
            ASM_REWRITE_TAC [LT] THEN SET_TAC []],
          DISCH_THEN (K ALL_TAC) THEN STRIP_TAC] THEN
        REPEAT (FIRST_X_ASSUM (fun th => tactic_of do
          let _ ← liftExcept (check (free_in loc_ynumb) (concl th)); pure ALL_TAC)) THEN
        ABBREV_TAC
         (← q r"B = \n:num. ring_carrier(subfield_generated m
                       (IMAGE (g:B->C) (A n) UNION b))") THEN
        SUBGOAL_THEN (← q r"!n. (B:num->C->bool) n subfield_of m") ASSUME_TAC THENL
         [EXPAND_TAC "B" THEN REWRITE_TAC [] THEN
          ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED],
          ALL_TAC] THEN
        SUBGOAL_THEN (← q r"!m n. m < n ==> (B:num->C->bool) m PSUBSET B n")
        ASSUME_TAC THENL
         [SUBGOAL_THEN
           (← q r"!n:num. {x | algebraic_over (k,subfield_generated m (B n))
                                        ((g:B->C) o (f:A->B)) x} =
                    IMAGE g (A n)")
          ASSUME_TAC THENL
           [ALL_TAC,
            MAP_EVERY X_GEN_TAC [← q r"i:num", ← q r"j:num"] THEN DISCH_TAC THEN
            FIRST_X_ASSUM (MP_TAC o SPECL [← q r"i:num", ← q r"j:num"]) THEN
            ASM_REWRITE_TAC [PSUBSET] THEN MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
             [EXPAND_TAC "B" THEN REWRITE_TAC [] THEN DISCH_TAC THEN
              MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN ASM SET_TAC [],
              REWRITE_TAC [CONTRAPOS_THM]] THEN
            DISCH_TAC THEN FIRST_X_ASSUM (fun th => tactic_of do
              pure (MP_TAC (← SPEC (← q r"i:num") th) THEN MP_TAC (← SPEC (← q r"j:num") th))) THEN
            ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
            RULE_ASSUM_TAC (REWRITE_RULE
             [field_extension, ring_monomorphism, ring_homomorphism,
              subfield_of, subring_of]) THEN
            ASM SET_TAC []] THEN
          X_GEN_TAC (← q r"n:num") THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
          REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN CONJ_TAC THENL
           [ALL_TAC,
            X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN
            ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
            MATCH_MP_TAC ALGEBRAIC_OVER_SUBRING_GENERATED THEN
            ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
            REPEAT CONJ_TAC THENL
             [ASM_MESON_TAC [FIELD_EXTENSION_TRANS],
              REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, o_THM] THEN
              REPEAT STRIP_TAC THEN EXPAND_TAC "B" THEN REWRITE_TAC [] THEN
              MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN,
              MP_TAC (← ISPECL [← q r"f:A->B", ← q r"g:B->C", ← q r"k:A ring", ← q r"l:B ring", ← q r"m:C ring",
                             ← q r"x:B"] ALGEBRAIC_OVER_MONOMORPHIC_IMAGE) THEN
              ASM_SIMP_TAC [FIELD_EXTENSION_IMP_MONOMORPHISM,
                           RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
              SUBGOAL_THEN (← q r"(x:B) IN ring_carrier l") ASSUME_TAC THENL
               [RULE_ASSUM_TAC (REWRITE_RULE [subfield_of, subring_of]) THEN
                ASM SET_TAC [],
                ASM_MESON_TAC [algebraic_extension]],
              EXPAND_TAC "B" THEN REWRITE_TAC [] THEN
              MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN] THEN
            RULE_ASSUM_TAC (REWRITE_RULE
             [field_extension, ring_monomorphism, ring_homomorphism,
              subfield_of, subring_of]) THEN
            ASM SET_TAC []] THEN
          X_GEN_TAC (← q r"y:C") THEN DISCH_TAC THEN
          MP_TAC (← ISPECL [← q r"g:B->C", ← q r"subfield_generated l ((A:num->B->bool) n)",
                         ← q r"m:C ring", ← q r"b:C->bool", ← q r"y:C"]
            TOTALLY_TRANSCENDENTAL_EXTENSION) THEN
          ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
          DISCH_THEN MATCH_MP_TAC THEN
          FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
          SIMP_TAC [] THEN DISCH_THEN (K ALL_TAC) THEN REPEAT CONJ_TAC THENL
           [ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
            MATCH_MP_TAC FIELD_EXTENSION_FROM_SUBRING_GENERATED THEN
            ASM_REWRITE_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
            ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED],
            ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
            MATCH_MP_TAC ALGEBRAICALLY_INDEPENDENT_OVER_SUBRING_GENERATED_MONO THEN
            EXISTS_TAC (← q r"ring_carrier l:B->bool") THEN
            ASM_REWRITE_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET] THEN
            ASM_REWRITE_TAC [SUBRING_GENERATED_RING_CARRIER],
            MATCH_MP_TAC ALGEBRAIC_FROM_SUBRING_GENERATED THEN
            EXISTS_TAC
             (← q r"ring_carrier (subfield_generated m ((B:num->C->bool) n))") THEN
            CONJ_TAC THENL
             [REWRITE_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
              ASM_SIMP_TAC [field_extension, FIELD_SUBFIELD_GENERATED] THEN
              ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
              MATCH_MP_TAC RING_MONOMORPHISM_BETWEEN_SUBRINGS THEN
              ASM_SIMP_TAC [FIELD_EXTENSION_IMP_MONOMORPHISM] THEN
              ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
              EXPAND_TAC "B" THEN REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN
              MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
              RULE_ASSUM_TAC (REWRITE_RULE
               [field_extension, ring_monomorphism, ring_homomorphism,
                subfield_of, subring_of]) THEN
              ASM SET_TAC [],
              ASM_SIMP_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED,
                           CARRIER_SUBFIELD_GENERATED_SUBFIELD]] THEN
            MP_TAC (← ISPECL
             [← q r"f:A->B", ← q r"g:B->C", ← q r"k:A ring",
              ← q r"subfield_generated l ((A:num->B->bool) n)",
              ← q r"subfield_generated m ((B:num->C->bool) n)"]
             ALGEBRAIC_OVER_FROM_MONOMORPHIC_IMAGE) THEN
            DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
            ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
            CONJ_TAC THENL
             [MATCH_MP_TAC RING_MONOMORPHISM_INTO_SUBRING THEN
              ASM_SIMP_TAC [FIELD_EXTENSION_IMP_MONOMORPHISM] THEN
              ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD],
              MATCH_MP_TAC RING_HOMOMORPHISM_BETWEEN_SUBRINGS THEN
              ASM_SIMP_TAC [FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
              ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
              EXPAND_TAC "B" THEN REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN
              MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
              RULE_ASSUM_TAC (REWRITE_RULE
               [field_extension, ring_monomorphism, ring_homomorphism,
                subfield_of, subring_of]) THEN
              ASM SET_TAC []],
            FIRST_X_ASSUM (MP_TAC o MATCH_MP ALGEBRAIC_OVER_IN_CARRIER) THEN
            ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD]],
          ALL_TAC] THEN
        SUBGOAL_THEN
         (← q r"finite_extension
            (subfield_generated m
               (IMAGE ((g:B->C) o (f:A->B)) (ring_carrier k) UNION b),m) I")
        MP_TAC THENL
         [REWRITE_TAC [FINITE_EQ_FINITELY_GENERATED_ALGEBRAIC_EXTENSION] THEN
          FIRST_ASSUM (MP_TAC o MATCH_MP
            TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_SPANNING) THEN
          ASM_SIMP_TAC [ALGEBRAICALLY_SPANNING,
                       FINITELY_GENERATED_IMP_FIELD_EXTENSION] THEN
          DISCH_THEN (K ALL_TAC) THEN
          ASM_REWRITE_TAC [FINITELY_GENERATED_EXTENSION] THEN CONJ_TAC THENL
           [ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
            ASM_REWRITE_TAC [FIELD_EXTENSION_SUBRING_GENERATED] THEN
            REWRITE_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
            ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED],
            ALL_TAC] THEN
          FIRST_ASSUM (MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I
            [FINITELY_GENERATED_EXTENSION]) THEN
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"c:C->bool") THEN STRIP_TAC THEN
          ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
           (← REWRITE_RULE [IMP_CONJ] SUBSET_TRANS)) THEN
          MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN REWRITE_TAC [IMAGE_o] THEN
          MATCH_MP_TAC n3 THEN
          REWRITE_TAC [SUBSET, IMAGE_I] THEN REPEAT STRIP_TAC THEN
          MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
          RULE_ASSUM_TAC (REWRITE_RULE
           [field_extension, ring_monomorphism, ring_homomorphism,
            subfield_of, subring_of]) THEN
          ASM SET_TAC [],
          ALL_TAC] THEN
        REWRITE_TAC [FINITE_EXTENSION_RING_MATROID] THEN STRIP_TAC THEN
        SUBGOAL_THEN
         (← q r"!n. ?y:C. y IN ring_carrier m /\ ~(y IN B n) /\ y IN B(SUC n)")
        MP_TAC THENL
         [RULE_ASSUM_TAC (REWRITE_RULE [subfield_of, subring_of, PSUBSET_ALT]) THEN
          ASM_MESON_TAC [SUBSET, n4],
          REWRITE_TAC [SKOLEM_THM, FORALL_AND_THM] THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"y:num->C") STRIP_ASSUME_TAC)] THEN
        SUBGOAL_THEN (← q r"!i j. (y:num->C) i IN B j <=> i < j") ASSUME_TAC THENL
         [ASM SET_TAC [NOT_LE, LE_SUC_LT, LT_CASES], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"!i j. (y:num->C) i = y j <=> i = j") ASSUME_TAC THENL
         [MATCH_MP_TAC WLOG_LT THEN ASM SET_TAC [], ALL_TAC] THEN
        FIRST_ASSUM (MP_TAC o SPEC (← q r"IMAGE (y:num->C) (:num)") o MATCH_MP
         (← REWRITE_RULE [IMP_CONJ] MATROID_DIMENSION_GE_FINITE_CARD)) THEN
        ASM_SIMP_TAC [FINITE_IMAGE_INJ_EQ] THEN
        REWRITE_TAC [← REWRITE_RULE [INFINITE] num_INFINITE] THEN
        ASM_SIMP_TAC [RING_MATROID_INDEPENDENT, FIELD_SUBFIELD_GENERATED] THEN
        ONCE_REWRITE_TAC [MATROID_INDEPENDENT_FINITARY] THEN
        ASM_SIMP_TAC [RING_MATROID, FIELD_SUBFIELD_GENERATED,
                     FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
        REWRITE_TAC [FORALL_FINITE_SUBSET_IMAGE, SUBSET_UNIV] THEN
        ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
        X_GEN_TAC (← q r"d:num->bool") THEN REWRITE_TAC [FINITE_SUBSET_NUMSEG] THEN
        DISCH_THEN (X_CHOOSE_TAC (← q r"nn:num")) THEN
        MATCH_MP_TAC MATROID_INDEPENDENT_MONO THEN
        EXISTS_TAC (← q r"IMAGE (y:num->C) {i | i < SUC nn}") THEN
        CONJ_TAC THENL
         [SPEC_TAC (← q r"SUC nn", ← q r"n:num"),
          MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
           (← REWRITE_RULE [IMP_CONJ] SUBSET_TRANS)) THEN
          REWRITE_TAC [IN_NUMSEG, IN_ELIM_THM, SUBSET] THEN ARITH_TAC] THEN
        ASM_SIMP_TAC [RING_MATROID_INDEPENDENT, FIELD_SUBFIELD_GENERATED,
                     FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
        MATCH_MP_TAC num_INDUCTION THEN
        REWRITE_TAC [NUMSEG_CLAUSES_LT, IMAGE_CLAUSES, RING_INDEPENDENT_EMPTY] THEN
        X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN
        W (MP_TAC o PART_MATCH (lhand o rand) RING_INDEPENDENT_INSERT o snd) THEN
        ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
         [ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED,
                       FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
          ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE],
          DISCH_THEN SUBST1_TAC] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE [SUBSET]
           RING_SPAN_SUBSET_SUBFIELD_GENERATED)) THEN
        REWRITE_TAC [IMAGE_I] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"(B:num->C->bool) n") o MATCH_MP n5) THEN
        ASM_REWRITE_TAC [NOT_LT] THEN
        MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [UNION_SUBSET] THEN CONJ_TAC THENL
         [ALL_TAC, ASM SET_TAC []] THEN
        MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [] THEN
        EXPAND_TAC "B" THEN REWRITE_TAC [SUBSET, IMAGE_o] THEN
        REWRITE_TAC [SUBSET, IMAGE_I] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
        RULE_ASSUM_TAC (REWRITE_RULE
         [field_extension, ring_monomorphism, ring_homomorphism,
          subfield_of, subring_of]) THEN
        ASM SET_TAC []))
    let s6 ← SET_RULE
     (← q r"s SUBSET t ==> IMAGE g s UNION u SUBSET IMAGE g t UNION u")
    prove
     r"!(f:A->B) (g:B->C) k l m.
            field_extension (k,l) f /\ field_extension (l,m) g
            ==> (finitely_generated_extension (k,m) (g o f) <=>
                 finitely_generated_extension (k,l) f /\
                 finitely_generated_extension (l,m) g)"
     (REPEAT STRIP_TAC THEN EQ_TAC THEN
      REWRITE_TAC [FINITELY_GENERATED_EXTENSION_TRANS] THEN
      DISCH_THEN (fun th => CONJ_TAC THEN MP_TAC th) THENL
       [DISCH_TAC,
        ASM_REWRITE_TAC [FINITELY_GENERATED_EXTENSION] THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"c:C->bool") THEN STRIP_TAC THEN
        ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
         (← REWRITE_RULE [IMP_CONJ] SUBSET_TRANS)) THEN
        MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN REWRITE_TAC [IMAGE_o] THEN
        REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET)) THEN
        ASM SET_TAC []] THEN
      MP_TAC (← ISPECL [← q r"(g:B->C) o (f:A->B)", ← q r"k:A ring", ← q r"m:C ring"]
            TRANSCENDENCE_BASIS_EXISTS) THEN
      MP_TAC (← ISPECL [← q r"f:A->B", ← q r"k:A ring", ← q r"l:B ring"]
            TRANSCENDENCE_BASIS_EXISTS) THEN
      ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"b:B->bool") THEN STRIP_TAC THEN
      ANTS_TAC THENL [ASM_MESON_TAC [FIELD_EXTENSION_TRANS], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"c:C->bool")) THEN
      SUBGOAL_THEN (← q r"FINITE(b:B->bool)") ASSUME_TAC THENL
       [ASM_MESON_TAC [FINITELY_GENERATED_ALGEBRAICALLY_INDEPENDENT_IMP_FINITE,
                      TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_INDEPENDENT,
                      TRANSCENDENCE_BASIS_CARD_LE_LEFT, CARD_LE_FINITE],
        ALL_TAC] THEN
      MP_TAC (← ISPECL
       [← q r"f:A->B", ← q r"I:B->B", ← q r"k:A ring",
        ← q r"subfield_generated l (IMAGE (f:A->B) (ring_carrier k) UNION b)",
        ← q r"l:B ring"] FINITELY_GENERATED_EXTENSION_TRANS) THEN
      REWRITE_TAC [I_O_ID] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC [FINITELY_GENERATED_EXTENSION] THEN CONJ_TAC THENL
         [ONCE_REWRITE_TAC [← GSYM SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN
          MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
          ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN CONJ_TAC THENL
           [ASM_MESON_TAC [SUBFIELD_SUBFIELD_GENERATED, field_extension],
            REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
            REPEAT (FIRST_X_ASSUM (MP_TAC o
              MATCH_MP FIELD_EXTENSION_IMP_SUBSET)) THEN
            ASM SET_TAC []],
          EXISTS_TAC (← q r"b:B->bool") THEN
          ASM_REWRITE_TAC [SUBFIELD_GENERATED_IDEMPOT, SUBSET_REFL] THEN
          REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN
          MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN ASM_REWRITE_TAC [IN_UNION] THEN
          REPEAT (FIRST_X_ASSUM (MP_TAC o
            MATCH_MP TRANSCENDENCE_BASIS_IMP_SUBSET)) THEN
          RULE_ASSUM_TAC (REWRITE_RULE
           [field_extension, ring_monomorphism, ring_homomorphism]) THEN
          ASM SET_TAC []],
        ALL_TAC] THEN
      MP_TAC (← ISPECL
       [← q r"I:B->B", ← q r"g:B->C",
        ← q r"subfield_generated l (IMAGE (f:A->B) (ring_carrier k) UNION b)",
        ← q r"l:B ring", ← q r"m:C ring"] main_lemma) THEN
      ASM_REWRITE_TAC [I_O_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC [ALGEBRAICALLY_SPANNING, transcendence_basis], ALL_TAC] THEN
      REWRITE_TAC [FINITELY_GENERATED_EXTENSION] THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC [← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
        MATCH_MP_TAC FIELD_EXTENSION_FROM_SUBRING_GENERATED THEN
        ASM_REWRITE_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
        ASM_MESON_TAC [FIELD_SUBFIELD_GENERATED, field_extension],
        FIRST_ASSUM (MP_TAC o CONJUNCT2 o
          GEN_REWRITE_RULE I [finitely_generated_extension])] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"d:C->bool") THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← SYM th])) THEN
      MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN REWRITE_TAC [IMAGE_o] THEN
      MATCH_MP_TAC s6 THEN
      REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN ASM_REWRITE_TAC [IN_UNION] THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o
        MATCH_MP TRANSCENDENCE_BASIS_IMP_SUBSET)) THEN
      RULE_ASSUM_TAC (REWRITE_RULE
       [field_extension, ring_monomorphism, ring_homomorphism]) THEN
      ASM SET_TAC []))

  -- @@RETURN BEGIN
  return { FINITELY_GENERATED_EXTENSION_TRANS_EQ }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Algebraically closed fields and algebraic closures.                       -/
/- ------------------------------------------------------------------------- -/

structure AcfBasic where
  -- @@FIELDS
  algebraically_closed_field : thm
  ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD : thm
  ALGEBRAICALLY_CLOSED_FIELD_ISOMORPHIC_IMAGE : thm
  ISOMORPHIC_RING_ALGEBRAICALLY_CLOSED_FIELD : thm
  ALGEBRAICALLY_CLOSED_FIELD_IMP_INFINITE : thm
  ALGEBRAICALLY_CLOSED_FIELD_NO_PROPER_ALGEBRAIC_EXTENSION : thm
  deriving Inhabited

@[nospecialize]
def setupAcfBasic [HolBase] (D : FieldTheoryDeps) (BFieldExtension : FieldExtension) (BAlgebraicOverBasics : AlgebraicOverBasics) :
    ExceptT String IO AcfBasic := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, TAUT, new_definition, .. } := D
  let { FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING, FIELD_MUL_EQ_0,
        FUN_EQ_THM, FUN_IN_IMAGE, .. } := D.core2
  let { INFINITE, INTEGRAL_DOMAIN_POLY_RING, INTEGRAL_DOMAIN_PRODUCT_EQ_0, IN_ELIM_THM,
        IN_IMAGE, IN_RING_POLYNOMIAL_CARRIER_COMPOSE, ISOMORPHIC_RING_FIELDNESS, .. } := D.core3
  let { NOT_EXISTS_THM, NOT_IMP, POLY_CLAUSES, POLY_COMPOSE_HOMOMORPHISM_CONST,
        POLY_COMPOSE_HOMOMORPHISM_MUL, POLY_COMPOSE_HOMOMORPHISM_SUB,
        POLY_COMPOSE_HOMOMORPHISM_VAR, POLY_CONST_0, POLY_DEG_1, POLY_DEG_ADD,
        POLY_DEG_EQ_0, POLY_DEG_MONOMORPHIC_IMAGE, POLY_DEG_MUL_X_MINUS_A,
        POLY_DIVIDES_X_MINUS_ROOT, POLY_EVAL, POLY_EVAL_1, POLY_EVAL_ADD,
        POLY_EVAL_CONST, POLY_EVAL_HOMOMORPHIC_IMAGE, POLY_EVAL_MUL, .. } := D.core4
  let { POLY_EVAL_RING_PRODUCT, POLY_EVAL_SUB, POLY_EVAL_VAR, POLY_RING,
        POLY_RING_CLAUSES, POLY_X_MINUS_A_IN_CARRIER, POLY_X_MINUS_A_NONZERO, RING_0,
        RING_1, RING_ADD_LZERO, .. } := D.core5
  let { RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_POLY_RINGS,
        RING_ISOMORPHISMS_ISOMORPHISM, RING_ISOMORPHISM_IMP_HOMOMORPHISM,
        RING_ISOMORPHISM_IMP_MONOMORPHISM, RING_ISOMORPHISM_MONOMORPHISM_ALT,
        RING_MONOMORPHISM_EQ_0, RING_MONOMORPHISM_IMP_HOMOMORPHISM, .. } := D.core6
  let { RING_MUL_RZERO, RING_POLYNOMIAL, RING_POLYNOMIAL_1, RING_POLYNOMIAL_ADD,
        RING_POLYNOMIAL_CONST, RING_POLYNOMIAL_IMP_POWERSERIES, RING_POLYNOMIAL_MUL,
        RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR, RING_POWERSERIES_CONST,
        RING_POWERSERIES_SUB, RING_POWERSERIES_VAR, RING_PRODUCT, RING_SUB,
        RING_SUB_EQ_0, RING_SUB_REFL, .. } := D.core7
  let { SUBSET, SUBSET_UNIV, TRIVIAL_RING_10, isomorphic_ring, num_WF, .. } := D.core8
  let { o_THM, ring_divides, ring_homomorphism, ring_isomorphism, ring_polynomial,
        ring_powerseries, .. } := D.core9
  let { field_extension, .. } := BFieldExtension
  let { ALGEBRAIC_EXTENSION_ALT, .. } := BAlgebraicOverBasics
  -- @@SCOPE END

  let algebraically_closed_field ← new_definition
   r"algebraically_closed_field(k:A ring) <=>
        field k /\
        !p. p IN ring_carrier(poly_ring k (:1)) /\ ~(poly_deg k p = 0)
            ==> ?x. x IN ring_carrier k /\ poly_eval k p x = ring_0 k"

  let ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD ← prove
   r"!k:A ring. algebraically_closed_field k ==> field k"
   (SIMP_TAC [algebraically_closed_field])

  let ALGEBRAICALLY_CLOSED_FIELD_ISOMORPHIC_IMAGE ← prove
   r"!(k:A ring) (l:B ring) f.
        ring_isomorphism(k,l) f /\ algebraically_closed_field k
        ==> algebraically_closed_field l"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q r"g:B->A") MP_TAC o
      GEN_REWRITE_RULE I [ring_isomorphism]) THEN
    REWRITE_TAC [RING_ISOMORPHISMS_ISOMORPHISM] THEN STRIP_TAC THEN
    REWRITE_TAC [algebraically_closed_field] THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC [ISOMORPHIC_RING_FIELDNESS, isomorphic_ring], ALL_TAC] THEN
    X_GEN_TAC (← q r"p:(1->num)->B") THEN STRIP_TAC THEN SUBGOAL_THEN
     (← q r"(g:B->A) o (p:(1->num)->B) IN ring_carrier(poly_ring k (:1)) /\
      poly_deg (k:A ring) ((g:B->A) o (p:(1->num)->B)) =
      poly_deg (l:B ring) p") STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [IN_RING_POLYNOMIAL_CARRIER_COMPOSE,
        RING_ISOMORPHISM_IMP_HOMOMORPHISM, POLY_DEG_MONOMORPHIC_IMAGE,
        RING_POLYNOMIAL, RING_ISOMORPHISM_IMP_MONOMORPHISM], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(g:B->A) o (p:(1->num)->B)")) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"y:A") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"(f:A->B) y") THEN
    SUBGOAL_THEN (← q r"(f:A->B) y IN ring_carrier l") ASSUME_TAC THENL
     [ASM_MESON_TAC [RING_ISOMORPHISM_IMP_HOMOMORPHISM,
                     ring_homomorphism, SUBSET, FUN_IN_IMAGE],
      ASM_REWRITE_TAC []] THEN
    SUBGOAL_THEN (← q r"(f:A->B) o (g:B->A) o (p:(1->num)->B) = p") ASSUME_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, o_THM] THEN
      X_GEN_TAC (← q r"m:1->num") THEN FIRST_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC
       (← q r"(p:(1->num)->B) IN ring_carrier(poly_ring (l:B ring) (:1))") THEN
      REWRITE_TAC [POLY_RING, IN_ELIM_THM, SUBSET_UNIV,
                  ring_polynomial, ring_powerseries] THEN
      MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL
     [← q r"k:A ring", ← q r"l:B ring", ← q r"y:A", ← q r"f:A->B", ← q r"(g:B->A) o (p:(1->num)->B)"]
     POLY_EVAL_HOMOMORPHIC_IMAGE) THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN
      TRY (MATCH_MP_TAC RING_ISOMORPHISM_IMP_HOMOMORPHISM) THEN
      ASM_REWRITE_TAC [], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    UNDISCH_TAC (← q r"ring_isomorphism(k:A ring,l:B ring) (f:A->B)") THEN
    DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP RING_HOMOMORPHISM_0
        (← MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM th)])))

  let ISOMORPHIC_RING_ALGEBRAICALLY_CLOSED_FIELD ← prove
   r"!(k:A ring) (l:B ring).
        k isomorphic_ring l
        ==> (algebraically_closed_field k <=> algebraically_closed_field l)"
   (REWRITE_TAC [isomorphic_ring] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM (X_CHOOSE_TAC (← q r"g:B->A") o
      GEN_REWRITE_RULE I [ring_isomorphism]) THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o
      GEN_REWRITE_RULE I [RING_ISOMORPHISMS_ISOMORPHISM]) THEN
    ASM_MESON_TAC [ALGEBRAICALLY_CLOSED_FIELD_ISOMORPHIC_IMAGE])

  let ALGEBRAICALLY_CLOSED_FIELD_IMP_INFINITE ← prove
   r"!k:A ring. algebraically_closed_field k ==> INFINITE(ring_carrier k)"
   (GEN_TAC THEN REWRITE_TAC [algebraically_closed_field] THEN
    STRIP_TAC THEN REWRITE_TAC [INFINITE] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"~trivial_ring (k:A ring)") ASSUME_TAC THENL
     [ASM_MESON_TAC [FIELD_IMP_NONTRIVIAL_RING], ALL_TAC] THEN
    ABBREV_TAC (← q r"P = ring_product (poly_ring (k:A ring) (:1)) (ring_carrier k)
          (\a. poly_sub k (poly_var k one) (poly_const k a))") THEN SUBGOAL_THEN
     (← q r"P IN ring_carrier(poly_ring (k:A ring) (:1))") ASSUME_TAC THENL
     [EXPAND_TAC "P" THEN REWRITE_TAC [RING_PRODUCT], ALL_TAC] THEN SUBGOAL_THEN
     (← q r"~(P = ring_0(poly_ring (k:A ring) (:1)))") ASSUME_TAC THENL
     [EXPAND_TAC "P" THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_PRODUCT_EQ_0,
                   INTEGRAL_DOMAIN_POLY_RING, FIELD_IMP_INTEGRAL_DOMAIN] THEN
      REWRITE_TAC [NOT_EXISTS_THM, ← TAUT (← q r"~(p /\ q) <=> p ==> ~q")] THEN
      X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN REWRITE_TAC [POLY_RING_CLAUSES] THEN
      ASM_SIMP_TAC [POLY_X_MINUS_A_NONZERO], ALL_TAC] THEN SUBGOAL_THEN
     (← q r"!x:A. x IN ring_carrier k ==> poly_eval k P x = ring_0 k") ASSUME_TAC THENL
     [X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN EXPAND_TAC "P" THEN
      ASM_SIMP_TAC [POLY_EVAL_RING_PRODUCT, POLY_X_MINUS_A_IN_CARRIER] THEN
      ASM_SIMP_TAC [INTEGRAL_DOMAIN_PRODUCT_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN] THEN
      EXISTS_TAC (← q r"x:A") THEN ASM_REWRITE_TAC [] THEN BETA_TAC THEN
      ASM_SIMP_TAC [POLY_EVAL_SUB, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST,
                   POLY_EVAL_VAR, POLY_EVAL_CONST, RING_SUB_REFL], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~(poly_deg (k:A ring) (P:(1->num)->A) = 0)") ASSUME_TAC THENL
     [DISCH_TAC THEN
      MP_TAC (← ISPECL [← q r"k:A ring", ← q r"P:(1->num)->A"] POLY_DEG_EQ_0) THEN
      ASM_REWRITE_TAC [RING_POLYNOMIAL] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"c:A") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"(c:A) = ring_0 k") SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"ring_0 (k:A ring)")) THEN
        REWRITE_TAC [RING_0] THEN ASM_SIMP_TAC [POLY_EVAL_CONST],
        ASM_MESON_TAC [POLY_CONST_0, POLY_RING_CLAUSES]], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC
     (← q r"poly_add (k:A ring) P (poly_1 k:(1->num)->A)")) THEN
    REWRITE_TAC [NOT_IMP, NOT_EXISTS_THM] THEN CONJ_TAC THENL [CONJ_TAC THENL
       [REWRITE_TAC [← GSYM RING_POLYNOMIAL] THEN MATCH_MP_TAC
          RING_POLYNOMIAL_ADD THEN ASM_REWRITE_TAC [RING_POLYNOMIAL,
            RING_POLYNOMIAL_1],
        MP_TAC (← ISPECL [← q r"k:A ring", ← q r"P:(1->num)->A",
                       ← q r"poly_1 (k:A ring):(1->num)->A"] POLY_DEG_ADD) THEN
        ASM_REWRITE_TAC [RING_POLYNOMIAL, RING_POLYNOMIAL_1, POLY_DEG_1] THEN
        DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC],
      X_GEN_TAC (← q r"x:A") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_SIMP_TAC [POLY_EVAL_ADD, RING_POLYNOMIAL, RING_POLYNOMIAL_1,
                   POLY_EVAL_1, RING_ADD_LZERO, RING_1,
                   ← GSYM TRIVIAL_RING_10]])

  let ALGEBRAICALLY_CLOSED_FIELD_NO_PROPER_ALGEBRAIC_EXTENSION ← prove
   r"!(k:A ring) (l:B ring) (f:A->B).
        algebraically_closed_field k /\ algebraic_extension(k,l) f
        ==> ring_isomorphism(k,l) f"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [algebraically_closed_field, ALGEBRAIC_EXTENSION_ALT] THEN
    STRIP_TAC THEN SUBGOAL_THEN
      (← q r"ring_monomorphism(k:A ring,l:B ring) (f:A->B) /\ field(l:B ring) /\
       ring_homomorphism(k:A ring,l:B ring) (f:A->B)") STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [field_extension,
       RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN SUBGOAL_THEN
     (← q r"ring_homomorphism(poly_ring (k:A ring) (:1), poly_ring (l:B ring) (:1))
                        (\p:(1->num)->A. (f:A->B) o p)") ASSUME_TAC THENL
    [MATCH_MP_TAC RING_HOMOMORPHISM_POLY_RINGS THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [RING_ISOMORPHISM_MONOMORPHISM_ALT] THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"!n (x:B) (p:(1->num)->A). x IN ring_carrier l /\
        p IN ring_carrier(poly_ring (k:A ring) (:1)) /\
        ~(p = ring_0(poly_ring k (:1))) /\
        poly_eval (l:B ring) ((f:A->B) o p) x = ring_0 l /\ poly_deg k p = n
        ==> x IN IMAGE f (ring_carrier k)") MP_TAC THENL
    [MATCH_MP_TAC num_WF THEN X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN
     MAP_EVERY X_GEN_TAC [← q r"x:B", ← q r"p:(1->num)->A"] THEN STRIP_TAC THEN
     SUBGOAL_THEN (← q r"ring_polynomial (k:A ring) (p:(1->num)->A)") ASSUME_TAC THENL
     [ASM_REWRITE_TAC [RING_POLYNOMIAL], ALL_TAC] THEN ASM_CASES_TAC (← q r"n = 0") THENL
     [-- Base case: n = 0, p is nonzero constant, contradiction
      FIRST_ASSUM (MP_TAC o MATCH_MP POLY_DEG_EQ_0) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"c:A") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"~(c = ring_0 (k:A ring))") ASSUME_TAC THENL
       [ASM_MESON_TAC [POLY_CONST_0, POLY_RING_CLAUSES], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(f:A->B) c = ring_0 (l:B ring)") ASSUME_TAC THENL
      [UNDISCH_TAC (← q r"poly_eval (l:B ring) ((f:A->B) o (p:(1->num)->A)) (x:B) =
         ring_0 l") THEN SUBGOAL_THEN
         (← q r"(f:A->B) c IN ring_carrier (l:B ring)") ASSUME_TAC THENL
        [ASM_MESON_TAC [ring_homomorphism, SUBSET, IN_IMAGE], ALL_TAC] THEN
       SUBGOAL_THEN
         (← q r"(f:A->B) o (poly_const (k:A ring) c:(1->num)->A) =
          (poly_const (l:B ring) (f c):(1->num)->B)") ASSUME_TAC THENL
        [MATCH_MP_TAC POLY_COMPOSE_HOMOMORPHISM_CONST THEN
         ASM_REWRITE_TAC [], ALL_TAC] THEN
       ASM_SIMP_TAC [POLY_EVAL_CONST],
       ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"k:A ring", ← q r"l:B ring", ← q r"f:A->B", ← q r"c:A"]
        RING_MONOMORPHISM_EQ_0) THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN -- Inductive step: n >= 1  -- Get root from ACF
     FIRST_ASSUM (MP_TAC o SPEC (← q r"p:(1->num)->A")) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
     DISCH_THEN (X_CHOOSE_THEN (← q r"y:A") STRIP_ASSUME_TAC) THEN
     -- Factor p = (X-y) * q
     SUBGOAL_THEN (← q r"?q:(1->num)->A.
         q IN ring_carrier(poly_ring (k:A ring) (:1)) /\
         p:(1->num)->A = poly_mul k
             (poly_sub k (poly_var k one) (poly_const k (y:A))) q")
      (X_CHOOSE_THEN (← q r"q:(1->num)->A") STRIP_ASSUME_TAC) THENL
     [MP_TAC (← ISPECL [← q r"k:A ring", ← q r"y:A", ← q r"p:(1->num)->A"]
        POLY_DIVIDES_X_MINUS_ROOT) THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [ring_divides, POLY_RING_CLAUSES,
                  IN_ELIM_THM, SUBSET_UNIV] THEN
      MESON_TAC [], ALL_TAC] THEN
     SUBGOAL_THEN (← q r"ring_polynomial (k:A ring) (q:(1->num)->A) /\
      poly_sub k (poly_var k one) (poly_const k (y:A)):(1->num)->A
       IN ring_carrier(poly_ring (k:A ring) (:1))") STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC [RING_POLYNOMIAL],
       MATCH_MP_TAC POLY_X_MINUS_A_IN_CARRIER THEN ASM_REWRITE_TAC []],
      ALL_TAC] THEN
     SUBGOAL_THEN (← q r"~(q:(1->num)->A = poly_0 (k:A ring))") ASSUME_TAC THENL
     [DISCH_TAC THEN SUBGOAL_THEN
       (← q r"(p:(1->num)->A) = poly_0 (k:A ring)") MP_TAC THENL
       [ASM_REWRITE_TAC [POLY_CLAUSES] THEN
        MATCH_MP_TAC RING_MUL_RZERO THEN MATCH_MP_TAC RING_SUB THEN
        REWRITE_TAC [← GSYM RING_POLYNOMIAL] THEN
        ASM_SIMP_TAC [RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST],
        REWRITE_TAC [POLY_CLAUSES] THEN ASM_MESON_TAC []], ALL_TAC] THEN
     SUBGOAL_THEN (← q r"poly_deg (k:A ring) (q:(1->num)->A) < n") ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"k:A ring", ← q r"y:A", ← q r"q:(1->num)->A"]
        POLY_DEG_MUL_X_MINUS_A) THEN
      ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN
      UNDISCH_TAC (← q r"poly_deg (k:A ring) (p:(1->num)->A) = n") THEN
      ASM_REWRITE_TAC [] THEN ARITH_TAC, ALL_TAC] THEN
     SUBGOAL_THEN (← q r"(f:A->B) o (p:(1->num)->A) = poly_mul (l:B ring)
         (f o poly_sub k (poly_var k one) (poly_const k (y:A)))
         (f o (q:(1->num)->A))") ASSUME_TAC THENL
     [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC POLY_COMPOSE_HOMOMORPHISM_MUL THEN
      ASM_SIMP_TAC [RING_POWERSERIES_SUB, RING_POWERSERIES_VAR,
                   RING_POWERSERIES_CONST,
                   RING_POLYNOMIAL_IMP_POWERSERIES], ALL_TAC] THEN
     -- f o (X-y) = X_l - const_l(f y)
     SUBGOAL_THEN (← q r"(f:A->B) o poly_sub (k:A ring) (poly_var k one)
                              (poly_const k (y:A)) =
       poly_sub (l:B ring) (poly_var l one)
                            (poly_const l ((f:A->B) y))") ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"k:A ring", ← q r"l:B ring", ← q r"f:A->B",
        ← q r"poly_var k one:(1->num)->A", ← q r"poly_const k (y:A):(1->num)->A"]
       POLY_COMPOSE_HOMOMORPHISM_SUB) THEN
      ASM_SIMP_TAC [RING_POWERSERIES_VAR, RING_POWERSERIES_CONST] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN
        (← q r"((f:A->B) o (poly_var (k:A ring) one:(1->num)->A) =
          (poly_var (l:B ring) one:(1->num)->B)) /\
         ((f:A->B) o (poly_const (k:A ring) (y:A):(1->num)->A) =
          (poly_const (l:B ring) (f y):(1->num)->B))")
        (fun th => tactic_of do pure (REWRITE_TAC [th])) THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC POLY_COMPOSE_HOMOMORPHISM_VAR THEN
       ASM_REWRITE_TAC [],
       MATCH_MP_TAC POLY_COMPOSE_HOMOMORPHISM_CONST THEN
       ASM_REWRITE_TAC []],
      ALL_TAC] THEN
     SUBGOAL_THEN (← q r"(f:A->B) y IN ring_carrier (l:B ring) /\
      ring_polynomial (l:B ring) ((f:A->B) o (q:(1->num)->A))")
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [ring_homomorphism, SUBSET, IN_IMAGE,
       RING_POLYNOMIAL, IN_RING_POLYNOMIAL_CARRIER_COMPOSE], ALL_TAC] THEN
     SUBGOAL_THEN (← q r"ring_sub (l:B ring) (x:B) ((f:A->B) y) = ring_0 l \/
       poly_eval (l:B ring) ((f:A->B) o (q:(1->num)->A)) (x:B) = ring_0 l")
      MP_TAC THENL [MP_TAC (← ISPECL [← q r"l:B ring",
        ← q r"ring_sub (l:B ring) (x:B) ((f:A->B) y)",
        ← q r"poly_eval (l:B ring) ((f:A->B) o (q:(1->num)->A)) (x:B)"]
       FIELD_MUL_EQ_0) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
      [CONJ_TAC THENL [MATCH_MP_TAC RING_SUB THEN ASM_REWRITE_TAC [],
        REWRITE_TAC [POLY_EVAL]], ALL_TAC] THEN
      DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← GSYM th])) THEN UNDISCH_TAC
       (← q r"poly_eval (l:B ring) ((f:A->B) o (p:(1->num)->A)) (x:B) =
        ring_0 l") THEN ASM_REWRITE_TAC [] THEN
      ASM_SIMP_TAC [POLY_EVAL_MUL, POLY_EVAL_SUB, POLY_EVAL_VAR,
                    POLY_EVAL_CONST, RING_POLYNOMIAL_VAR,
                    RING_POLYNOMIAL_CONST, RING_POLYNOMIAL_SUB,
                    RING_POLYNOMIAL_MUL], ALL_TAC] THEN
     -- Case split
     DISCH_THEN (DISJ_CASES_TAC) THENL
     [-- Case 1: ring_sub l x (f y) = 0, so x = f y
      REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"y:A") THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [RING_SUB_EQ_0],
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"poly_deg (k:A ring) (q:(1->num)->A)")) THEN
        ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o SPECL [← q r"x:B", ← q r"q:(1->num)->A"]) THEN
      ASM_REWRITE_TAC [POLY_RING_CLAUSES]], DISCH_TAC THEN
     REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN
     FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:B")) THEN ASM_REWRITE_TAC [] THEN
     DISCH_THEN (X_CHOOSE_THEN (← q r"p0:(1->num)->A") STRIP_ASSUME_TAC) THEN
     FIRST_X_ASSUM (MP_TAC o SPECL
      [← q r"poly_deg (k:A ring) (p0:(1->num)->A)", ← q r"x:B", ← q r"p0:(1->num)->A"]) THEN
     ASM_REWRITE_TAC []])

  -- @@RETURN BEGIN
  return { algebraically_closed_field, ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD,
           ALGEBRAICALLY_CLOSED_FIELD_ISOMORPHIC_IMAGE,
           ISOMORPHIC_RING_ALGEBRAICALLY_CLOSED_FIELD,
           ALGEBRAICALLY_CLOSED_FIELD_IMP_INFINITE,
           ALGEBRAICALLY_CLOSED_FIELD_NO_PROPER_ALGEBRAIC_EXTENSION }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Irreducibles, decomposition and splitting over an ACF.                    -/
/- ------------------------------------------------------------------------- -/

structure AcfSplit where
  -- @@FIELDS
  ALGEBRAICALLY_CLOSED_FIELD_EQ_IRREDUCIBLES : thm
  IRREDUCIBLE_ALGEBRAICALLY_CLOSED_FIELD : thm
  ALGEBRAICALLY_CLOSED_FIELD_DECOMPOSE : thm
  ALGEBRAICALLY_CLOSED_FIELD_SPLITS : thm
  deriving Inhabited

@[nospecialize]
def setupAcfSplit [HolBase] (D : FieldTheoryDeps) (BAcfBasic : AcfBasic) :
    ExceptT String IO AcfSplit := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, .. } := D
  let { ARITH_EQ, CONJ_ASSOC, .. } := D.core1
  let { FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING, FIELD_UNIT, .. } := D.core2
  let { IMP_CONJ_ALT, INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING, INTEGRAL_DOMAIN_POLY_RING,
        IN_ELIM_THM, IN_NUMSEG, .. } := D.core3
  let { MONO_EXISTS, NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS, PID_IMP_UFD,
        PID_POLY_RING, POLY_CLAUSES, POLY_CONST, POLY_CONST_0, POLY_CONST_1,
        POLY_CONST_EQ, POLY_CONST_EQ_0, POLY_DEG_0, POLY_DEG_1_IMP_IRREDUCIBLE,
        POLY_DEG_1_ROOT, POLY_DEG_CONST, POLY_DEG_EQ_0, POLY_DEG_MUL_X_MINUS_A,
        POLY_DEG_X_MINUS_A, POLY_DIVIDES_X_MINUS_ROOT, .. } := D.core4
  let { POLY_MUL_0, POLY_MUL_RID, POLY_RING, POLY_RING_CLAUSES, POLY_VAR_UNIV,
        POLY_X_MINUS_A_IN_CARRIER, .. } := D.core5
  let { RING_DIVIDES_HOMOMORPHIC_IMAGE, RING_DIVIDES_ZERO, RING_HOMOMORPHISM_POLY_EVAL,
        RING_IRREDUCIBLE_IN_CARRIER, .. } := D.core6
  let { RING_MUL_ASSOC, RING_MUL_RZERO, RING_MUL_SYM, RING_POLYNOMIAL,
        RING_POLYNOMIAL_CONST, RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR,
        RING_POWERSERIES_CONST, RING_PRODUCT, RING_PRODUCT_CLAUSES_NUMSEG,
        RING_PRODUCT_CLAUSES_NUMSEG_ALT, RING_PRODUCT_EQ, RING_SUB, RING_UNIT_0,
        RING_UNIT_POLY_DOMAIN, .. } := D.core7
  let { SUBSET_UNIV, .. } := D.core8
  let { ring_divides, ring_irreducible, ring_unit, .. } := D.core9
  let { ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD, algebraically_closed_field, .. } := BAcfBasic
  -- @@SCOPE END

  let ALGEBRAICALLY_CLOSED_FIELD_EQ_IRREDUCIBLES ← prove
   r"!k:A ring.
        algebraically_closed_field k <=>
        field k /\
        !p. ring_irreducible (poly_ring k (:1)) p ==> poly_deg k p = 1"
   (GEN_TAC THEN EQ_TAC THENL
     [-- Forward: ACF ==> field /\ irreducibles have degree 1
      DISCH_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC [ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD], ALL_TAC] THEN
      X_GEN_TAC (← q r"p:(1->num)->A") THEN
      REWRITE_TAC [ring_irreducible, POLY_RING_CLAUSES, IN_ELIM_THM] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN (← q r"field (k:A ring) /\ integral_domain (k:A ring) /\
        ~trivial_ring (k:A ring)") STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC [ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD,
         FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"~(poly_deg (k:A ring) (p:(1->num)->A) = 0)") ASSUME_TAC THENL
       [DISCH_TAC THEN
        UNDISCH_TAC (← q r"~ring_unit (poly_ring (k:A ring) (:1)) (p:(1->num)->A)")
          THEN REWRITE_TAC [] THEN
        ASM_SIMP_TAC [RING_UNIT_POLY_DOMAIN] THEN
        MP_TAC (← ISPECL [← q r"k:A ring", ← q r"p:(1->num)->A"] POLY_DEG_EQ_0) THEN
          ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"a:A") THEN ASM_REWRITE_TAC [] THEN
        ASM_SIMP_TAC [FIELD_UNIT] THEN ASM_MESON_TAC [POLY_CONST_0], ALL_TAC] THEN
      FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [algebraically_closed_field]) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC (← q r"p:(1->num)->A"))) THEN
      ASM_REWRITE_TAC [POLY_RING_CLAUSES, IN_ELIM_THM, SUBSET_UNIV] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"x:A") STRIP_ASSUME_TAC) THEN
      -- (X - x) divides p
      MP_TAC (← ISPECL [← q r"k:A ring", ← q r"x:A", ← q r"p:(1->num)->A"]
             POLY_DIVIDES_X_MINUS_ROOT) THEN
      ASM_REWRITE_TAC [POLY_RING_CLAUSES, IN_ELIM_THM, SUBSET_UNIV] THEN
      REWRITE_TAC [ring_divides, POLY_RING_CLAUSES, IN_ELIM_THM] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
         (X_CHOOSE_THEN (← q r"q:(1->num)->A") STRIP_ASSUME_TAC))) THEN
      FIRST_X_ASSUM (MP_TAC o SPECL
        [← q r"poly_sub (k:A ring) (poly_var k one) (poly_const k x)",
         ← q r"q:(1->num)->A"]) THEN
      REWRITE_TAC [POLY_RING_CLAUSES, IN_ELIM_THM, SUBSET_UNIV] THEN
      ASM_SIMP_TAC [RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR,
                   RING_POLYNOMIAL_CONST, POLY_VAR_UNIV] THEN
                     ASM_REWRITE_TAC [] THEN
      DISCH_THEN (DISJ_CASES_TAC) THENL
       [-- Case: (X - x) is a unit - impossible since deg = 1
        UNDISCH_TAC (← q r"ring_unit (poly_ring (k:A ring) (:1))
          (poly_sub k (poly_var k one) (poly_const k (x:A)))") THEN
        ASM_SIMP_TAC [RING_UNIT_POLY_DOMAIN] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"u:A") STRIP_ASSUME_TAC) THEN
        MP_TAC (← SPECL [← q r"k:A ring", ← q r"x:A"] POLY_DEG_X_MINUS_A) THEN
        ASM_REWRITE_TAC [POLY_DEG_CONST] THEN ARITH_TAC, ALL_TAC] THEN
      -- Case: q is a unit, so p = (X - x) * unit, deg p = 1
      UNDISCH_TAC
        (← q r"ring_unit (poly_ring (k:A ring) (:1)) (q:(1->num)->A)") THEN
      ASM_SIMP_TAC [RING_UNIT_POLY_DOMAIN] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"u:A") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"(u:A) IN ring_carrier k") ASSUME_TAC THENL
       [ASM_MESON_TAC [ring_unit], ALL_TAC] THEN UNDISCH_TAC
        (← q r"p:(1->num)->A = poly_mul k
           (poly_sub k (poly_var k one) (poly_const k (x:A))) q") THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [← q r"k:A ring", ← q r"x:A",
        ← q r"poly_const (k:A ring) (u:A):(1->num)->A"]
        POLY_DEG_MUL_X_MINUS_A) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [CONJ_TAC THENL [REWRITE_TAC [← GSYM RING_POLYNOMIAL] THEN
          ASM_SIMP_TAC [RING_POLYNOMIAL_CONST],
          REWRITE_TAC [← GSYM POLY_CONST_0, POLY_CONST_EQ] THEN
          ASM_MESON_TAC [RING_UNIT_0, INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING]],
        ASM_REWRITE_TAC [POLY_DEG_CONST] THEN ARITH_TAC],
      STRIP_TAC THEN ASM_REWRITE_TAC [algebraically_closed_field] THEN
      X_GEN_TAC (← q r"p:(1->num)->A") THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"integral_domain (k:A ring) /\
        ~((p:(1->num)->A) = ring_0 (poly_ring k (:1)))") STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN],
          ASM_MESON_TAC [POLY_DEG_0, POLY_RING_CLAUSES]], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"~ring_unit (poly_ring (k:A ring) (:1)) (p:(1->num)->A)")
      ASSUME_TAC THENL [ASM_SIMP_TAC [RING_UNIT_POLY_DOMAIN] THEN STRIP_TAC THEN
        UNDISCH_TAC (← q r"~(poly_deg (k:A ring) (p:(1->num)->A) = 0)") THEN
        ASM_REWRITE_TAC [POLY_DEG_CONST], ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"poly_ring (k:A ring) (:1)", ← q r"p:(1->num)->A"]
        NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS) THEN
      ASM_SIMP_TAC [INTEGRAL_DOMAIN_POLY_RING] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN DISJ2_TAC THEN MATCH_MP_TAC PID_IMP_UFD THEN
        ASM_SIMP_TAC [PID_POLY_RING], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"q:(1->num)->A") STRIP_ASSUME_TAC) THEN
      MP_TAC (← ISPECL [← q r"k:A ring", ← q r"q:(1->num)->A"] POLY_DEG_1_ROOT) THEN
      ANTS_TAC THENL [ASM_MESON_TAC [ring_irreducible, RING_POLYNOMIAL,
                       POLY_RING_CLAUSES, IN_ELIM_THM], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"x:A") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"x:A") THEN ASM_REWRITE_TAC [] THEN
      MP_TAC (← ISPECL [← q r"poly_ring (k:A ring) (:1)", ← q r"k:A ring",
        ← q r"\(pp:(1->num)->A). poly_eval (k:A ring) pp (x:A)",
        ← q r"q:(1->num)->A", ← q r"p:(1->num)->A"] RING_DIVIDES_HOMOMORPHIC_IMAGE) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC [RING_HOMOMORPHISM_POLY_EVAL], ALL_TAC] THEN
      BETA_TAC THEN ASM_REWRITE_TAC [RING_DIVIDES_ZERO]])

  let IRREDUCIBLE_ALGEBRAICALLY_CLOSED_FIELD ← prove
   r"!(k:A ring) p.
        algebraically_closed_field k
        ==> (ring_irreducible (poly_ring k (:1)) p <=>
             p IN ring_carrier (poly_ring k (:1)) /\ poly_deg k p = 1)"
   (MESON_TAC [POLY_DEG_1_IMP_IRREDUCIBLE, RING_IRREDUCIBLE_IN_CARRIER,
              ALGEBRAICALLY_CLOSED_FIELD_EQ_IRREDUCIBLES])

  let ALGEBRAICALLY_CLOSED_FIELD_DECOMPOSE ← prove
   r"!k:A ring.
     algebraically_closed_field k
     ==> !p. p IN ring_carrier(poly_ring k (:1)) /\ ~(poly_deg k p = 0)
             ==> ?a q. a IN ring_carrier k /\
                       q IN ring_carrier(poly_ring k (:1)) /\ p = poly_mul k
                         (poly_sub k (poly_var k one) (poly_const k a)) q /\
                       poly_deg k q + 1 = poly_deg k p"
   (GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC (← q r"p:(1->num)->A") THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"field (k:A ring)") ASSUME_TAC THENL
     [ASM_MESON_TAC [ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"?a:A. a IN ring_carrier k /\ poly_eval k p a = ring_0 k")
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [algebraically_closed_field], ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"a:A", ← q r"p:(1->num)->A"]
      POLY_DIVIDES_X_MINUS_ROOT) THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [ring_divides, POLY_RING_CLAUSES, IN_ELIM_THM, SUBSET_UNIV] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN (← q r"q:(1->num)->A") STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC (← q r"a:A") THEN EXISTS_TAC (← q r"q:(1->num)->A") THEN
    ASM_REWRITE_TAC [POLY_RING_CLAUSES, IN_ELIM_THM, SUBSET_UNIV] THEN
    SUBGOAL_THEN (← q r"~((q:(1->num)->A) = poly_0 (k:A ring))") ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN (← q r"(p:(1->num)->A) = poly_0 (k:A ring)") MP_TAC THENL
       [ASM_REWRITE_TAC [POLY_CLAUSES] THEN
        MATCH_MP_TAC RING_MUL_RZERO THEN MATCH_MP_TAC RING_SUB THEN
        REWRITE_TAC [← GSYM RING_POLYNOMIAL] THEN
        ASM_SIMP_TAC [RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST],
        ASM_MESON_TAC [POLY_DEG_0]], ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"a:A", ← q r"q:(1->num)->A"]
      POLY_DEG_MUL_X_MINUS_A) THEN
    ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN,
                 POLY_RING_CLAUSES, IN_ELIM_THM, SUBSET_UNIV] THEN
    ARITH_TAC)

  let ALGEBRAICALLY_CLOSED_FIELD_SPLITS ← prove
   r"!(k:A ring) p.
        algebraically_closed_field k /\
        p IN ring_carrier(poly_ring k (:1)) /\ ~(p = poly_0 k)
        ==> ?c a. c IN ring_carrier k /\ ~(c = ring_0 k) /\
                  (!i. 1 <= i /\ i <= poly_deg k p
                       ==> a(i) IN ring_carrier k) /\
                  p = poly_mul k (poly_const k c)
                        (ring_product (poly_ring k (:1)) (1..poly_deg k p)
                           (\i. poly_sub k (poly_var k one)
                                           (poly_const k (a i))))"
   (← do
    let a4 ← D.ARITH_RULE (← q r"~(SUC n <= n)")
    let a3 ← D.ARITH_RULE (← q r"1 <= SUC n")
    let a2 ← D.ARITH_RULE (← q r"~(SUC n = 0)")
    let a1 ← D.ARITH_RULE (← q r"~(1 <= i /\ i <= 0)")
    pure (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    SUBGOAL_THEN (← q r"field (k:A ring) /\ integral_domain (k:A ring)")
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD,
                    FIELD_IMP_INTEGRAL_DOMAIN],
      ALL_TAC] THEN
    ABBREV_TAC (← q r"n = poly_deg k (p:(1->num)->A)") THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [← GSYM IMP_CONJ_ALT, ← GSYM CONJ_ASSOC] THEN
    MAP_EVERY (fun t => SPEC_TAC (t, t)) [← q r"p:(1->num)->A", ← q r"n:num"] THEN
    INDUCT_TAC THEN X_GEN_TAC (← q r"p:(1->num)->A") THEN STRIP_TAC THENL
     [UNDISCH_TAC (← q r"poly_deg k (p:(1->num)->A) = 0") THEN
      ASM_SIMP_TAC [POLY_DEG_EQ_0, RING_POLYNOMIAL] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"c:A") THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
      REWRITE_TAC [RING_PRODUCT_CLAUSES_NUMSEG, ARITH_EQ] THEN
      ASM_REWRITE_TAC [POLY_CONST_1, POLY_RING] THEN
      REWRITE_TAC [a1] THEN
      ASM_SIMP_TAC [POLY_MUL_RID, RING_POWERSERIES_CONST] THEN
      ASM_MESON_TAC [POLY_CONST_EQ_0],
      ALL_TAC] THEN
    MP_TAC (← SPEC (← q r"k:A ring") ALGEBRAICALLY_CLOSED_FIELD_DECOMPOSE) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o SPEC (← q r"p:(1->num)->A")) THEN
    ASM_REWRITE_TAC [a2] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"a0:A")
      (X_CHOOSE_THEN (← q r"q:(1->num)->A") STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN (← q r"poly_deg (k:A ring) (q:(1->num)->A) = n") ASSUME_TAC THENL
     [ASM_ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN
      (← q r"poly_sub (k:A ring) (poly_var k one) (poly_const k (a0:A))
       IN ring_carrier(poly_ring k (:1))") ASSUME_TAC THENL
     [MATCH_MP_TAC POLY_X_MINUS_A_IN_CARRIER THEN ASM_REWRITE_TAC [],
       ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"q:(1->num)->A")) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [ASM_MESON_TAC [POLY_MUL_0, RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_CONST,
                    RING_POLYNOMIAL_VAR],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"c':A")
      (X_CHOOSE_THEN (← q r"a':num->A") STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC (← q r"c':A") THEN
    EXISTS_TAC
      (← q r"\i:num. if i = SUC n then (a0:A) else (a':num->A) i") THEN
    ASM_REWRITE_TAC [] THEN
    CONJ_TAC THENL
     [X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
      COND_CASES_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_product (poly_ring (k:A ring) (:1)) (1..SUC n)
         (\i. poly_sub k (poly_var k one)
                (poly_const k (if i = SUC n then a0 else (a':num->A) i)))
         :(1->num)->A = poly_mul k
         (poly_sub k (poly_var k one) (poly_const k (a0:A)))
         (ring_product (poly_ring k (:1)) (1..n)
           (\i. poly_sub k (poly_var k one) (poly_const k (a' i))))")
      SUBST1_TAC THENL
     [REWRITE_TAC [RING_PRODUCT_CLAUSES_NUMSEG_ALT, a3] THEN
      ASM_REWRITE_TAC [a4] THEN
      REWRITE_TAC [POLY_RING_CLAUSES] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC RING_PRODUCT_EQ THEN REWRITE_TAC [IN_NUMSEG] THEN
      X_GEN_TAC (← q r"j:num") THEN STRIP_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"poly_mul (k:A ring) = ring_mul
      (poly_ring k (:1))") SUBST1_TAC THENL
     [REWRITE_TAC [POLY_RING_CLAUSES], ALL_TAC] THEN
    ASM_SIMP_TAC [RING_MUL_ASSOC, POLY_CONST, RING_PRODUCT] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC RING_MUL_SYM THEN
    ASM_REWRITE_TAC [POLY_CONST, RING_PRODUCT]))

  -- @@RETURN BEGIN
  return { ALGEBRAICALLY_CLOSED_FIELD_EQ_IRREDUCIBLES,
           IRREDUCIBLE_ALGEBRAICALLY_CLOSED_FIELD, ALGEBRAICALLY_CLOSED_FIELD_DECOMPOSE,
           ALGEBRAICALLY_CLOSED_FIELD_SPLITS }
  -- @@RETURN END

structure ClosedFieldSplits where
  -- @@FIELDS
  ALGEBRAICALLY_CLOSED_FIELD_EQ_SPLITS_ALT : thm
  ALGEBRAICALLY_CLOSED_FIELD_EQ_SPLITS : thm
  deriving Inhabited

@[nospecialize]
def setupClosedFieldSplits [HolBase] (D : FieldTheoryDeps) (BAcfBasic : AcfBasic) (BAcfSplit : AcfSplit) :
    ExceptT String IO ClosedFieldSplits := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, .. } := D
  let { FIELD_IMP_INTEGRAL_DOMAIN, FINITE_NUMSEG, .. } := D.core2
  let { INTEGRAL_DOMAIN_PRODUCT_EQ_0, IN_NUMSEG, LE_REFL, .. } := D.core3
  let { POLY_DEG_0, POLY_EVAL_CONST, POLY_EVAL_MUL, .. } := D.core4
  let { POLY_EVAL_RING_PRODUCT, POLY_EVAL_SUB, POLY_EVAL_VAR,
        POLY_X_MINUS_A_IN_CARRIER, .. } := D.core5
  let { RING_MUL_RZERO, RING_POLYNOMIAL, RING_POLYNOMIAL_CONST, RING_POLYNOMIAL_VAR,
        RING_PRODUCT, RING_PRODUCT_EQ, RING_SUB_REFL, .. } := D.core7
  let { ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD, algebraically_closed_field, .. } := BAcfBasic
  let { ALGEBRAICALLY_CLOSED_FIELD_SPLITS, .. } := BAcfSplit
  -- @@SCOPE END

  let ALGEBRAICALLY_CLOSED_FIELD_EQ_SPLITS_ALT ← prove
   r"!k:A ring.
     algebraically_closed_field k <=>
     field k /\
     !p. p IN ring_carrier(poly_ring k (:1)) /\ ~(poly_deg k p = 0)
         ==> ?c a. c IN ring_carrier k /\ ~(c = ring_0 k) /\
                   (!i. 1 <= i /\ i <= poly_deg k p
                        ==> a(i) IN ring_carrier k) /\
                   p = poly_mul k (poly_const k c)
                         (ring_product (poly_ring k (:1)) (1..poly_deg k p)
                           (\i. poly_sub k (poly_var k one)
                                           (poly_const k (a i))))"
   (GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC [ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD], ALL_TAC] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC ALGEBRAICALLY_CLOSED_FIELD_SPLITS THEN
      ASM_MESON_TAC [POLY_DEG_0],
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [algebraically_closed_field] THEN
    X_GEN_TAC (← q r"p:(1->num)->A") THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"p:(1->num)->A")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"c:A")
      (X_CHOOSE_THEN (← q r"a:num->A") STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN (← q r"integral_domain (k:A ring)") ASSUME_TAC THENL
     [ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"1 <= poly_deg (k:A ring) (p:(1->num)->A)") ASSUME_TAC THENL
     [ASM_ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(a:num->A) 1 IN ring_carrier k") ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [LE_REFL], ALL_TAC] THEN
    EXISTS_TAC (← q r"(a:num->A) 1") THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC
     (← q r"Q = ring_product (poly_ring (k:A ring) (:1))
            (1..poly_deg k (p:(1->num)->A)) (\i. poly_sub k (poly_var k
              one)
                            (poly_const k ((a:num->A) i)))") THEN
    SUBGOAL_THEN (← q r"ring_polynomial (k:A ring) (Q:(1->num)->A)") ASSUME_TAC THENL
     [EXPAND_TAC "Q" THEN REWRITE_TAC [RING_POLYNOMIAL, RING_PRODUCT],
       ALL_TAC] THEN
    ASM_SIMP_TAC [POLY_EVAL_MUL, RING_POLYNOMIAL_CONST, POLY_EVAL_CONST] THEN
    -- Goal: ring_mul k c (poly_eval k Q (a 1)) = ring_0 k
    SUBGOAL_THEN
     (← q r"poly_eval (k:A ring) (Q:(1->num)->A) ((a:num->A) 1) = ring_0 k")
    SUBST1_TAC THENL
     [-- Step 1: Expand Q and apply POLY_EVAL_RING_PRODUCT
      EXPAND_TAC "Q" THEN SUBGOAL_THEN (← q r"poly_eval (k:A ring)
          (ring_product (poly_ring k (:1)) (1..poly_deg k (p:(1->num)->A))
            (\i. poly_sub k (poly_var k one)
                            (poly_const k ((a:num->A) i)))) ((a:num->A) 1) =
        ring_product k (1..poly_deg k p) (\i. poly_eval k
            (poly_sub k (poly_var k one) (poly_const k (a i)))
            (a 1))") SUBST1_TAC THENL [MATCH_MP_TAC POLY_EVAL_RING_PRODUCT THEN
        ASM_REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC POLY_X_MINUS_A_IN_CARRIER THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"ring_product (k:A ring) (1..poly_deg k (p:(1->num)->A))
          (\i. poly_eval k (poly_sub k (poly_var k one)
                        (poly_const k ((a:num->A) i))) ((a:num->A) 1)) =
        ring_product k (1..poly_deg k p)
          (\i. ring_sub k (a 1) (a i))") SUBST1_TAC THENL
       [MATCH_MP_TAC RING_PRODUCT_EQ THEN
        REWRITE_TAC [IN_NUMSEG] THEN X_GEN_TAC (← q r"j:num") THEN STRIP_TAC THEN
          BETA_TAC THEN
        SUBGOAL_THEN (← q r"(a:num->A) j IN ring_carrier k") ASSUME_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
        ASM_SIMP_TAC [POLY_EVAL_SUB, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST,
                      POLY_EVAL_VAR, POLY_EVAL_CONST], ALL_TAC] THEN
      MP_TAC (← SPEC (← q r"\i:num. ring_sub (k:A ring) ((a:num->A) 1) (a i)")
        (← MATCH_MP (← REWRITE_RULE [FINITE_NUMSEG] (← ISPECL [← q r"k:A ring",
                     ← q r"1..poly_deg (k:A ring) (p:(1->num)->A)"]
              INTEGRAL_DOMAIN_PRODUCT_EQ_0))
          (← ASSUME (← q r"integral_domain (k:A ring)")))) THEN
      DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
      EXISTS_TAC (← q r"1") THEN REWRITE_TAC [IN_NUMSEG, LE_REFL] THEN
      BETA_TAC THEN ASM_SIMP_TAC [RING_SUB_REFL] THEN ASM_REWRITE_TAC [],
      -- ring_mul k c (ring_0 k) = ring_0 k
      ASM_SIMP_TAC [RING_MUL_RZERO]])

  let ALGEBRAICALLY_CLOSED_FIELD_EQ_SPLITS ← prove
   r"!k:A ring.
     algebraically_closed_field k <=>
     field k /\
     !p. p IN ring_carrier(poly_ring k (:1)) /\ ~(p = poly_0 k)
         ==> ?c a. c IN ring_carrier k /\ ~(c = ring_0 k) /\
                   (!i. 1 <= i /\ i <= poly_deg k p
                        ==> a(i) IN ring_carrier k) /\
                   p = poly_mul k (poly_const k c)
                         (ring_product (poly_ring k (:1)) (1..poly_deg k p)
                           (\i. poly_sub k (poly_var k one)
                                           (poly_const k (a i))))"
   (GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC [ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD], ALL_TAC] THEN
      ASM_SIMP_TAC [ALGEBRAICALLY_CLOSED_FIELD_SPLITS],
      REWRITE_TAC [ALGEBRAICALLY_CLOSED_FIELD_EQ_SPLITS_ALT] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC [POLY_DEG_0]])

  -- @@RETURN BEGIN
  return { ALGEBRAICALLY_CLOSED_FIELD_EQ_SPLITS_ALT,
           ALGEBRAICALLY_CLOSED_FIELD_EQ_SPLITS }
  -- @@RETURN END

structure SimpleExtendHom where
  -- @@FIELDS
  SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM : thm
  deriving Inhabited

@[nospecialize]
def setupSimpleExtendHom [HolBase] (D : FieldTheoryDeps) (BAcfBasic : AcfBasic) :
    ExceptT String IO SimpleExtendHom := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, .. } := D
  let { FIELD_UNIT, IDEAL_GENERATED_0, IDEAL_GENERATED_MINIMAL,
        IDEAL_GENERATED_SING_EQ_CARRIER, IMAGE_POLY_EXTEND_1, .. } := D.core2
  let { INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING, IN_ELIM_THM, IN_UNIV, .. } := D.core3
  let { PID, PID_POLY_RING, POLY_CONST, POLY_CONST_0, POLY_DEG_EQ_0,
        POLY_DEG_MONOMORPHIC_IMAGE, .. } := D.core4
  let { POLY_EXTEND_CONST, POLY_EXTEND_EVALUATE, POLY_RING_CLAUSES, RING_0, RING_1, .. } := D.core5
  let { RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_EPIMORPHISM_FACTOR,
        RING_HOMOMORPHISM_INTO_SUBRING_EQ_GEN, RING_HOMOMORPHISM_POLY_EXTEND,
        RING_IDEAL_RING_KERNEL, .. } := D.core6
  let { RING_POLYNOMIAL, RING_POLYNOMIAL_COMPOSE, RING_UNIT_POLY_CONST, SING_SUBSET,
        SUBRING_GENERATED, .. } := D.core7
  let { SUBSET_REFL, TRIVIAL_RING_10, .. } := D.core8
  let { poly_eval, principal_ideal, ring_epimorphism, ring_kernel, ring_monomorphism, .. } := D.core9
  let { algebraically_closed_field, .. } := BAcfBasic
  -- @@SCOPE END

  let SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM ← prove
   r"!(k:A ring) (l:B ring) (l':C ring) (f:A->B) (g:A->C) a.
        field k /\ integral_domain l /\
        ring_monomorphism(k,l) f /\ a IN ring_carrier l /\
        algebraic_over(k,l) f a /\ algebraically_closed_field l' /\
        ring_monomorphism(k,l') g
        ==> ?h. ring_homomorphism
                 (subring_generated l (a INSERT IMAGE f (ring_carrier k)),
                  l') h /\
                (!x. x IN ring_carrier k ==> h(f x) = g x)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"ring_homomorphism(k:A ring,l:B ring) (f:A->B) /\
      ring_homomorphism(k:A ring,l':C ring) (g:A->C)") STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [ring_monomorphism], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_epimorphism(poly_ring (k:A ring) (:1),
                        subring_generated (l:B ring)
                          ((a:B) INSERT IMAGE (f:A->B) (ring_carrier k)))
        (poly_extend(k,l) f (\v:1. a))") ASSUME_TAC THENL
     [REWRITE_TAC [ring_epimorphism, RING_HOMOMORPHISM_INTO_SUBRING_EQ_GEN] THEN
      ASM_SIMP_TAC [RING_HOMOMORPHISM_POLY_EXTEND, IN_UNIV] THEN
      MP_TAC (← ISPECL [← q r"f:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"a:B"]
        IMAGE_POLY_EXTEND_1) THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [SUBSET_REFL],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"?a'. (a':C) IN ring_carrier l' /\
            ring_kernel(poly_ring (k:A ring) (:1), subring_generated (l:B ring)
                          (a INSERT IMAGE (f:A->B) (ring_carrier k)))
              (poly_extend(k,l) f (\v:1. a)) SUBSET
            ring_kernel(poly_ring (k:A ring) (:1), l':C ring)
              (poly_extend(k,l') (g:A->C) (\v:1. a'))") STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN (← q r"PID(poly_ring (k:A ring) (:1)) /\
        ring_ideal (poly_ring (k:A ring) (:1))
          (ring_kernel(poly_ring (k:A ring) (:1), subring_generated (l:B ring)
                         (a INSERT IMAGE (f:A->B) (ring_carrier k)))
            (poly_extend(k,l) f (\v:1. a)))") STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [MATCH_MP_TAC PID_POLY_RING THEN ASM_REWRITE_TAC [],
          MATCH_MP_TAC RING_IDEAL_RING_KERNEL THEN
          ASM_MESON_TAC [ring_epimorphism]], ALL_TAC] THEN SUBGOAL_THEN
        (← q r"principal_ideal (poly_ring (k:A ring) (:1))
          (ring_kernel(poly_ring (k:A ring) (:1), subring_generated (l:B ring)
                         (a INSERT IMAGE (f:A->B) (ring_carrier k)))
            (poly_extend(k,l) f (\v:1. a)))") MP_TAC THENL
       [FIRST_X_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [PID]) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      REWRITE_TAC [principal_ideal] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:(1->num)->A")
        (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
      SUBGOAL_THEN (← q r"ring_polynomial (k:A ring) (m:(1->num)->A)") ASSUME_TAC THENL
       [ASM_REWRITE_TAC [RING_POLYNOMIAL], ALL_TAC] THEN
      -- g o m is in poly_ring l'
      SUBGOAL_THEN (← q r"(g:A->C) o (m:(1->num)->A) IN
         ring_carrier(poly_ring (l':C ring) (:1))")
      ASSUME_TAC THENL [ASM_MESON_TAC [RING_POLYNOMIAL, RING_POLYNOMIAL_COMPOSE],
        ALL_TAC] THEN
      ASM_CASES_TAC (← q r"poly_deg (k:A ring) (m:(1->num)->A) = 0") THENL
       [-- poly_deg k m = 0: m is either 0 or a unit
        ASM_CASES_TAC
          (← q r"m = ring_0(poly_ring (k:A ring) (:1)):(1->num)->A") THENL
         [-- m = 0: kernel = {0}, any a' works
          EXISTS_TAC (← q r"ring_0(l':C ring)") THEN
          CONJ_TAC THENL [REWRITE_TAC [RING_0], ALL_TAC] THEN
          ASM_REWRITE_TAC [IDEAL_GENERATED_0] THEN
          REWRITE_TAC [SING_SUBSET, ring_kernel, IN_ELIM_THM] THEN CONJ_TAC THENL
           [REWRITE_TAC [RING_0],
            MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN MATCH_MP_TAC
              RING_HOMOMORPHISM_POLY_EXTEND THEN ASM_REWRITE_TAC [IN_UNIV,
                RING_0]],
          SUBGOAL_THEN (← q r"ring_unit (poly_ring (k:A ring) (:1)) (m:(1->num)->A)")
          ASSUME_TAC THENL
           [MP_TAC (← ISPECL [← q r"k:A ring", ← q r"m:(1->num)->A"] POLY_DEG_EQ_0) THEN
             ASM_REWRITE_TAC [] THEN
            DISCH_THEN (X_CHOOSE_THEN (← q r"c:A") STRIP_ASSUME_TAC) THEN
            ASM_REWRITE_TAC [RING_UNIT_POLY_CONST] THEN
            ASM_SIMP_TAC [FIELD_UNIT] THEN DISCH_TAC THEN UNDISCH_TAC
              (← q r"~(m = ring_0(poly_ring (k:A ring) (:1)):(1->num)->A)") THEN
            ASM_REWRITE_TAC [POLY_RING_CLAUSES, ← GSYM POLY_CONST_0], ALL_TAC] THEN
          -- ideal_generated {m} = ring_carrier
          SUBGOAL_THEN
            (← q r"ideal_generated (poly_ring (k:A ring) (:1)) {m:(1->num)->A} =
             ring_carrier(poly_ring (k:A ring) (:1))") ASSUME_TAC THENL
           [ASM_MESON_TAC [IDEAL_GENERATED_SING_EQ_CARRIER], ALL_TAC] THEN
          SUBGOAL_THEN (← q r"F") (fun th => MESON_TAC [th]) THEN
          SUBGOAL_THEN (← q r"poly_extend(k:A ring,l:B ring) (f:A->B) (\v:1. a:B)
              (ring_1(poly_ring (k:A ring) (:1))) =
             ring_0(subring_generated (l:B ring)
               ((a:B) INSERT IMAGE (f:A->B) (ring_carrier (k:A ring))))")
          ASSUME_TAC THENL [SUBGOAL_THEN (← q r"ring_1(poly_ring (k:A ring) (:1)) IN
               ring_kernel(poly_ring (k:A ring) (:1), subring_generated (l:B
                 ring)
                             (a INSERT IMAGE (f:A->B) (ring_carrier k)))
                 (poly_extend(k,l) f (\v:1. a))")
            MP_TAC THENL [ASM_REWRITE_TAC [RING_1], ALL_TAC] THEN
            REWRITE_TAC [ring_kernel, IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN
          SUBGOAL_THEN (← q r"poly_extend(k:A ring,l:B ring) (f:A->B) (\v:1. a:B)
              (ring_1(poly_ring (k:A ring) (:1))) =
             ring_1(subring_generated (l:B ring)
               ((a:B) INSERT IMAGE (f:A->B) (ring_carrier (k:A ring))))")
          ASSUME_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_1 THEN
            ASM_MESON_TAC [ring_epimorphism], ALL_TAC] THEN
          SUBGOAL_THEN (← q r"ring_0 (l:B ring) = ring_1 (l:B ring)") ASSUME_TAC THENL
           [SUBGOAL_THEN (← q r"ring_0(subring_generated (l:B ring)
                ((a:B) INSERT IMAGE (f:A->B) (ring_carrier (k:A ring)))) =
               ring_1(subring_generated (l:B ring)
                ((a:B) INSERT IMAGE (f:A->B) (ring_carrier (k:A ring))))")
            MP_TAC THENL [ASM_MESON_TAC [], REWRITE_TAC [SUBRING_GENERATED]],
              ALL_TAC] THEN
          ASM_MESON_TAC [INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING, TRIVIAL_RING_10]],
        SUBGOAL_THEN (← q r"~(poly_deg (l':C ring) ((g:A->C) o (m:(1->num)->A)) = 0)")
        ASSUME_TAC THENL [ASM_MESON_TAC [POLY_DEG_MONOMORPHIC_IMAGE],
          ALL_TAC] THEN
        MP_TAC (← ISPEC (← q r"l':C ring") algebraically_closed_field) THEN
          ASM_REWRITE_TAC [] THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
          (MP_TAC o SPEC (← q r"(g:A->C) o (m:(1->num)->A)"))) THEN
            ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"a':C") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"a':C") THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN CONJ_TAC THENL
         [REWRITE_TAC [← SET_RULE (← q r"{x:(1->num)->A} SUBSET s <=> x IN s")] THEN
          REWRITE_TAC [ring_kernel, IN_ELIM_THM] THEN CONJ_TAC THENL
           [ASM_REWRITE_TAC [], MP_TAC (← ISPECL [← q r"k:A ring", ← q r"l':C ring", ← q r"g:A->C",
                            ← q r"(\v:1. a':C)", ← q r"m:(1->num)->A"]
              POLY_EXTEND_EVALUATE) THEN
            ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
            ASM_REWRITE_TAC [← GSYM poly_eval]],
          MATCH_MP_TAC RING_IDEAL_RING_KERNEL THEN
          MATCH_MP_TAC RING_HOMOMORPHISM_POLY_EXTEND THEN
          ASM_REWRITE_TAC [IN_UNIV]]], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_homomorphism(poly_ring (k:A ring) (:1), l':C ring)
        (poly_extend(k,l') (g:A->C) (\v:1. a':C))") ASSUME_TAC THENL
     [MATCH_MP_TAC RING_HOMOMORPHISM_POLY_EXTEND THEN ASM_REWRITE_TAC [IN_UNIV],
      ALL_TAC] THEN -- Step 4: Apply RING_HOMOMORPHISM_EPIMORPHISM_FACTOR
    MP_TAC (← ISPECL [← q r"poly_ring (k:A ring) (:1)", ← q r"subring_generated (l:B ring)
          ((a:B) INSERT IMAGE (f:A->B) (ring_carrier k))", ← q r"l':C ring",
       ← q r"poly_extend(k:A ring,l:B ring) (f:A->B) (\v:1. a:B)",
       ← q r"poly_extend(k:A ring,l':C ring) (g:A->C) (\v:1. a':C)"]
      RING_HOMOMORPHISM_EPIMORPHISM_FACTOR) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"h:B->C") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"h:B->C") THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o
      SPEC (← q r"(poly_const (k:A ring) (x:A)):(1->num)->A")) THEN
    ASM_REWRITE_TAC [POLY_CONST] THEN ASM_SIMP_TAC [POLY_EXTEND_CONST])

  -- @@RETURN BEGIN
  return { SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM }
  -- @@RETURN END

structure ClosureExtendHom where
  -- @@FIELDS
  ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM : thm
  deriving Inhabited

@[nospecialize]
def setupClosureExtendHom [HolBase] (D : FieldTheoryDeps) (BSubfields : Subfields) (BSubfieldGenerated2 : SubfieldGenerated2) (BFieldExtension : FieldExtension) (BAlgebraicExtension : AlgebraicExtension) (BAlgebraicExtensionProps : AlgebraicExtensionProps) (BAcfBasic : AcfBasic) (BSimpleExtendHom : SimpleExtendHom) :
    ExceptT String IO ClosureExtendHom := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_TAC, .. } := D
  let { CARRIER_SUBRING_GENERATED_SUBRING, EXISTS_PAIR_THM, EXTENSION, .. } := D.core1
  let { FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING, FIELD_MUL_RINV,
        FIELD_NONTRIVIAL, FIELD_RING_HOMOMORPHISM_MONOMORPHISM, FORALL_IN_IMAGE,
        FORALL_PAIR_THM, FST, IMAGE_EQ_EMPTY, IMAGE_I, IMAGE_SUBSET, IMAGE_UNIONS, .. } := D.core2
  let { INSERT_SUBSET, IN_CROSS, IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_UNIONS, I_DEF, .. } := D.core3
  let { MEMBER_NOT_EMPTY, PAIR_EQ, .. } := D.core4
  let { RING_CARRIER_SUBRING_GENERATED_SUBSET, .. } := D.core5
  let { RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_ADD,
        RING_HOMOMORPHISM_EPIMORPHISM_FACTOR, RING_HOMOMORPHISM_EQ,
        RING_HOMOMORPHISM_INTO_SUBRING, RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_NEG,
        RING_KERNEL_0, RING_KERNEL_TO_SUBRING_GENERATED, RING_MONOMORPHISM,
        RING_MONOMORPHISM_INCLUSION, .. } := D.core6
  let { SELECT_UNIQUE, SING_SUBSET, SND, SUBRING_GENERATED,
        SUBRING_GENERATED_BY_SUBRING_GENERATED, .. } := D.core7
  let { SUBRING_GENERATED_INC_GEN, SUBRING_GENERATED_RING_CARRIER,
        SUBRING_GENERATED_SUBSET_CARRIER_SUBSET, SUBRING_OF_UNIONS,
        SUBRING_SUBRING_GENERATED, SUBSET, SUBSET_ANTISYM_EQ, SUBSET_REFL,
        SUBSET_TRANS, UNIONS_SUBSET, ZL_SUBSETS_UNIONS_NONEMPTY, field, .. } := D.core8
  let { ring_epimorphism, ring_homomorphism, ring_monomorphism, subring_of, .. } := D.core9
  let { CARRIER_SUBFIELD_OF, IN_SUBFIELD_INV, SUBFIELD_IMP_SUBRING_OF,
        SUBFIELD_OF_IMP_SUBSET, subfield_of, .. } := BSubfields
  let { SUBFIELD_OF_MONOMORPHIC_IMAGE, .. } := BSubfieldGenerated2
  let { field_extension, .. } := BFieldExtension
  let { ALGEBRAIC_OVER_SUBRING_GENERATED_MONO, algebraic_extension, .. } := BAlgebraicExtension
  let { ALGEBRAIC_OVER_RANGE, FIELD_SIMPLE_ALGEBRAIC_EXTENSION_GEN, .. } := BAlgebraicExtensionProps
  let { ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD, .. } := BAcfBasic
  let { SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM, .. } := BSimpleExtendHom
  -- @@SCOPE END

  let ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM ← prove
   r"!(k:A ring) (l:B ring) (l':C ring) (f:A->B) (g:A->C).
        algebraic_extension(k,l) f /\ algebraically_closed_field l' /\
        ring_homomorphism(k,l') g
        ==> ?h. ring_homomorphism(l,l') h /\
                (!x. x IN ring_carrier k ==> h(f x) = g x)"
   (← do
    let SUBRING_OF_G0_FROM_CH_P : tactic := tactic_of do pure (
     MATCH_MP_TAC SUBFIELD_IMP_SUBRING_OF THEN USE_THEN "CH_P" (fun ch_p =>
       FIRST_ASSUM (fun th => tactic_of do pure (ACCEPT_TAC (← CONJUNCT1 (← CONJUNCT2 (←
         CONJUNCT2 (← REWRITE_RULE [] (←
         MATCH_MP (← SPEC (← q r"G0:(B#C)->bool") ch_p) th)))))))))
    let HOM_CONST_TAC (thm : thm) :=
     USE_THEN "HOM_U" (fun hom_u => USE_THEN "GW" (fun gw => tactic_of do
         pure (MP_TAC (← REWRITE_RULE [← CONJUNCT2 SUBRING_GENERATED]
           (← MATCH_MP thm (← MATCH_MP hom_u gw)))))) THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN REWRITE_TAC []
    let G0_X0_IN_CC_TAC : tactic := tactic_of do pure (
     SUBGOAL_THEN (← q r"?G0:(B#C)->bool. G0 IN cc /\ x0:B IN IMAGE FST G0")
       STRIP_ASSUME_TAC THENL
      [ASM_MESON_TAC [IN_IMAGE, IN_UNIONS], ALL_TAC] THEN
     SUBGOAL_THEN (← q r"IMAGE FST (G0:(B#C)->bool) subring_of (l:B ring)")
       ASSUME_TAC THENL [SUBRING_OF_G0_FROM_CH_P, ALL_TAC] THEN
     SUBGOAL_THEN
       (← q r"x0:B IN ring_carrier
         (subring_generated (l:B ring) (IMAGE FST (G0:(B#C)->bool)))")
       ASSUME_TAC THENL
      [ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING], ALL_TAC])
    let chain_binop_tac (ring_hom_op : thm) : tactic := tactic_of do pure (
      MAP_EVERY X_GEN_TAC [← q r"x0:B", ← q r"y0:B"] THEN STRIP_TAC THEN SUBGOAL_THEN
        (← q r"?G0:(B#C)->bool. G0 IN cc /\
           x0:B IN IMAGE FST G0 /\ y0:B IN IMAGE FST G0")
        STRIP_ASSUME_TAC THENL [SUBGOAL_THEN
          (← q r"(?G1:(B#C)->bool. G1 IN cc /\ x0:B IN IMAGE FST G1) /\
           (?G2:(B#C)->bool. G2 IN cc /\ y0:B IN IMAGE FST G2)")
          (CONJUNCTS_THEN2 STRIP_ASSUME_TAC STRIP_ASSUME_TAC) THENL
         [CONJ_TAC THEN ASM_MESON_TAC [IN_IMAGE, IN_UNIONS], ALL_TAC] THEN
        USE_THEN "CH_ORD" (fun ch_ord => tactic_of do pure (DISJ_CASES_TAC (←MATCH_MP
            (← SPECL [← q r"G1:(B#C)->bool", ← q r"G2:(B#C)->bool"] ch_ord)
            (← CONJ (← ASSUME (← q r"G1:(B#C)->bool IN cc"))
                  (← ASSUME (← q r"G2:(B#C)->bool IN cc")))))) THENL
         [EXISTS_TAC (← q r"G2:(B#C)->bool") THEN ASM_REWRITE_TAC [] THEN
           ASM_MESON_TAC [SUBSET, IN_IMAGE],
          EXISTS_TAC (← q r"G1:(B#C)->bool") THEN ASM_REWRITE_TAC [] THEN
            ASM_MESON_TAC [SUBSET, IN_IMAGE]],
        ALL_TAC] THEN SUBGOAL_THEN
        (← q r"IMAGE FST (G0:(B#C)->bool) subring_of (l:B ring)")
        ASSUME_TAC THENL [SUBRING_OF_G0_FROM_CH_P, ALL_TAC] THEN
      SUBGOAL_THEN (← q r"x0:B IN ring_carrier (subring_generated (l:B ring)
            (IMAGE FST (G0:(B#C)->bool))) /\
         y0:B IN ring_carrier (subring_generated (l:B ring)
            (IMAGE FST (G0:(B#C)->bool)))")
        ASSUME_TAC THENL [ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING],
          ALL_TAC] THEN
      USE_THEN "HOM_U" (fun hom_u =>
        FIRST_ASSUM (fun gin => FIRST_ASSUM (fun xyin => tactic_of do
            pure (MP_TAC (← CONV_RULE (DEPTH_CONV BETA_CONV)
              (← REWRITE_RULE [← CONJUNCT2 SUBRING_GENERATED]
                (← MATCH_MP (← SPECL [← q r"x0:B", ← q r"y0:B"]
                    (← MATCH_MP ring_hom_op (← MATCH_MP hom_u gin)))
                  xyin))))))) THEN REWRITE_TAC [])
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"field (k:A ring) /\ field (l:B ring) /\ field (l':C ring) /\
       ring_monomorphism(k:A ring,l:B ring) f /\ integral_domain (l:B ring) /\
       ring_monomorphism(k:A ring,l':C ring) g /\
       ring_homomorphism(k:A ring,l:B ring) (f:A->B)") STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [algebraic_extension, field_extension,
       ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD, FIELD_IMP_INTEGRAL_DOMAIN,
       FIELD_RING_HOMOMORPHISM_MONOMORPHISM, FIELD_IMP_NONTRIVIAL_RING,
       ring_monomorphism], ALL_TAC] THEN
    -- Apply Zorn's lemma on graphs (subsets of B x C) encoding partial
    --   homomorphisms. P(G) says G is a functional relation whose domain is
    --   a subfield of l containing IMAGE f (carrier k), and the induced
    --   function is a ring homomorphism extending g.
    MP_TAC (← ISPEC (← q r"\G:(B#C)->bool.
         G SUBSET (ring_carrier l CROSS ring_carrier l') /\
         (!x:B y1:C y2:C. (x,y1) IN G /\ (x,y2) IN G ==> y1 = y2) /\
         (IMAGE FST G) subfield_of (l:B ring) /\
         IMAGE (f:A->B) (ring_carrier k) SUBSET IMAGE FST G /\ ring_homomorphism
           (subring_generated l (IMAGE FST G), l':C ring)
           (\x:B. @y:C. (x,y) IN G) /\ (!x:A. x IN ring_carrier k
                ==> (@y:C. ((f:A->B) x,y) IN G) = g x)")
      ZL_SUBSETS_UNIONS_NONEMPTY) THEN ANTS_TAC THENL [CONJ_TAC THENL
       [-- Existence: the graph {(f x, g x) | x in carrier k} works
        ABBREV_TAC
          (← q r"G0 = {((f:A->B) x, (g:A->C) x) | x IN ring_carrier k}") THEN
        EXISTS_TAC (← q r"G0:(B#C)->bool") THEN
        SUBGOAL_THEN (← q r"!a1 a2:A. a1 IN ring_carrier k /\ a2 IN ring_carrier k /\
                     (f:A->B) a1 = f a2 ==> a1 = a2")
          (LABEL_TAC "INJ") THENL [ASM_MESON_TAC [ring_monomorphism],
            ALL_TAC] THEN
        SUBGOAL_THEN (← q r"!a:A. a IN ring_carrier k
                 ==> (@y:C. ((f:A->B) a, y) IN G0) = (g:A->C) a")
          (LABEL_TAC "SELECT") THENL [X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN
          MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC (← q r"c:C") THEN
          EXPAND_TAC "G0" THEN REWRITE_TAC [IN_ELIM_THM, PAIR_EQ] THEN
          ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN
          (← q r"IMAGE FST (G0:(B#C)->bool) = IMAGE (f:A->B) (ring_carrier k)")
          ASSUME_TAC THENL [EXPAND_TAC "G0" THEN
          REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM,
                      EXISTS_PAIR_THM, PAIR_EQ, FST] THEN
          MESON_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
         [-- G0 SUBSET carrier l CROSS carrier l'
          EXPAND_TAC "G0" THEN REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_CROSS] THEN
          X_GEN_TAC (← q r"p:B#C") THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"a0:A") STRIP_ASSUME_TAC) THEN
          ASM_REWRITE_TAC [FST, SND, IN_CROSS] THEN CONJ_TAC THEN
          FIRST_ASSUM (fun th => tactic_of do pure (MATCH_MP_TAC (← REWRITE_RULE [SUBSET, FORALL_IN_IMAGE] (←
            CONJUNCT1 (← GEN_REWRITE_RULE I [ring_homomorphism] th))))) THEN
          ASM_REWRITE_TAC [], EXPAND_TAC "G0" THEN
          REWRITE_TAC [IN_ELIM_THM, PAIR_EQ] THEN ASM_MESON_TAC [],
          MATCH_MP_TAC SUBFIELD_OF_MONOMORPHIC_IMAGE THEN
          EXISTS_TAC (← q r"k:A ring") THEN ASM_SIMP_TAC [CARRIER_SUBFIELD_OF],
            SET_TAC [],
          MP_TAC (← ISPECL [← q r"k:A ring", ← q r"subring_generated (l:B ring)
                (IMAGE (f:A->B) (ring_carrier k))", ← q r"l':C ring",
             ← q r"f:A->B", ← q r"g:A->C"]
            RING_HOMOMORPHISM_EPIMORPHISM_FACTOR) THEN ANTS_TAC THENL
           [REPEAT CONJ_TAC THENL
             [-- ring_epimorphism(k, subring_generated l (IMAGE f carrier_k)) f
              REWRITE_TAC [ring_epimorphism] THEN CONJ_TAC THENL
               [MATCH_MP_TAC RING_HOMOMORPHISM_INTO_SUBRING THEN
                ASM_REWRITE_TAC [SUBSET_REFL],
                SUBGOAL_THEN (← q r"(IMAGE (f:A->B) (ring_carrier k)) subring_of l")
                  (fun th => SIMP_TAC [th,
                    CARRIER_SUBRING_GENERATED_SUBRING]) THEN
                MATCH_MP_TAC SUBFIELD_IMP_SUBRING_OF THEN
                MATCH_MP_TAC SUBFIELD_OF_MONOMORPHIC_IMAGE THEN
                EXISTS_TAC (← q r"k:A ring") THEN ASM_SIMP_TAC [CARRIER_SUBFIELD_OF]],
              -- ring_homomorphism(k, l') g
              ASM_REWRITE_TAC [],
              REWRITE_TAC [RING_KERNEL_TO_SUBRING_GENERATED] THEN SUBGOAL_THEN
                (← q r"ring_kernel(k:A ring,l:B ring) f = {ring_0 k}")
                SUBST1_TAC THENL [ASM_MESON_TAC [RING_MONOMORPHISM], ALL_TAC] THEN
              REWRITE_TAC [SING_SUBSET] THEN MATCH_MP_TAC RING_KERNEL_0 THEN
                ASM_REWRITE_TAC []],
            ALL_TAC] THEN -- Continuation: transfer from h' to the @-function
          DISCH_THEN (X_CHOOSE_THEN (← q r"h':B->C") STRIP_ASSUME_TAC) THEN
          MATCH_MP_TAC RING_HOMOMORPHISM_EQ THEN
          EXISTS_TAC (← q r"h':B->C") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN
            (← q r"(IMAGE (f:A->B) (ring_carrier k)) subring_of l") ASSUME_TAC THENL
           [MATCH_MP_TAC SUBFIELD_IMP_SUBRING_OF THEN MATCH_MP_TAC
              SUBFIELD_OF_MONOMORPHIC_IMAGE THEN
            EXISTS_TAC (← q r"k:A ring") THEN ASM_SIMP_TAC [CARRIER_SUBFIELD_OF],
              ALL_TAC] THEN
          ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING] THEN
          REWRITE_TAC [FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN
          SUBGOAL_THEN (← q r"(@y:C. ((f:A->B) a,y) IN G0) = (g:A->C) a")
            SUBST1_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN ASM_MESON_TAC []],
        X_GEN_TAC (← q r"cc:((B#C)->bool)->bool") THEN BETA_TAC THEN
        DISCH_THEN (CONJUNCTS_THEN2
          (X_CHOOSE_THEN (← q r"G_w:(B#C)->bool") (LABEL_TAC "GW"))
          (CONJUNCTS_THEN2 (LABEL_TAC "CH_P") (LABEL_TAC "CH_ORD"))) THEN
        SUBGOAL_THEN (← q r"!G:(B#C)->bool. G IN cc ==>
             !x:B y1:C y2:C. (x,y1) IN G /\ (x,y2) IN G ==> y1 = y2")
          ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"!x:B y1:C y2:C.
             (x,y1) IN UNIONS cc /\ (x,y2) IN UNIONS cc ==> y1 = y2")
          (LABEL_TAC "UFUNC") THENL
         [REWRITE_TAC [IN_UNIONS] THEN ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"!G:(B#C)->bool. G IN cc ==> !x:B. x IN IMAGE FST G ==>
               (@y:C. (x,y) IN UNIONS cc) = (@y. (x,y) IN G)")
          (LABEL_TAC "SELECT_UNION") THENL
         [X_GEN_TAC (← q r"G0:(B#C)->bool") THEN DISCH_TAC THEN
          X_GEN_TAC (← q r"x0:B") THEN DISCH_TAC THEN SUBGOAL_THEN
            (← q r"!y0:C. (x0:B,y0) IN UNIONS cc <=>
                    (x0,y0) IN (G0:(B#C)->bool)") (fun th => REWRITE_TAC [th]) THEN
          X_GEN_TAC (← q r"y0:C") THEN EQ_TAC THENL [DISCH_TAC THEN
            SUBGOAL_THEN (← q r"?y':C. (x0:B,y') IN (G0:(B#C)->bool)")
              STRIP_ASSUME_TAC THENL
             [MP_TAC (← ASSUME (← q r"x0:B IN IMAGE FST (G0:(B#C)->bool)")) THEN
              REWRITE_TAC [IN_IMAGE, EXISTS_PAIR_THM, FST, PAIR_EQ] THEN
              MESON_TAC [], ALL_TAC] THEN ASM_MESON_TAC [IN_UNIONS],
            ASM_MESON_TAC [IN_UNIONS]], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"IMAGE FST (UNIONS cc:(B#C)->bool) subring_of (l:B ring)")
          (LABEL_TAC "SR") THENL [REWRITE_TAC [IMAGE_UNIONS] THEN
          MATCH_MP_TAC SUBRING_OF_UNIONS THEN REPEAT CONJ_TAC THENL
           [REWRITE_TAC [IMAGE_EQ_EMPTY] THEN
            REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN USE_THEN "GW" (fun gw =>
              tactic_of do pure (EXISTS_TAC (← q r"G_w:(B#C)->bool") THEN ACCEPT_TAC gw)),
            REWRITE_TAC [FORALL_IN_IMAGE] THEN
            X_GEN_TAC (← q r"G0:(B#C)->bool") THEN DISCH_TAC THEN
            SUBRING_OF_G0_FROM_CH_P, REWRITE_TAC [IN_IMAGE] THEN
            MAP_EVERY X_GEN_TAC [← q r"s1:B->bool", ← q r"s2:B->bool"] THEN
            DISCH_THEN (CONJUNCTS_THEN2
              (X_CHOOSE_THEN (← q r"G1:(B#C)->bool") STRIP_ASSUME_TAC)
              (X_CHOOSE_THEN (← q r"G2:(B#C)->bool") STRIP_ASSUME_TAC)) THEN
            FIRST_X_ASSUM SUBST1_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
            USE_THEN "CH_ORD" (fun ch_ord => tactic_of do pure (DISJ_CASES_TAC (← MATCH_MP
                (← SPECL [← q r"G1:(B#C)->bool", ← q r"G2:(B#C)->bool"] ch_ord)
                (← CONJ (← ASSUME (← q r"(G1:(B#C)->bool) IN cc"))
                      (← ASSUME (← q r"(G2:(B#C)->bool) IN cc")))))) THENL
             [DISJ1_TAC, DISJ2_TAC] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
               ASM_REWRITE_TAC []],
          ALL_TAC] THEN REPEAT CONJ_TAC THENL
         [-- 1. UNIONS cc SUBSET carrier l CROSS carrier l'
          REWRITE_TAC [UNIONS_SUBSET] THEN ASM_MESON_TAC [],
          -- 2. Functional
          USE_THEN "UFUNC" ACCEPT_TAC, -- 3. subfield_of
          REWRITE_TAC [subfield_of] THEN CONJ_TAC THENL [USE_THEN "SR" ACCEPT_TAC,
            ASM_SIMP_TAC [field, ← CONJUNCT2 SUBRING_GENERATED,
                          CARRIER_SUBRING_GENERATED_SUBRING] THEN
            CONJ_TAC THENL [ASM_MESON_TAC [FIELD_NONTRIVIAL], ALL_TAC] THEN
            X_GEN_TAC (← q r"x0:B") THEN STRIP_TAC THEN
            SUBGOAL_THEN (← q r"?G0. (G0:(B#C)->bool) IN cc /\ (x0:B) IN IMAGE FST G0")
              STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [IN_IMAGE, IN_UNIONS],
              ALL_TAC] THEN
            SUBGOAL_THEN (← q r"IMAGE FST (G0:(B#C)->bool) subfield_of (l:B ring)")
              ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN
              (← q r"ring_inv (l:B ring) (x0:B) IN IMAGE FST (G0:(B#C)->bool)")
              ASSUME_TAC THENL [MATCH_MP_TAC IN_SUBFIELD_INV THEN
                ASM_REWRITE_TAC [], ALL_TAC] THEN
            SUBGOAL_THEN (← q r"(x0:B) IN ring_carrier (l:B ring)")
              ASSUME_TAC THENL [ASM_MESON_TAC [subring_of, SUBSET], ALL_TAC] THEN
            EXISTS_TAC (← q r"ring_inv (l:B ring) (x0:B)") THEN CONJ_TAC THENL
             [ASM_MESON_TAC [IN_IMAGE, IN_UNIONS], ASM_SIMP_TAC [FIELD_MUL_RINV]]],
          USE_THEN "CH_P" (fun ch_p => USE_THEN "GW" (fun gw => tactic_of do
              pure (STRIP_ASSUME_TAC (← MATCH_MP (← SPEC (← q r"G_w:(B#C)->bool") ch_p) gw)))) THEN
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC (← q r"IMAGE FST (G_w:(B#C)->bool)") THEN ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC [SUBSET, IN_UNIONS] THEN
          USE_THEN "GW" (fun th => MESON_TAC [th]),
          -- 5. ring_homomorphism (per-G and for UNIONS)
          SUBGOAL_THEN (← q r"!G. G IN cc ==> ring_homomorphism
                   (subring_generated (l:B ring) (IMAGE FST G), l':C ring)
                   (\x:B. @y:C. (x,y) IN UNIONS cc)") (LABEL_TAC "HOM_U") THENL
           [X_GEN_TAC (← q r"G0:(B#C)->bool") THEN DISCH_TAC THEN SUBGOAL_THEN
              (← q r"IMAGE FST (G0:(B#C)->bool) subring_of (l:B ring)")
              ASSUME_TAC THENL [SUBRING_OF_G0_FROM_CH_P, ALL_TAC] THEN
            MATCH_MP_TAC RING_HOMOMORPHISM_EQ THEN
            EXISTS_TAC (← q r"\x:B. @y:C. (x,y) IN (G0:(B#C)->bool)") THEN
              CONJ_TAC THENL
             [ASM_MESON_TAC [],
              ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING] THEN
              X_GEN_TAC (← q r"x0:B") THEN DISCH_TAC THEN
              CONV_TAC (DEPTH_CONV BETA_CONV) THEN
              USE_THEN "SELECT_UNION" (fun su =>
                FIRST_ASSUM (fun gin => tactic_of do pure (MP_TAC (← SPEC (← q r"x0:B")
                    (← MATCH_MP (← SPEC (← q r"G0:(B#C)->bool") su) gin))))) THEN
              ASM_REWRITE_TAC []], ALL_TAC] THEN
          REWRITE_TAC [ring_homomorphism, ← CONJUNCT2 SUBRING_GENERATED] THEN
          USE_THEN "SR" (fun sr => tactic_of do
            pure (REWRITE_TAC [← MATCH_MP CARRIER_SUBRING_GENERATED_SUBRING sr])) THEN
          CONJ_TAC THENL
           [-- 5a. IMAGE subset
            REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"c0:C") THEN
            GEN_REWRITE_TAC LAND_CONV [IN_IMAGE] THEN
            DISCH_THEN (X_CHOOSE_THEN (← q r"x0:B")
              (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
            CONV_TAC (DEPTH_CONV BETA_CONV) THEN G0_X0_IN_CC_TAC THEN
            USE_THEN "HOM_U" (fun hom_u =>
              FIRST_ASSUM (fun gin => FIRST_ASSUM (fun xin => tactic_of do
                  pure (MP_TAC (← CONV_RULE (DEPTH_CONV BETA_CONV)
                    (← MP (← SPEC (← q r"x0:B") (← CONJUNCT1 (← REWRITE_RULE
                        [ring_homomorphism, SUBSET, FORALL_IN_IMAGE]
                        (← MATCH_MP hom_u gin))))
                    xin)))))) THEN SIMP_TAC [], ALL_TAC] THEN
          CONJ_TAC THENL [HOM_CONST_TAC RING_HOMOMORPHISM_0, ALL_TAC] THEN
          CONJ_TAC THENL [HOM_CONST_TAC RING_HOMOMORPHISM_1, ALL_TAC] THEN
          CONJ_TAC THENL [-- 5d: ring_neg
            X_GEN_TAC (← q r"x0:B") THEN DISCH_TAC THEN G0_X0_IN_CC_TAC THEN
            USE_THEN "HOM_U" (fun hom_u =>
              FIRST_ASSUM (fun gin => FIRST_ASSUM (fun xin => tactic_of do
                  pure (MP_TAC (← CONV_RULE (DEPTH_CONV BETA_CONV)
                    (← REWRITE_RULE [← CONJUNCT2 SUBRING_GENERATED]
                      (← MATCH_MP (← SPEC (← q r"x0:B") (← MATCH_MP RING_HOMOMORPHISM_NEG
                            (← MATCH_MP hom_u gin)))
                        xin))))))) THEN REWRITE_TAC [], ALL_TAC] THEN
          (CONJ_TAC THENL [chain_binop_tac RING_HOMOMORPHISM_ADD, ALL_TAC] THEN
          chain_binop_tac RING_HOMOMORPHISM_MUL), -- 6. extends g
          X_GEN_TAC (← q r"a0:A") THEN DISCH_TAC THEN USE_THEN "CH_P" (fun ch_p =>
            USE_THEN "GW" (fun gw => tactic_of do pure (STRIP_ASSUME_TAC (← MATCH_MP
                (← SPEC (← q r"G_w:(B#C)->bool") ch_p) gw)))) THEN
          SUBGOAL_THEN (← q r"(f:A->B) a0 IN IMAGE FST (G_w:(B#C)->bool)")
            ASSUME_TAC THENL [FIRST_X_ASSUM (fun th => tactic_of do pure (MATCH_MP_TAC (←
              REWRITE_RULE [SUBSET, FORALL_IN_IMAGE] th))) THEN
            ASM_REWRITE_TAC [], ALL_TAC] THEN USE_THEN "SELECT_UNION" (fun su =>
            USE_THEN "GW" (fun gw => tactic_of do pure (MP_TAC (← SPEC (← q r"(f:A->B) a0")
                (← MATCH_MP (← SPEC (← q r"G_w:(B#C)->bool") su) gw))))) THEN
          ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
          ASM_MESON_TAC []]], -- end chain closure
      DISCH_THEN (X_CHOOSE_THEN (← q r"G:(B#C)->bool") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"IMAGE FST (G:(B#C)->bool) = ring_carrier (l:B ring)")
        ASSUME_TAC THENL [-- Proof: IMAGE FST G = ring_carrier l
        REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THENL
         [-- Easy: IMAGE FST G SUBSET ring_carrier l
          ASM_MESON_TAC [SUBFIELD_OF_IMP_SUBSET], ALL_TAC] THEN
        REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"a:B") THEN DISCH_TAC THEN
        ASM_CASES_TAC (← q r"(a:B) IN IMAGE FST (G:(B#C)->bool)") THENL
         [ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN
          (← q r"field(subring_generated (l:B ring) (IMAGE FST (G:(B#C)->bool))) /\
           IMAGE FST (G:(B#C)->bool) subring_of (l:B ring) /\
           ring_monomorphism (subring_generated (l:B ring)
                (IMAGE FST (G:(B#C)->bool)), l) I") STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THENL
           [ASM_MESON_TAC [subfield_of], ASM_MESON_TAC [SUBFIELD_IMP_SUBRING_OF],
            REWRITE_TAC [I_DEF, RING_MONOMORPHISM_INCLUSION]], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"ring_carrier(subring_generated (l:B ring)
            (IMAGE FST (G:(B#C)->bool))) = IMAGE FST G") ASSUME_TAC THENL
         [ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"algebraic_over (subring_generated (l:B ring)
              (IMAGE FST (G:(B#C)->bool)), l) I (a:B)") ASSUME_TAC THENL
         [MATCH_MP_TAC ALGEBRAIC_OVER_SUBRING_GENERATED_MONO THEN
          EXISTS_TAC (← q r"IMAGE (f:A->B) (ring_carrier k)") THEN CONJ_TAC THENL
           [MP_TAC (← ISPECL [← q r"f:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"a:B"]
              ALGEBRAIC_OVER_RANGE) THEN ASM_REWRITE_TAC [] THEN
            DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← GSYM th])) THEN
            ASM_MESON_TAC [algebraic_extension], ASM_MESON_TAC []], ALL_TAC] THEN
        -- Monomorphism of h_G
        SUBGOAL_THEN (← q r"ring_monomorphism
            (subring_generated (l:B ring) (IMAGE FST (G:(B#C)->bool)), l':C ring)
            (\x:B. @y:C. (x,y) IN G)") ASSUME_TAC THENL
         [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
           ASM_REWRITE_TAC [] THEN
          ASM_MESON_TAC [FIELD_IMP_NONTRIVIAL_RING], ALL_TAC] THEN MP_TAC (← ISPECL
          [← q r"subring_generated (l:B ring) (IMAGE FST (G:(B#C)->bool))",
           ← q r"l:B ring", ← q r"l':C ring", ← q r"I:B->B",
           ← q r"(\x:B. @y:C. (x,y) IN (G:(B#C)->bool)):B->C", ← q r"a:B"]
          SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM) THEN ANTS_TAC THENL
         [ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [IMAGE_I, I_DEF] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"h':B->C") STRIP_ASSUME_TAC) THEN
        ABBREV_TAC (← q r"S' = ring_carrier(subring_generated (l:B ring)
          ((a:B) INSERT IMAGE FST (G:(B#C)->bool)))") THEN
        SUBGOAL_THEN (← q r"field(subring_generated (l:B ring)
            ((a:B) INSERT IMAGE FST (G:(B#C)->bool)))") ASSUME_TAC THENL
         [MP_TAC (← ISPECL [← q r"I:B->B",
             ← q r"subring_generated (l:B ring) (IMAGE FST (G:(B#C)->bool))",
             ← q r"l:B ring", ← q r"a:B"] FIELD_SIMPLE_ALGEBRAIC_EXTENSION_GEN) THEN
          ASM_REWRITE_TAC [IMAGE_I] THEN DISCH_THEN MATCH_MP_TAC THEN
          ASM_MESON_TAC [ring_monomorphism], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"(S':B->bool) subfield_of (l:B ring) /\
          (a:B) IN (S':B->bool)") STRIP_ASSUME_TAC THENL
         [EXPAND_TAC "S'" THEN CONJ_TAC THENL
           [ASM_REWRITE_TAC [subfield_of, SUBRING_SUBRING_GENERATED,
                            SUBRING_GENERATED_BY_SUBRING_GENERATED],
            MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
            ASM_REWRITE_TAC [IN_INSERT]], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"IMAGE FST (G:(B#C)->bool) SUBSET (S':B->bool) /\
           (S':B->bool) SUBSET ring_carrier (l:B ring)") STRIP_ASSUME_TAC THENL
         [EXPAND_TAC "S'" THEN CONJ_TAC THENL [MATCH_MP_TAC SUBSET_TRANS THEN
            EXISTS_TAC (← q r"(a:B) INSERT IMAGE FST (G:(B#C)->bool)") THEN
            CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
            MATCH_MP_TAC SUBRING_GENERATED_SUBSET_CARRIER_SUBSET THEN
            REWRITE_TAC [INSERT_SUBSET] THEN
            ASM_MESON_TAC [SUBFIELD_OF_IMP_SUBSET, SUBSET],
            REWRITE_TAC [RING_CARRIER_SUBRING_GENERATED_SUBSET]], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"(!x:B y1:C y2:C.
             (x,y1) IN (G:(B#C)->bool) /\ (x,y2) IN G ==> y1 = y2) /\
           (!x:A. x IN ring_carrier k
                 ==> (@y:C. ((f:A->B) x,y) IN (G:(B#C)->bool)) =
                     (g:A->C) x)") STRIP_ASSUME_TAC THENL
         [CONJ_TAC THEN ASM_MESON_TAC [], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"IMAGE FST (IMAGE (\x:B. (x, (h':B->C) x)) (S':B->bool))
           = (S':B->bool)") ASSUME_TAC THENL
         [REWRITE_TAC [EXTENSION, IN_IMAGE, EXISTS_PAIR_THM, FST, PAIR_EQ] THEN
          MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!b:B. b IN S'
                 ==> (@c:C. (b,c) IN IMAGE (\x:B. (x, (h':B->C) x))
                                            (S':B->bool)) = h' b") ASSUME_TAC
                                              THENL
         [REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
          X_GEN_TAC (← q r"c':C") THEN
          REWRITE_TAC [IN_IMAGE, PAIR_EQ] THEN ASM_MESON_TAC [], ALL_TAC] THEN
        -- Apply maximality: G = IMAGE (\x. (x, h' x)) S'
        SUBGOAL_THEN
          (← q r"(G:(B#C)->bool) = IMAGE (\x:B. (x, (h':B->C) x)) (S':B->bool)")
          ASSUME_TAC THENL [FIRST_X_ASSUM (MP_TAC o SPEC
            (← q r"IMAGE (\x:B. (x, (h':B->C) x)) (S':B->bool)")) THEN
              REWRITE_TAC [] THEN
          ANTS_TAC THENL [CONJ_TAC THENL [-- P(G') - 6 conditions
              ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
               [-- 1
                REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_CROSS] THEN
                X_GEN_TAC (← q r"b':B") THEN DISCH_TAC THEN CONJ_TAC THENL
                 [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN EXPAND_TAC "S'" THEN
                ASM_MESON_TAC [ring_homomorphism, SUBSET, IN_IMAGE],
                -- 2
                REWRITE_TAC [IN_IMAGE, PAIR_EQ] THEN MESON_TAC [],
                -- 4
                ASM_MESON_TAC [SUBSET_TRANS], -- 5: ring_homomorphism
                SUBGOAL_THEN (← q r"subring_generated (l:B ring) (S':B->bool) =
                   subring_generated l
                     ((a:B) INSERT IMAGE FST (G:(B#C)->bool))") SUBST1_TAC THENL
                 [UNDISCH_TAC (← q r"ring_carrier (subring_generated (l:B ring)
                      ((a:B) INSERT IMAGE FST (G:(B#C)->bool))) = S'") THEN
                  DISCH_THEN (fun th => tactic_of do pure (SUBST1_TAC (← SYM th))) THEN
                  REWRITE_TAC [SUBRING_GENERATED_BY_SUBRING_GENERATED],
                    ALL_TAC] THEN
                MATCH_MP_TAC RING_HOMOMORPHISM_EQ THEN EXISTS_TAC (← q r"h':B->C") THEN
                CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
                ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
                CONV_TAC BETA_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
                ASM_REWRITE_TAC [], X_GEN_TAC (← q r"x0:A") THEN DISCH_TAC THEN
                SUBGOAL_THEN (← q r"(f:A->B) x0 IN (S':B->bool) /\
                  (f:A->B) x0 IN IMAGE FST (G:(B#C)->bool)") STRIP_ASSUME_TAC
                    THENL
                 [CONJ_TAC THEN ASM_MESON_TAC [SUBSET, IN_IMAGE], ALL_TAC] THEN
                SUBGOAL_THEN (← q r"(@y:C. ((f:A->B) x0,y) IN
                    IMAGE (\x:B. (x,(h':B->C) x)) (S':B->bool)) =
                   (h':B->C) ((f:A->B) x0)") SUBST1_TAC THENL [ASM_MESON_TAC [],
                     ALL_TAC] THEN
                ASM_MESON_TAC []], -- G SUBSET G'
              REWRITE_TAC [SUBSET, FORALL_PAIR_THM, IN_IMAGE, PAIR_EQ] THEN
              MAP_EVERY X_GEN_TAC [← q r"x0:B", ← q r"y0:C"] THEN DISCH_TAC THEN
              SUBGOAL_THEN (← q r"(x0:B) IN (S':B->bool)") ASSUME_TAC THENL
               [ASM_MESON_TAC [SUBSET, IN_IMAGE, FST], ALL_TAC] THEN
              EXISTS_TAC (← q r"x0:B") THEN ASM_REWRITE_TAC [] THEN
              SUBGOAL_THEN (← q r"(h':B->C) x0 =
                (@y:C. (x0,y) IN (G:(B#C)->bool))") SUBST1_TAC THENL
               [ASM_MESON_TAC [IN_IMAGE, FST], ALL_TAC] THEN
              CONV_TAC SYM_CONV THEN MATCH_MP_TAC SELECT_UNIQUE THEN
              X_GEN_TAC (← q r"z:C") THEN ASM_MESON_TAC []],
            DISCH_THEN ACCEPT_TAC], ALL_TAC] THEN ASM_MESON_TAC [], ALL_TAC] THEN
      EXISTS_TAC (← q r"\x:B. @y:C. (x,y) IN (G:(B#C)->bool)") THEN
      ASM_MESON_TAC [SUBRING_GENERATED_RING_CARRIER]]))

  -- @@RETURN BEGIN
  return { ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM }
  -- @@RETURN END

structure PolySquarefree where
  -- @@FIELDS
  POLY_SQUAREFREE_ROOT_COUNT_EXPLICIT : thm
  POLY_SQUAREFREE_ROOT_COUNT : thm
  POLY_SQUAREFREE_ROOT_COUNT_EQ : thm
  POLY_SQUAREFREE_EXPLICIT_EQ : thm
  deriving Inhabited

@[nospecialize]
def setupPolySquarefree [HolBase] (D : FieldTheoryDeps) (BAcfBasic : AcfBasic) (BAcfSplit : AcfSplit) :
    ExceptT String IO PolySquarefree := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, SET_TAC, .. } := D
  let { ARITH_EQ, CARD_IMAGE_INJ, CARD_NUMSEG_1, EXTENSION, .. } := D.core1
  let { FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING, FINITE_DIFF,
        FINITE_INSERT, FINITE_NUMSEG, .. } := D.core2
  let { IMP_CONJ_ALT, INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_DOMAIN_PRODUCT_EQ_0, IN_DIFF,
        IN_ELIM_THM, IN_INSERT, IN_NUMSEG, LEFT_IMP_EXISTS_THM, .. } := D.core3
  let { NOT_IMP, NOT_IN_EMPTY, POLY_CLAUSES, POLY_CONST, POLY_DEG_UNIT,
        POLY_DEG_X_MINUS_A, POLY_EVAL_CONST, POLY_EVAL_MUL, .. } := D.core4
  let { POLY_EVAL_RING_PRODUCT, POLY_EVAL_SUB, POLY_EVAL_VAR, POLY_RING,
        POLY_RING_CLAUSES, POLY_ROOT_COUNT_IMP_SQUAREFREE, POLY_VAR_UNIV, .. } := D.core5
  let { RING_DIVIDES_LMUL, RING_DIVIDES_LMUL2, RING_DIVIDES_REFL, RING_DIVIDES_RMUL, .. } := D.core6
  let { RING_POLYNOMIAL, RING_POLYNOMIAL_CONST, RING_POLYNOMIAL_SUB,
        RING_POLYNOMIAL_VAR, RING_POW_2, RING_PRODUCT, RING_PRODUCT_CLAUSES,
        RING_SQUAREFREE_IMP_NONZERO, RING_SQUAREFREE_IN_CARRIER, RING_SUB,
        RING_SUB_EQ_0, .. } := D.core7
  let { TRIVIAL_POLY_RING, .. } := D.core8
  let { ring_squarefree, .. } := D.core9
  let { ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD, .. } := BAcfBasic
  let { ALGEBRAICALLY_CLOSED_FIELD_SPLITS, .. } := BAcfSplit
  -- @@SCOPE END

  let POLY_SQUAREFREE_ROOT_COUNT_EXPLICIT ← prove
   r"!(k:A ring) p.
      algebraically_closed_field k /\
      p IN ring_carrier(poly_ring k (:1)) /\
      ~(p = ring_0(poly_ring k (:1))) /\
      (!a. a IN ring_carrier k /\ poly_eval k p a = ring_0 k
           ==> ~(ring_divides (poly_ring k (:1))
                  (poly_pow k (poly_sub k (poly_var k one) (poly_const k a)) 2)
                  p))
      ==> CARD {x | x IN ring_carrier k /\ poly_eval k p x = ring_0 k} =
          poly_deg k p"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"p:(1->num)->A"]
              ALGEBRAICALLY_CLOSED_FIELD_SPLITS) THEN
    ASM_REWRITE_TAC [← GSYM IN_NUMSEG] THEN ANTS_TAC THENL
     [ASM_MESON_TAC [POLY_RING], REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [← q r"c:A", ← q r"a:num->A"] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (ASSUME_TAC o SYM) THEN
    ABBREV_TAC (← q r"n = poly_deg k (p:(1->num)->A)") THEN
    SUBGOAL_THEN
     (← q r"{x:A | x IN ring_carrier k /\ poly_eval k p x = ring_0 k} =
      IMAGE a (1..n)")
    ASSUME_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:A") THEN
      ASM_CASES_TAC (← q r"(x:A) IN ring_carrier k") THENL
       [ASM_REWRITE_TAC [], ASM SET_TAC []] THEN
      FIRST_X_ASSUM (MP_TAC o AP_TERM (← q r"\p:(1->num)->A. poly_eval k p x")) THEN
      REWRITE_TAC [] THEN
      wPart (fun c => do lhand (← lhand c)) (fun c => do lhand (← rand c)) POLY_EVAL_MUL THEN
      ASM_REWRITE_TAC [RING_POLYNOMIAL_CONST] THEN
      REWRITE_TAC [RING_POLYNOMIAL, RING_PRODUCT] THEN
      DISCH_THEN SUBST1_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      wPart (fun c => do rand (← lhand (← lhand c))) (fun c => do lhand (← rand c))
        POLY_EVAL_RING_PRODUCT THEN
      ASM_REWRITE_TAC [FINITE_NUMSEG, ← GSYM RING_POLYNOMIAL] THEN
      ASM_SIMP_TAC [POLY_EVAL_CONST, POLY_EVAL_SUB, POLY_EVAL_VAR,
                   POLY_EVAL_CONST, RING_POLYNOMIAL_CONST,
                   RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR] THEN
      DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0, RING_PRODUCT, FINITE_NUMSEG,
                   INTEGRAL_DOMAIN_PRODUCT_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN,
                   ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD] THEN
      ASM SET_TAC [RING_SUB_EQ_0],
      ASM_REWRITE_TAC []] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM CARD_NUMSEG_1] THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN REWRITE_TAC [FINITE_NUMSEG] THEN
    MAP_EVERY X_GEN_TAC [← q r"i:num", ← q r"j:num"] THEN
    ABBREV_TAC (← q r"b = (a:num->A) j") THEN STRIP_TAC THEN
    ASM_CASES_TAC (← q r"i:num = j") THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"(b:A) IN ring_carrier k") ASSUME_TAC THENL
     [ASM SET_TAC [], FIRST_X_ASSUM (MP_TAC o SPEC (← q r"b:A"))] THEN
    ANTS_TAC THENL [ASM SET_TAC [], EXPAND_TAC "p" THEN REWRITE_TAC []] THEN
    SUBGOAL_THEN (← q r"1..n = i INSERT j INSERT ((1..n) DIFF {i,j})") SUBST1_TAC THENL
     [ASM SET_TAC [], ALL_TAC] THEN
    ASM_SIMP_TAC [RING_PRODUCT_CLAUSES, FINITE_NUMSEG, FINITE_DIFF, FINITE_INSERT,
                 IN_INSERT, IN_DIFF, NOT_IN_EMPTY] THEN
    ASM_SIMP_TAC [POLY_CLAUSES, RING_SUB, POLY_CONST, POLY_VAR_UNIV,
                 RING_POW_2] THEN
    MATCH_MP_TAC RING_DIVIDES_LMUL THEN ASM_REWRITE_TAC [POLY_CONST] THEN
    MATCH_MP_TAC RING_DIVIDES_LMUL2 THEN
    ASM_SIMP_TAC [RING_SUB, POLY_CONST, POLY_VAR_UNIV] THEN
    MATCH_MP_TAC RING_DIVIDES_RMUL THEN
    REWRITE_TAC [RING_PRODUCT, RING_DIVIDES_REFL] THEN
    ASM_SIMP_TAC [RING_SUB, POLY_CONST, POLY_VAR_UNIV])

  let POLY_SQUAREFREE_ROOT_COUNT ← prove
   r"!(k:A ring) p.
      algebraically_closed_field k /\
      ring_squarefree (poly_ring k (:1)) p
      ==> CARD {x | x IN ring_carrier k /\ poly_eval k p x = ring_0 k} =
          poly_deg k p"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC POLY_SQUAREFREE_ROOT_COUNT_EXPLICIT THEN
    ASM_SIMP_TAC [RING_SQUAREFREE_IN_CARRIER, RING_SQUAREFREE_IMP_NONZERO,
                 FIELD_IMP_NONTRIVIAL_RING, ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD,
                 TRIVIAL_POLY_RING] THEN
    X_GEN_TAC (← q r"a:A") THEN STRIP_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM (CONJUNCTS_THEN2 ASSUME_TAC
        (MP_TAC o SPEC (← q r"poly_sub k (poly_var k one) (poly_const k (a:A))")) o
      REWRITE_RULE [ring_squarefree]) THEN
    ASM_REWRITE_TAC [← CONJUNCT2 POLY_RING_CLAUSES, NOT_IMP] THEN
    ASM_SIMP_TAC [POLY_CLAUSES, RING_SUB, POLY_CONST, POLY_VAR_UNIV] THEN
    DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT]
          POLY_DEG_UNIT)) THEN
    ASM_SIMP_TAC [ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD, FIELD_IMP_INTEGRAL_DOMAIN,
                 FIELD_IMP_NONTRIVIAL_RING, ARITH_EQ,
                ← CONJUNCT2 POLY_RING_CLAUSES, POLY_DEG_X_MINUS_A])

  let POLY_SQUAREFREE_ROOT_COUNT_EQ ← prove
   r"!(k:A ring) p.
      algebraically_closed_field k
      ==> (ring_squarefree (poly_ring k (:1)) p <=>
           p IN ring_carrier (poly_ring k (:1)) /\
           ~(p = ring_0 (poly_ring k (:1))) /\
           CARD {x | x IN ring_carrier k /\ poly_eval k p x = ring_0 k} =
           poly_deg k p)"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [ASM_SIMP_TAC [POLY_SQUAREFREE_ROOT_COUNT, RING_SQUAREFREE_IN_CARRIER,
                   RING_SQUAREFREE_IMP_NONZERO, FIELD_IMP_NONTRIVIAL_RING,
                   ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD, TRIVIAL_POLY_RING],
      ASM_SIMP_TAC [POLY_ROOT_COUNT_IMP_SQUAREFREE,
                   ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD]])

  let POLY_SQUAREFREE_EXPLICIT_EQ ← prove
   r"!(k:A ring) p.
      algebraically_closed_field k
      ==> (ring_squarefree (poly_ring k (:1)) p <=>
           p IN ring_carrier (poly_ring k (:1)) /\
           ~(p = ring_0 (poly_ring k (:1))) /\
           (!a. a IN ring_carrier k /\ poly_eval k p a = ring_0 k
                ==> ~(ring_divides (poly_ring k (:1))
                  (poly_pow k (poly_sub k (poly_var k one) (poly_const k a)) 2)
                  p)))"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN
      ASM_SIMP_TAC [RING_SQUAREFREE_IN_CARRIER, RING_SQUAREFREE_IMP_NONZERO,
                   FIELD_IMP_NONTRIVIAL_RING, TRIVIAL_POLY_RING,
                   ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD] THEN
      X_GEN_TAC (← q r"a:A") THEN STRIP_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM (CONJUNCTS_THEN2 ASSUME_TAC
          (MP_TAC o SPEC (← q r"poly_sub k (poly_var k one) (poly_const k (a:A))")) o
        REWRITE_RULE [ring_squarefree]) THEN
      ASM_REWRITE_TAC [← CONJUNCT2 POLY_RING_CLAUSES, NOT_IMP] THEN
      ASM_SIMP_TAC [POLY_CLAUSES, RING_SUB, POLY_CONST, POLY_VAR_UNIV] THEN
      DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT]
            POLY_DEG_UNIT)) THEN
      ASM_SIMP_TAC [ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD, POLY_DEG_X_MINUS_A,
                   FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING, ARITH_EQ,
                   ← CONJUNCT2 POLY_RING_CLAUSES],
      STRIP_TAC THEN MATCH_MP_TAC POLY_ROOT_COUNT_IMP_SQUAREFREE THEN
      ASM_SIMP_TAC [ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD] THEN
      MATCH_MP_TAC POLY_SQUAREFREE_ROOT_COUNT_EXPLICIT THEN ASM_REWRITE_TAC []])

  -- @@RETURN BEGIN
  return { POLY_SQUAREFREE_ROOT_COUNT_EXPLICIT, POLY_SQUAREFREE_ROOT_COUNT,
           POLY_SQUAREFREE_ROOT_COUNT_EQ, POLY_SQUAREFREE_EXPLICIT_EQ }
  -- @@RETURN END

structure AlgebraicClosureExistsId where
  -- @@FIELDS
  ALGEBRAIC_CLOSURE_EXISTS_ID : thm
  deriving Inhabited

@[nospecialize]
def setupAlgebraicClosureExistsId [HolBase] (D : FieldTheoryDeps) (BFieldExtension : FieldExtension) (BFiniteExtension : FiniteExtension) (BAlgebraicExtension : AlgebraicExtension) (BAlgebraicOverBasics : AlgebraicOverBasics) (BAlgebraicExtensionProps : AlgebraicExtensionProps) (BAlgebraicExtMisc : AlgebraicExtMisc) (BAcfBasic : AcfBasic) :
    ExceptT String IO AlgebraicClosureExistsId := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_TAC, TAUT, .. } := D
  let { CARD_DIFF_ABSORB, CARD_EQ_IMP_LE, CARD_EQ_SYM, CARD_LET_TRANS, CARD_LE_MUL,
        CARD_LE_REFL, CARD_LE_TRANS, CARD_LE_UNIV, CARD_LT_IMP_LE,
        CARD_MUL_LT_INFINITE, CARD_MUL_RID, CONJ_ASSOC, CROSS, EXISTS_IN_GSPEC,
        EXISTS_IN_UNIONS, .. } := D.core1
  let { FIELD_IMP_NONTRIVIAL_RING, FINITE_CROSS_EQ, FORALL_IN_GSPEC, FORALL_IN_IMAGE,
        FORALL_IN_UNIONS, IMAGE_I, .. } := D.core2
  let { IMP_CONJ, IMP_CONJ_ALT, INFINITE, INFINITE_CARD_LE, INJECTIVE_ON_ALT,
        INJECTIVE_ON_LEFT_INVERSE, IN_DIFF, IN_ELIM_THM, IN_FLD, IN_IMAGE,
        ISOMORPHIC_TRANSPORT_OF_RING, I_O_ID, I_THM, LEFT_IMP_EXISTS_THM, .. } := D.core3
  let { MEMBER_NOT_EMPTY, MONO_EXISTS, NOT_EXISTS_THM, NOT_IMP, NOT_IN_EMPTY,
        POLY_DEG_0, .. } := D.core4
  let { POLY_EXTEND_EVALUATE, POLY_EXTEND_HOMOMORPHIC_IMAGE, POLY_RING, QOSET_FLD,
        QOSET_RESTRICT, RIGHT_EXISTS_AND_THM, RIGHT_FORALL_IMP_THM,
        RING_CARRIER_NONEMPTY, .. } := D.core5
  let { RING_DIRECT_LIMIT, RING_ISOMORPHISM, RING_MONOMORPHISM_I,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, .. } := D.core6
  let { SUBSET, TRIVIAL_RING_10, TRIVIAL_RING_MONOMORPHIC_IMAGE_EQ, UNIONS_GSPEC,
        UNIV_NOT_EMPTY, ZL_STRONG, chain, field, le_c, mul_c, num_INFINITE, .. } := D.core8
  let { o_THM, poly_eval, qoset, ring_homomorphism, ring_monomorphism, .. } := D.core9
  let { FIELD_EXTENSION_IMP_SUBSET, FIELD_EXTENSION_REFL, FIELD_EXTENSION_TRANS,
        KRONECKER_SIMPLE_FIELD_EXTENSION, field_extension, .. } := BFieldExtension
  let { finite_extension, .. } := BFiniteExtension
  let { algebraic_extension, algebraic_over, .. } := BAlgebraicExtension
  let { ALGEBRAIC_EXTENSION, ALGEBRAIC_EXTENSION_EQ, FINITE_IMP_ALGEBRAIC_EXTENSION, .. } := BAlgebraicOverBasics
  let { FINITE_SIMPLE_ALGEBRAIC_EXTENSION, .. } := BAlgebraicExtensionProps
  let { ALGEBRAIC_EXTENSION_ISOMORPHISM, ALGEBRAIC_EXTENSION_REFL,
        ALGEBRAIC_EXTENSION_TRANS, CARD_LE_ALGEBRAIC_EXTENSION, .. } := BAlgebraicExtMisc
  let { algebraically_closed_field, .. } := BAcfBasic
  -- @@SCOPE END

  let ALGEBRAIC_CLOSURE_EXISTS_ID ← prove
   r"!k:A ring.
        ring_carrier k <_c (:A) /\ (:num) <_c (:A) /\ field k
        ==> ?l. algebraic_extension (k,l) I /\ algebraically_closed_field l"
   (← do
    let a3 ← TAUT (← q r"(~p ==> F) ==> p")
    let a2 ← TAUT (← q r"(p ==> q) /\ p ==> p /\ q")
    let a1 ← TAUT
      (← q r"(p /\ (p ==> (q ==> r) ==> s)) ==> (p /\ q ==> r) ==> s")
    pure (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC
     (← q r"\(l:A ring) (l':A ring). algebraic_extension(k,l) I /\
                  algebraic_extension(k,l') I /\
                  field_extension(l,l') I") ZL_STRONG) THEN
    REWRITE_TAC [] THEN MATCH_MP_TAC a1 THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC QOSET_RESTRICT THEN REWRITE_TAC [qoset, IN_FLD] THEN
      MESON_TAC [FIELD_EXTENSION_REFL, field_extension, I_O_ID,
                FIELD_EXTENSION_TRANS],
      SIMP_TAC [QOSET_FLD, IN_ELIM_THM] THEN DISCH_THEN (K ALL_TAC)] THEN
    REWRITE_TAC [CONJ_ASSOC] THEN REWRITE_TAC [chain, ← GSYM CONJ_ASSOC] THEN
    ANTS_TAC THENL [X_GEN_TAC (← q r"c:A ring->bool") THEN
      ASM_CASES_TAC (← q r"c:A ring->bool = {}") THENL
       [ASM_REWRITE_TAC [NOT_IN_EMPTY] THEN EXISTS_TAC (← q r"k:A ring") THEN
        ASM_REWRITE_TAC [ALGEBRAIC_EXTENSION_REFL, FIELD_EXTENSION_REFL],
        STRIP_TAC] THEN
      MP_TAC (← ISPEC (← q r"c:A ring->bool") RING_DIRECT_LIMIT) THEN ANTS_TAC THENL
       [RULE_ASSUM_TAC (REWRITE_RULE [field_extension]) THEN
        ASM_MESON_TAC [RING_MONOMORPHISM_I],
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"l:A ring") THEN STRIP_TAC] THEN
      REWRITE_TAC [FIELD_EXTENSION_REFL] THEN SUBGOAL_THEN (← q r"!f:A ring. f IN c
                   ==> field f /\ ring_monomorphism(k,f) I /\
                       algebraic_extension(k,f) I") ASSUME_TAC THENL
       [ASM_MESON_TAC [ALGEBRAIC_EXTENSION, field_extension],
        FIRST_X_ASSUM ((K ALL_TAC : thm → tactic) o SPECL [← q r"k:A ring", ← q r"k:A ring"])] THEN
      SUBGOAL_THEN (← q r"field(l:A ring)") ASSUME_TAC THENL
       [REWRITE_TAC [field, ← GSYM TRIVIAL_RING_10] THEN CONJ_TAC THENL
         [ASM_MESON_TAC [MEMBER_NOT_EMPTY,
              FIELD_IMP_NONTRIVIAL_RING, TRIVIAL_RING_MONOMORPHIC_IMAGE_EQ],
          ASM_REWRITE_TAC [IMP_CONJ, FORALL_IN_UNIONS, EXISTS_IN_UNIONS,
                          RIGHT_FORALL_IMP_THM, RIGHT_EXISTS_AND_THM,
                          FORALL_IN_GSPEC, EXISTS_IN_GSPEC]] THEN
        X_GEN_TAC (← q r"f:A ring") THEN DISCH_TAC THEN
        X_GEN_TAC (← q r"a:A") THEN REPEAT DISCH_TAC THEN
        REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"f:A ring"))) THEN
        ASM_REWRITE_TAC [ring_monomorphism, ring_homomorphism, I_THM] THEN
        STRIP_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
        REWRITE_TAC [field] THEN DISCH_THEN (MP_TAC o SPEC (← q r"a:A") o CONJUNCT2) THEN
        ASM_MESON_TAC [], ASM_SIMP_TAC []] THEN
      SUBGOAL_THEN (← q r"field_extension (k,l) (I:A->A)") ASSUME_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [← GSYM I_O_ID] THEN
        MATCH_MP_TAC FIELD_EXTENSION_TRANS THEN
          ASM_REWRITE_TAC [field_extension] THEN
        FIRST_X_ASSUM (MP_TAC o
          GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
        DISCH_THEN (X_CHOOSE_TAC (← q r"f0:A ring")) THEN
        EXISTS_TAC (← q r"f0:A ring") THEN ASM_MESON_TAC [],
          ALL_TAC] THEN
      MATCH_MP_TAC a2 THEN CONJ_TAC THENL
       [ASM_MESON_TAC [ALGEBRAIC_EXTENSION, field_extension],
        ASM_REWRITE_TAC [ALGEBRAIC_EXTENSION]] THEN
      REWRITE_TAC [UNIONS_GSPEC, FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"z:A") THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:A ring") STRIP_ASSUME_TAC) THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"f:A ring"))) THEN
      ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [ALGEBRAIC_EXTENSION]) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC (← q r"z:A"))) THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC (← q r"p:(1->num)->A") THEN
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o AP_TERM (← q r"I:A->A")) THEN
      ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL
       [← q r"k:A ring", ← q r"f:A ring", ← q r"l:A ring", ← q r"I:A->A", ← q r"(:1)",
        ← q r"(\v. z):1->A", ← q r"I:A->A", ← q r"p:(1->num)->A"]
          POLY_EXTEND_HOMOMORPHIC_IMAGE) THEN
      ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
      ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [I_O_ID] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [I_THM] THEN
      RULE_ASSUM_TAC (REWRITE_RULE
       [ring_monomorphism, ring_homomorphism, I_THM]) THEN ASM_MESON_TAC [],
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"l:A ring") THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [algebraically_closed_field] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC [ALGEBRAIC_EXTENSION, field_extension], ALL_TAC]] THEN
    SUBGOAL_THEN (← q r"ring_carrier(l:A ring) <_c (:A)") ASSUME_TAC THENL
      [MP_TAC (← ISPECL
       [← q r"I:A->A", ← q r"k:A ring", ← q r"l:A ring",
         ← q r"(ring_carrier k:A->bool) CROSS (:num)"]
       CARD_LE_ALGEBRAIC_EXTENSION) THEN
      ASM_REWRITE_TAC [INFINITE, FINITE_CROSS_EQ, UNIV_NOT_EMPTY] THEN
      ANTS_TAC THENL [REWRITE_TAC [← REWRITE_RULE [INFINITE] num_INFINITE,
                    RING_CARRIER_NONEMPTY] THEN
        TRANS_TAC CARD_LE_TRANS (← q r"(ring_carrier k:A->bool) *_c {0}") THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CARD_EQ_IMP_LE THEN MESON_TAC [CARD_EQ_SYM, CARD_MUL_RID],
          REWRITE_TAC [CROSS, ← GSYM mul_c] THEN MATCH_MP_TAC CARD_LE_MUL THEN
          REWRITE_TAC [CARD_LE_UNIV, CARD_LE_REFL]],
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] CARD_LET_TRANS) THEN
        REWRITE_TAC [CROSS, ← GSYM mul_c] THEN
        MATCH_MP_TAC CARD_MUL_LT_INFINITE THEN ASM_REWRITE_TAC [] THEN
        ASM_SIMP_TAC [INFINITE_CARD_LE, CARD_LT_IMP_LE]], ALL_TAC] THEN
    X_GEN_TAC (← q r"p:(1->num)->A") THEN STRIP_TAC THEN
    MATCH_MP_TAC a3 THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"l:A ring", ← q r"p:(1->num)->A"]
     KRONECKER_SIMPLE_FIELD_EXTENSION) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [field_extension], ALL_TAC] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
     [← q r"m:(((1->num)->A)->bool)ring", ← q r"h:A->((1->num)->A)->bool",
      ← q r"z:((1->num)->A)->bool"] THEN STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    MP_TAC (← ISPECL
      [← q r"h:A->((1->num)->A)->bool", ← q r"l:A ring", ← q r"m:(((1->num)->A)->bool)ring",
       ← q r"z:((1->num)->A)->bool"] FINITE_SIMPLE_ALGEBRAIC_EXTENSION) THEN
    ASM_REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC [algebraic_over] THEN EXISTS_TAC (← q r"p:(1->num)->A") THEN
      ASM_SIMP_TAC [POLY_EXTEND_EVALUATE, ← GSYM poly_eval] THEN
      ASM_MESON_TAC [POLY_DEG_0, POLY_RING], DISCH_TAC] THEN SUBGOAL_THEN
     (← q r"?h':(((1->num)->A)->bool)->A.
          (!x y. x IN ring_carrier m /\ y IN ring_carrier m /\ h' x = h' y
                 ==> x = y) /\
          (!x. x IN ring_carrier l ==> h'(h x) = x)") STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN
       (← q r"ring_carrier(m:(((1->num)->A)->bool)ring) <=_c (:A) DIFF ring_carrier l")
      MP_TAC THENL
       [wPart (fun c => do rand c) (fun c => do lhand (← rand c)) CARD_DIFF_ABSORB THEN
        ASM_SIMP_TAC [INFINITE_CARD_LE, CARD_LT_IMP_LE] THEN
        GEN_REWRITE_TAC LAND_CONV [CARD_EQ_SYM] THEN
        DISCH_THEN (MP_TAC o MATCH_MP CARD_EQ_IMP_LE) THEN
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] CARD_LE_TRANS) THEN MP_TAC (← ISPECL
         [← q r"(h:A->((1->num)->A)->bool) o (I:A->A)",
          ← q r"k:A ring", ← q r"m:(((1->num)->A)->bool)ring", ← q r"(:A)"]
         CARD_LE_ALGEBRAIC_EXTENSION) THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_SIMP_TAC [INFINITE_CARD_LE, CARD_LT_IMP_LE] THEN
        MATCH_MP_TAC ALGEBRAIC_EXTENSION_TRANS THEN
        ASM_MESON_TAC [FINITE_IMP_ALGEBRAIC_EXTENSION],
        REWRITE_TAC [le_c, LEFT_IMP_EXISTS_THM]] THEN
      X_GEN_TAC (← q r"h'':(((1->num)->A)->bool)->A") THEN
      REWRITE_TAC [IN_DIFF, INJECTIVE_ON_ALT] THEN STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o CONJUNCT2 o
        GEN_REWRITE_RULE I [ring_monomorphism]) THEN
      REWRITE_TAC [INJECTIVE_ON_LEFT_INVERSE] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"h':(((1->num)->A)->bool)->A")) THEN EXISTS_TAC
       (← q r"\x. if x IN IMAGE (h:A->((1->num)->A)->bool) (ring_carrier l)
            then (h':(((1->num)->A)->bool)->A) x else h'' x") THEN
      SIMP_TAC [] THEN REPEAT STRIP_TAC THEN TRY EQ_TAC THEN SIMP_TAC [] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [ring_homomorphism]) THEN ASM SET_TAC [],
      FIRST_X_ASSUM (MP_TAC o MATCH_MP ISOMORPHIC_TRANSPORT_OF_RING)] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"n:A ring")) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"n:A ring")) THEN
    ASM_REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL
     [SUBGOAL_THEN (← q r"algebraic_extension(l,n) (I:A->A)") MP_TAC THENL
       [MATCH_MP_TAC ALGEBRAIC_EXTENSION_EQ THEN EXISTS_TAC
         (← q r"(h':(((1->num)->A)->bool)->A) o (h:A->((1->num)->A)->bool)") THEN
        ASM_SIMP_TAC [o_THM, I_THM] THEN
        MATCH_MP_TAC ALGEBRAIC_EXTENSION_TRANS THEN
        EXISTS_TAC (← q r"m:(((1->num)->A)->bool)ring") THEN
          ASM_SIMP_TAC [FINITE_IMP_ALGEBRAIC_EXTENSION,
                     ALGEBRAIC_EXTENSION_ISOMORPHISM],
        ASM_MESON_TAC [I_O_ID, algebraic_extension, ALGEBRAIC_EXTENSION_TRANS]],
          ALL_TAC] THEN
    DISCH_THEN (MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET) THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, I_THM] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"(h':(((1->num)->A)->bool)->A) z")) THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [IN_IMAGE]) THEN
    REWRITE_TAC [NOT_EXISTS_THM] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"(h':(((1->num)->A)->bool)->A) z")) THEN
    RULE_ASSUM_TAC (REWRITE_RULE
       [field_extension, finite_extension, RING_ISOMORPHISM,
        ring_monomorphism, IMAGE_I, ring_homomorphism]) THEN ASM SET_TAC []))

  -- @@RETURN BEGIN
  return { ALGEBRAIC_CLOSURE_EXISTS_ID }
  -- @@RETURN END

structure AlgebraicClosure where
  -- @@FIELDS
  ALGEBRAIC_CLOSURE_EXISTS : thm
  ALGEBRAIC_CLOSURE_UNIQUE_EXPLICIT : thm
  ALGEBRAIC_CLOSURE_UNIQUE : thm
  deriving Inhabited

@[nospecialize]
def setupAlgebraicClosure [HolBase] (D : FieldTheoryDeps) (BFieldExtension : FieldExtension) (BAlgebraicExtension : AlgebraicExtension) (BAlgebraicOverBasics : AlgebraicOverBasics) (BAlgebraicExtMisc : AlgebraicExtMisc) (BAlgebraicField : AlgebraicField) (BAcfBasic : AcfBasic) (BClosureExtendHom : ClosureExtendHom) (BAlgebraicClosureExistsId : AlgebraicClosureExistsId) :
    ExceptT String IO AlgebraicClosure := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_TAC, TAUT, .. } := D
  let { CANTOR_THM_UNIV, CARD_EQ_IMP_LE, CARD_EQ_SYM, CARD_LET_TRANS, CARD_LE_MUL,
        CARD_LE_REFL, CARD_LE_SUBSET, CARD_LE_TRANS, CARD_LT_IMP_LE, CARD_MUL_LID,
        CARD_MUL_RID, CARD_SING_LE, EQ_IMP, .. } := D.core1
  let { FIELD_IMP_NONTRIVIAL_RING, FIELD_RING_HOMOMORPHISM_MONOMORPHISM, FUN_EQ_THM, .. } := D.core2
  let { IN_ELIM_THM, IN_RING_POLYNOMIAL_CARRIER_COMPOSE, ISOMORPHIC_RING_CARD_EQ,
        ISOMORPHIC_RING_FIELDNESS, ISOMORPHIC_SUBCOPY_OF_RING, I_O_ID, .. } := D.core3
  let { MONO_EXISTS, MUL_C_UNIV, POLY_DEG_MONOMORPHIC_IMAGE,
        POLY_EVAL_HOMOMORPHIC_IMAGE, .. } := D.core4
  let { POLY_RING, .. } := D.core5
  let { RING_HOMOMORPHISM_0, RING_ISOMORPHISM, RING_ISOMORPHISMS_ISOMORPHISM,
        RING_ISOMORPHISM_IMP_HOMOMORPHISM, RING_ISOMORPHISM_IMP_MONOMORPHISM, .. } := D.core6
  let { RING_POLYNOMIAL, .. } := D.core7
  let { SUBSET_UNIV, UNIV_NOT_EMPTY, isomorphic_ring, .. } := D.core8
  let { o_THM, ring_isomorphism, ring_monomorphism, ring_polynomial, ring_powerseries, .. } := D.core9
  let { field_extension, .. } := BFieldExtension
  let { algebraic_extension, .. } := BAlgebraicExtension
  let { ALGEBRAIC_EXTENSION, ALGEBRAIC_OVER_EQ, .. } := BAlgebraicOverBasics
  let { ALGEBRAIC_EXTENSION_ISOMORPHISM, ALGEBRAIC_EXTENSION_TRANS,
        CARD_LE_ALGEBRAIC_EXTENSION, .. } := BAlgebraicExtMisc
  let { ALGEBRAIC_OVER_ALGEBRAIC_EXTENSION, .. } := BAlgebraicField
  let { ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD,
        ALGEBRAICALLY_CLOSED_FIELD_NO_PROPER_ALGEBRAIC_EXTENSION,
        algebraically_closed_field, .. } := BAcfBasic
  let { ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM, .. } := BClosureExtendHom
  let { ALGEBRAIC_CLOSURE_EXISTS_ID, .. } := BAlgebraicClosureExistsId
  -- @@SCOPE END

  let ALGEBRAIC_CLOSURE_EXISTS ← prove
   r"!k:A ring.
        INFINITE(:B) /\ ring_carrier k <=_c (:B) /\ field k
        ==> ?l (f:A->B). algebraic_extension (k,l) f /\
                         algebraically_closed_field l"
   (← do
    let a1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(:A) <_c (:A#num->bool) /\ (:num) <_c (:A#num->bool)")
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN
      TRANS_TAC CARD_LET_TRANS (← q r"(:A#num)") THEN
      REWRITE_TAC [CANTOR_THM_UNIV] THENL
       [TRANS_TAC CARD_LE_TRANS (← q r"(:A) *_c {one}"),
        TRANS_TAC CARD_LE_TRANS (← q r"{one} *_c (:num)")] THEN
       SIMP_TAC [← GSYM MUL_C_UNIV, CARD_LE_MUL, CARD_SING_LE, UNIV_NOT_EMPTY,
                CARD_LE_REFL] THEN
       MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN
       REWRITE_TAC [CARD_MUL_LID, CARD_MUL_RID], ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"(:A#num->bool)"] ISOMORPHIC_SUBCOPY_OF_RING) THEN
    ANTS_TAC THENL [TRANS_TAC CARD_LE_TRANS (← q r"(:A)") THEN
      ASM_SIMP_TAC [CARD_LE_SUBSET, CARD_LT_IMP_LE, SUBSET_UNIV],
      REWRITE_TAC [SUBSET_UNIV] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"k':(A#num->bool)ring") STRIP_ASSUME_TAC)] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP ISOMORPHIC_RING_FIELDNESS) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MP_TAC (← ISPEC (← q r"k':(A#num->bool)ring") ALGEBRAIC_CLOSURE_EXISTS_ID) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [TRANS_TAC CARD_LET_TRANS (← q r"(:A)") THEN ASM_REWRITE_TAC [] THEN
      TRANS_TAC CARD_LE_TRANS (← q r"ring_carrier(k:A ring)") THEN
      ASM_SIMP_TAC [CARD_LE_SUBSET, SUBSET_UNIV] THEN
      MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN
      MATCH_MP_TAC ISOMORPHIC_RING_CARD_EQ THEN ASM_REWRITE_TAC [],
      DISCH_THEN (X_CHOOSE_THEN (← q r"l':(A#num->bool)ring")
        (STRIP_ASSUME_TAC o REWRITE_RULE [algebraically_closed_field]))] THEN
    MP_TAC (← ISPECL [← q r"l':(A#num->bool)ring", ← q r"(:B)"]
      ISOMORPHIC_SUBCOPY_OF_RING) THEN
    REWRITE_TAC [SUBSET_UNIV] THEN ANTS_TAC THENL
     [MP_TAC (← ISPECL [← q r"I:(A#num->bool)->(A#num->bool)",
                     ← q r"k':(A#num->bool)ring", ← q r"l':(A#num->bool)ring", ← q r"(:B)"]
          CARD_LE_ALGEBRAIC_EXTENSION) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
      TRANS_TAC CARD_LE_TRANS (← q r"ring_carrier(k:A ring)") THEN
        ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN
      MATCH_MP_TAC ISOMORPHIC_RING_CARD_EQ THEN ASM_REWRITE_TAC [],
      MATCH_MP_TAC MONO_EXISTS] THEN X_GEN_TAC (← q r"l:B ring") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"field(l:B ring)") ASSUME_TAC THENL
     [ASM_MESON_TAC [ALGEBRAIC_EXTENSION, field_extension,
                    ISOMORPHIC_RING_FIELDNESS], ALL_TAC] THEN
    FIRST_ASSUM (X_CHOOSE_TAC (← q r"f:A->A#num->bool") o
      GEN_REWRITE_RULE I [isomorphic_ring]) THEN
    FIRST_ASSUM (X_CHOOSE_TAC (← q r"g:(A#num->bool)->B") o
      GEN_REWRITE_RULE I [isomorphic_ring]) THEN
    EXISTS_TAC (← q r"(g:(A#num->bool)->B) o (f:A->A#num->bool)") THEN CONJ_TAC THENL
     [MATCH_MP_TAC ALGEBRAIC_EXTENSION_TRANS THEN
       EXISTS_TAC (← q r"l':(A#num->bool)ring") THEN
      ASM_SIMP_TAC [ALGEBRAIC_EXTENSION_ISOMORPHISM] THEN
      GEN_REWRITE_TAC RAND_CONV [← SYM (← CONJUNCT1 (← SPEC_ALL I_O_ID))] THEN
      MATCH_MP_TAC ALGEBRAIC_EXTENSION_TRANS THEN
        EXISTS_TAC (← q r"k':(A#num->bool)ring") THEN
      ASM_SIMP_TAC [ALGEBRAIC_EXTENSION_ISOMORPHISM],
      ASM_REWRITE_TAC [algebraically_closed_field] THEN
      FIRST_ASSUM (X_CHOOSE_THEN (← q r"g':B->A#num->bool") MP_TAC o
          GEN_REWRITE_RULE I [ring_isomorphism]) THEN
      REWRITE_TAC [RING_ISOMORPHISMS_ISOMORPHISM] THEN STRIP_TAC THEN
      X_GEN_TAC (← q r"p:(1->num)->B") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(g':B->A#num->bool) o (p:(1->num)->B)")) THEN
      MP_TAC (← ISPECL
       [← q r"l:B ring", ← q r"l':(A#num->bool)ring", ← q r"g':B->A#num->bool", ← q r"(:1)"]
       IN_RING_POLYNOMIAL_CARRIER_COMPOSE) THEN
      ASM_SIMP_TAC [RING_ISOMORPHISM_IMP_HOMOMORPHISM] THEN
      DISCH_THEN (K ALL_TAC) THEN MP_TAC (← ISPECL
        [← q r"l:B ring", ← q r"l':(A#num->bool)ring", ← q r"g':B->A#num->bool",
          ← q r"p:(1->num)->B"]
        POLY_DEG_MONOMORPHIC_IMAGE) THEN
      ASM_SIMP_TAC [RING_ISOMORPHISM_IMP_MONOMORPHISM, RING_POLYNOMIAL] THEN
      DISCH_THEN (K ALL_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"w:A#num->bool") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"(g:(A#num->bool)->B) w") THEN
      MATCH_MP_TAC a1 THEN CONJ_TAC THENL
       [RULE_ASSUM_TAC (REWRITE_RULE [RING_ISOMORPHISM]) THEN ASM SET_TAC [],
        DISCH_TAC] THEN FIRST_X_ASSUM (MP_TAC o AP_TERM (← q r"g:(A#num->bool)->B")) THEN
      MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
       [ALL_TAC, ASM_MESON_TAC [RING_ISOMORPHISM, RING_HOMOMORPHISM_0]] THEN
      MP_TAC (← ISPECL [← q r"l':(A#num->bool)ring", ← q r"l:B ring", ← q r"w:A#num->bool",
       ← q r"g:(A#num->bool)->B", ← q r"(g':B->A#num->bool) o (p:(1->num)->B)"]
          POLY_EVAL_HOMOMORPHIC_IMAGE) THEN MP_TAC (← ISPECL
       [← q r"l:B ring", ← q r"l':(A#num->bool)ring", ← q r"g':B->A#num->bool", ← q r"(:1)"]
       IN_RING_POLYNOMIAL_CARRIER_COMPOSE) THEN
      ASM_SIMP_TAC [RING_ISOMORPHISM_IMP_HOMOMORPHISM] THEN
      DISCH_THEN (K ALL_TAC) THEN DISCH_THEN SUBST1_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM, o_THM] THEN
      RULE_ASSUM_TAC (REWRITE_RULE
       [POLY_RING, IN_ELIM_THM, ring_polynomial, ring_powerseries]) THEN
      ASM_SIMP_TAC []]))

  let ALGEBRAIC_CLOSURE_UNIQUE_EXPLICIT ← prove
   r"!(k:A ring) (l:B ring) (l':C ring) (f:A->B) (g:A->C).
        algebraic_extension(k,l) f /\ algebraically_closed_field l /\
        algebraic_extension(k,l') g /\ algebraically_closed_field l'
        ==> ?h. ring_isomorphism(l,l') h /\
                (!x. x IN ring_carrier k ==> h(f x) = g x)"
   (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"field (l:B ring) /\ field (l':C ring) /\
       ring_homomorphism(k:A ring,l':C ring) g /\
       field_extension(k:A ring,l:B ring) f") STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN ASM_MESON_TAC [ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD,
       algebraic_extension, field_extension, ring_monomorphism], ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"l:B ring", ← q r"l':C ring", ← q r"f:A->B", ← q r"g:A->C"]
      ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"h:B->C") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"h:B->C") THEN CONJ_TAC THENL [ALL_TAC, ASM_REWRITE_TAC []] THEN
    SUBGOAL_THEN (← q r"ring_monomorphism(l:B ring,l':C ring) (h:B->C)") ASSUME_TAC
      THENL
     [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
      ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [FIELD_IMP_NONTRIVIAL_RING],
        ALL_TAC] THEN
    SUBGOAL_THEN (← q r"field_extension(l:B ring,l':C ring) (h:B->C)") ASSUME_TAC THENL
     [ASM_REWRITE_TAC [field_extension], ALL_TAC] THEN
    MATCH_MP_TAC ALGEBRAICALLY_CLOSED_FIELD_NO_PROPER_ALGEBRAIC_EXTENSION THEN
    ASM_REWRITE_TAC [algebraic_extension] THEN X_GEN_TAC (← q r"x:C") THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A->B", ← q r"h:B->C", ← q r"k:A ring", ← q r"l:B ring", ← q r"l':C ring",
      ← q r"x:C"] ALGEBRAIC_OVER_ALGEBRAIC_EXTENSION) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC (← ISPECL [← q r"k:A ring", ← q r"l':C ring", ← q r"x:C",
      ← q r"g:A->C", ← q r"((h:B->C) o (f:A->B)):A->C"] ALGEBRAIC_OVER_EQ) THEN
    ASM_REWRITE_TAC [o_THM] THEN ASM_MESON_TAC [algebraic_extension])

  let ALGEBRAIC_CLOSURE_UNIQUE ← prove
   r"!(k:A ring) (l:B ring) (l':C ring) (f:A->B) (g:A->C).
        algebraic_extension(k,l) f /\ algebraically_closed_field l /\
        algebraic_extension(k,l') g /\ algebraically_closed_field l'
        ==> l isomorphic_ring l'"
   (REWRITE_TAC [isomorphic_ring] THEN
    MESON_TAC [ALGEBRAIC_CLOSURE_UNIQUE_EXPLICIT])

  -- @@RETURN BEGIN
  return { ALGEBRAIC_CLOSURE_EXISTS, ALGEBRAIC_CLOSURE_UNIQUE_EXPLICIT,
           ALGEBRAIC_CLOSURE_UNIQUE }
  -- @@RETURN END

end HolLibrary.FieldTheory
